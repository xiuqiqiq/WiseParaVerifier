import sys
# sys.path.append('./')
import murphi
import wiseParaVerifier.concretedF as concretedF
from z3 import *
import itertools
import subprocess
import re
from collections import defaultdict
import shutil
from murphiparser import *
import copy
from collections import Counter

#from BMC.SMT import BMC






from itertools import product


import time

import client


import threading
from concurrent.futures import ThreadPoolExecutor
import multiprocessing

callSmt = 0
callLS = 0
callNuSMV = 0
callBMC = 0
invPattern = list()
invPattern_dict = defaultdict(list)
enum_value_map = dict()
# enum_value_map = BMC.enum_value_map

recursive_call_count = 0

checkPattern = list()
checklistPattern = defaultdict(list)
checkresultPattern = dict()

t_smt = 0
t_smv = 0
t_constructlist = 0

smt_solutions = 0
listnum_of_callSMV = 0
all_auxinv = 0
symm_auxinv = 0

test_time = 0
EnumType_vars = {}

all_vars = dict()
all_ins_vars = list()
all_pmurphi = dict()
const_pmurphi_map = dict()



inv_cnt = 1


expartitionsRecord = dict()
flpartitionsRecord = dict()

paraAlpdict = dict()
allparainvs = list()
exfolparainvs = list()


EXISTENTIAL_QUANTIFICATION = False
USE_HEURISTIC_GENERALIZE = True



def setKey(expr, replacement, isbool=False, isdigit=False, isenum=False):
    global EnumType_vars
    if isbool:
        if replacement == "":
            return [Bool(str(expr) + replacement), expr]
        else:
            return [Bool(str(expr) + replacement)]
    elif isdigit:
        if replacement == "":
            return [Int(str(expr) + replacement), expr]
        else:
            return [Int(str(expr) + replacement)]
    elif isenum:
        if replacement == "":
            return [Const(str(expr) + replacement, enum_value_map[EnumType_vars[str(expr) + replacement]][
                EnumType_vars[str(expr) + replacement]]), expr]
        else:
            return [Const(str(expr) + replacement, enum_value_map[EnumType_vars[str(expr) + replacement]][
                EnumType_vars[str(expr) + replacement]])]
    else:
        if replacement == "":
            return [z3.String(str(expr) + replacement), expr]
        else:
            return [z3.String(str(expr) + replacement)]


class ConstructF():
    def __init__(self, protocol_name, name, instance, inv_path, current_inv, ori_inv, boolVars, enum_typ_map, typ_map,
                 scalarsetVars):
        self.protocol_name = protocol_name
        self.name = name
        self.inv_path = inv_path
        self.current_inv = current_inv
        self.ori_inv = ori_inv
        self.boolVars = boolVars

        self.guard = instance["guard"]
        

        self.assign = instance["assign"]
        # assert all(isinstance(f, murphi.AssignCmd) for f in self.assign)

        self.assumption = instance["assumption"]

        self.negInv = instance["!inv"]

        self.inv = instance["inv"]

        self.variables = dict()
        self.boundStates = list()

        self.solver = Solver()

        self.aux_inv = None

        self.enum_typ_map = enum_typ_map
        self.enum_vars = dict()

        self.typ_map = typ_map

        self.paraVars = list()
        self.var_list = []

        self.murphiInvLines = ""

        self.scalarsetVars = scalarsetVars

        self.dataVars = []

        self.cti = {}

        self.invnums = 1

        self.before_check = None

        self.join_before_check = None

        self.join_before_check_map = dict()

        self.join_aux_inv = None

        self.negInveqs = list()	

    def isdigit(self, fomula):
        assert isinstance(fomula, murphi.OpExpr)
        if isinstance(fomula.expr1, murphi.OpExpr):
            if self.isdigit(fomula.expr1) == False:
                return False
        if isinstance(fomula.expr2, murphi.OpExpr):
            if self.isdigit(fomula.expr2) == False:
                return False
        if isinstance(fomula.expr1, murphi.VarExpr) and (fomula.expr1.name).isdigit() and isinstance(fomula.expr2,
                                                                                                     murphi.VarExpr) and (
                fomula.expr2.name).isdigit():
            return True
        else:
            return False

    def smtOP(self, expr1, expr2, op):
        global EnumType_vars
        if op == '=':
            if str(expr1) in EnumType_vars and str(expr2) in enum_value_map[EnumType_vars[str(expr1)]]:
                return expr1 == enum_value_map[EnumType_vars[str(expr1)]][expr2]

            return expr1 == expr2
        if op == '!=':
            if str(expr1) in EnumType_vars and str(expr2) in enum_value_map[EnumType_vars[str(expr1)]]:
                return expr1 != enum_value_map[EnumType_vars[str(expr1)]][expr2]
            return expr1 != expr2
        if op == '&':
            return And(expr1, expr2)
        if op == '|':
            return Or(expr1, expr2)
        if op == '->':
            return Implies(expr1, expr2)
        if op == '<=':
            return expr1<=expr2
        if op == '>=':
            return expr1>=expr2
        if op == '>':
            return expr1>expr2
        if op == '<':
            return expr1<expr2

    def getVal(self, expr):
        if isinstance(expr, murphi.EnumValExpr):
            return str(expr.enum_val)
        elif isinstance(expr, murphi.BooleanExpr):
            return True if expr.val else False
        elif str(expr).isdigit():
            return int(str(expr))
        else:
            return str(expr)

    def digitfomulaResult(self, digitf):
        
        assert isinstance(digitf, murphi.OpExpr)
        op1 = digitf.expr1.name
        op2 = digitf.expr2.name

        digitseq = op1 == op2

        if digitf.op in ('='):
            return digitseq
        elif digitf.op in ('!='):
            return not digitseq

    def getVars(self, fomula, vardict, statements, replacement=""):
        global EnumType_vars
        # for guard and inv
        if isinstance(fomula, murphi.OpExpr):
            if self.isdigit(fomula):
                statements.append(self.digitfomulaResult(fomula))
            else:
                if isinstance(fomula.expr1, murphi.OpExpr) or isinstance(fomula.expr1, murphi.NegExpr) or isinstance(
                        fomula.expr2, murphi.OpExpr) or isinstance(fomula.expr2, murphi.NegExpr):
                    newlist1 = []
                    newlist2 = []
                    if isinstance(fomula.expr1, murphi.OpExpr) or isinstance(fomula.expr1, murphi.NegExpr):
                        _, newlist1 = self.getVars(fomula.expr1, vardict, newlist1, replacement)
                    if isinstance(fomula.expr2, murphi.OpExpr) or isinstance(fomula.expr2, murphi.NegExpr):
                        _, newlist2 = self.getVars(fomula.expr2, vardict, newlist2, replacement)
                    if len(newlist1) and len(newlist2):

                        statements.append(self.smtOP(newlist1[0], newlist2[0], fomula.op))
                    elif len(newlist2):
                        statements.append(newlist2[0])
                    elif len(newlist1):
                        statements.append(newlist1[0])
                else:
                    if isinstance(fomula.expr2, murphi.EnumValExpr) or isinstance(fomula.expr2, murphi.BooleanExpr) or (
                            isinstance(fomula.expr2, murphi.VarExpr) and fomula.expr2.name.isdigit()):
                        if str(fomula.expr1) + replacement not in vardict.keys():
                            vardict[str(fomula.expr1) + replacement] = all_vars[str(fomula.expr1) + replacement]
                            if str(fomula.expr1) in self.scalarsetVars and str(
                                    fomula.expr1) + replacement not in self.dataVars:
                                self.dataVars.append(str(fomula.expr1) + replacement)
                        val = self.getVal(fomula.expr2)
                        statements.append(self.smtOP(all_vars[str(fomula.expr1) + replacement][0], val, fomula.op))
                    elif isinstance(fomula.expr1, murphi.EnumValExpr) or isinstance(fomula.expr1, murphi.BooleanExpr) or (
                            isinstance(fomula.expr1, murphi.VarExpr) and fomula.expr1.name.isdigit()):
                        if str(fomula.expr2) + replacement not in vardict.keys():
                            vardict[str(fomula.expr2) + replacement] = all_vars[str(fomula.expr2) + replacement]
                            if str(fomula.expr2) in self.scalarsetVars and str(
                                    fomula.expr2) + replacement not in self.dataVars:
                                self.dataVars.append(str(fomula.expr2) + replacement)
                        val = self.getVal(fomula.expr1)
                        statements.append(self.smtOP(val, all_vars[str(fomula.expr2) + replacement][0], fomula.op))
                    else:
                        if str(fomula.expr1) + replacement not in vardict.keys():
                            # print("str(fomula.expr1) + replacement:",str(fomula.expr1) + replacement)
                            vardict[str(fomula.expr1) + replacement] = all_vars[str(fomula.expr1) + replacement]
                            if str(fomula.expr1) in self.scalarsetVars and str(
                                    fomula.expr1) + replacement not in self.dataVars:
                                self.dataVars.append(str(fomula.expr1) + replacement)
                        if str(fomula.expr2) + replacement not in vardict.keys():
                            vardict[str(fomula.expr2) + replacement] = all_vars[str(fomula.expr2) + replacement]
                            if str(fomula.expr2) in self.scalarsetVars and str(
                                    fomula.expr2) + replacement not in self.dataVars:
                                self.dataVars.append(str(fomula.expr2) + replacement)
                        statements.append(self.smtOP(all_vars[str(fomula.expr1) + replacement][0],
                                                     all_vars[str(fomula.expr2) + replacement][0], fomula.op))

        # for assignment
        if isinstance(fomula, murphi.AssignCmd):
            if isinstance(fomula.expr, murphi.EnumValExpr) or isinstance(fomula.expr, murphi.BooleanExpr) or (
                    isinstance(fomula.expr, murphi.VarExpr) and fomula.expr.name.isdigit()):

                if str(fomula.var) + replacement not in vardict.keys():
                    vardict[str(fomula.var) + replacement] = all_vars[str(fomula.var) + replacement]
                    if str(fomula.var) in self.scalarsetVars and str(fomula.var) + replacement not in self.dataVars:
                        self.dataVars.append(str(fomula.var) + replacement)

                val = self.getVal(fomula.expr)
                statements.append(self.smtOP(all_vars[str(fomula.var) + replacement][0], val, '='))
            else:
                expr_replacement = ""
                if str(fomula.var) + replacement not in vardict.keys():
                    vardict[str(fomula.var) + replacement] = all_vars[str(fomula.var) + replacement]
                    if str(fomula.var) in self.scalarsetVars and str(fomula.var) + replacement not in self.dataVars:
                        self.dataVars.append(str(fomula.var) + replacement)
                if str(fomula.expr) + expr_replacement not in vardict.keys():
                    vardict[str(fomula.expr) + expr_replacement] = all_vars[str(fomula.expr) + expr_replacement]
                    if str(fomula.expr) in self.scalarsetVars and str(
                            fomula.expr) + expr_replacement not in self.dataVars:
                        self.dataVars.append(str(fomula.expr) + expr_replacement)
                statements.append(self.smtOP(all_vars[str(fomula.var) + replacement][0],
                                             all_vars[str(fomula.expr) + expr_replacement][0], '='))

        # for negInv
        if isinstance(fomula, murphi.NegExpr):
            # assert isinstance(fomula.expr, murphi.OpExpr)
            if isinstance(fomula.expr, murphi.NegExpr):
                self.getVars(fomula.expr.expr, vardict, statements, replacement)
            else:
                if fomula.expr.op == '->':
                    # to cnf
                    cnf = murphi.OpExpr('&', fomula.expr.expr1, murphi.NegExpr(fomula.expr.expr2))
                    self.getVars(cnf, vardict, statements, replacement)
                if fomula.expr.op == '=':
                    neq = murphi.OpExpr('!=', fomula.expr.expr1, fomula.expr.expr2)

                    self.getVars(neq, vardict, statements, replacement)
                if fomula.expr.op == '!=':
                    self.getVars(murphi.OpExpr('=', fomula.expr.expr1, fomula.expr.expr2), vardict, statements,
                                 replacement)
                if fomula.expr.op == '&':
                    impl = murphi.OpExpr('->', fomula.expr.expr1, murphi.NegExpr(fomula.expr.expr2))
                    self.getVars(impl, vardict, statements, replacement)
                if fomula.expr.op == '|':
                    cnf = murphi.OpExpr('&', murphi.NegExpr(fomula.expr.expr1), murphi.NegExpr(fomula.expr.expr2))

                    self.getVars(cnf, vardict, statements, replacement)
                if fomula.expr.op == '<=':
                    self.getVars(murphi.OpExpr('>', fomula.expr.expr1, fomula.expr.expr2), vardict, statements,
                                 replacement)
                if fomula.expr.op == '>=':
                    self.getVars(murphi.OpExpr('<', fomula.expr.expr1, fomula.expr.expr2), vardict, statements,
                                 replacement)
                if fomula.expr.op == '<':
                    self.getVars(murphi.OpExpr('>=', fomula.expr.expr1, fomula.expr.expr2), vardict, statements,
                                 replacement)
                if fomula.expr.op == '>':
                    self.getVars(murphi.OpExpr('<=', fomula.expr.expr1, fomula.expr.expr2), vardict, statements,
                                 replacement)

        return vardict, statements

    def join_statements(self, statement):
        if len(statement) == 1:
            return statement[0]
        else:
            # return (str(statement[-1]) + "& (" + self.join_statements(statement[:-1]) + ")")
            return murphi.OpExpr('&', statement[-1], self.join_statements(statement[:-1]))
        
    def disjoin_statements(self, statement):
        if len(statement) == 1:
            return statement[0]
        else:
            # return (str(statement[-1]) + "& (" + self.join_statements(statement[:-1]) + ")")
            return murphi.OpExpr('|', statement[-1], self.join_statements(statement[:-1]))

    def disjoin_z3_statements(self, statement):
        if len(statement) == 1:
            return statement[0]
        else:
            # return (str(statement[-1]) + "& (" + self.join_statements(statement[:-1]) + ")")
            return Or(statement[-1], self.disjoin_z3_statements(statement[:-1]))


    def join_z3_statements(self, statement):
        if len(statement) == 1:
            return statement[0]
        else:
            # return (str(statement[-1]) + "& (" + self.join_statements(statement[:-1]) + ")")
            return And(statement[-1], self.join_z3_statements(statement[:-1]))

    def is_enum_value_in_list(self, enum_value, enum_list):
        for item in enum_list:
            if str(enum_value) == str(item):
                return True
        return False

    def smtFormula(self):
        test_s = time.time()

        # for guard's variables
        self.variables, self.boundStates = self.getVars(self.guard, self.variables, self.boundStates)


        for assign in self.assign:
            if isinstance(assign, murphi.AssignCmd):
                self.variables, self.boundStates = self.getVars(assign, self.variables, self.boundStates, "'")
            elif isinstance(assign, murphi.IfCmd):


                if_cond = []
                else_cond = []
                self.variables, if_cond = self.getVars(assign.if_branches[0][0], self.variables, if_cond)
                self.variables, else_cond = self.getVars(murphi.NegExpr(assign.if_branches[0][0]), self.variables,
                                                         else_cond)

                if_assign = []
                if_variables = []
                for if_as in assign.if_branches[0][1]:
                    self.variables, if_assign = self.getVars(if_as, self.variables, if_assign, "'")
                    assert isinstance(if_as, murphi.AssignCmd)
                    if_variables.append(if_as.var)

                else_assign = []
                else_variables = []
                if assign.else_branch:
                    for else_as in assign.else_branch:
                        self.variables, else_assign = self.getVars(else_as, self.variables, else_assign, "'")
                        assert isinstance(else_as, murphi.AssignCmd)
                        else_variables.append(else_as.var)

                

                # fix: how to handle when "else" not occure?
                # fix: assumptions when variables different from if_branch & else_branch
                if else_assign:
                    if_variables_bounds = []
                    else_variables_bounds = []
                    if_assumptions = [elem for elem in else_variables if elem not in if_variables]
                    else_assumptions = [elem for elem in if_variables if elem not in else_variables]

                    for if_assumption in if_assumptions:
                        if_variables_bounds.append(
                            self.smtOP(all_vars[str(if_assumption)][0], all_vars[str(if_assumption) + "'"][0], '='))

                    for else_assumption in else_assumptions:
                        else_variables_bounds.append(
                            self.smtOP(all_vars[str(else_assumption)][0], all_vars[str(else_assumption) + "'"][0], '='))

                    self.boundStates.append(Or(self.join_z3_statements(if_cond + if_assign + if_variables_bounds),
                                               self.join_z3_statements(else_cond + else_assign + else_variables_bounds)))
                else:
                    else_variables_bounds = []
                    for variables in if_variables:
                        else_variables_bounds.append(
                            self.smtOP(all_vars[str(variables)][0], all_vars[str(variables) + "'"][0], '='))

                    self.boundStates.append(Or(self.join_z3_statements(if_cond + if_assign),
                                               self.join_z3_statements(else_cond + else_variables_bounds)))


        for assumption in self.assumption:

            if str(assumption) not in self.variables.keys():
                self.variables[str(assumption)] = all_vars[str(assumption)]
                if str(assumption) in self.scalarsetVars and str(assumption) not in self.dataVars:
                    self.dataVars.append(str(assumption))

            if str(assumption) + "'" not in self.variables.keys():
                self.variables[str(assumption) + "'"] = all_vars[str(assumption) + "'"]
                if str(assumption) in self.scalarsetVars and str(assumption) + "'" not in self.dataVars:
                    self.dataVars.append(str(assumption) + "'")

            self.boundStates.append(
                self.smtOP(all_vars[str(assumption)][0], all_vars[str(assumption) + "'"][0], '='))

        self.variables, self.boundStates = self.getVars(self.negInv, self.variables, self.boundStates, "'")
        # all subOpExpr of neg_inv
        self.negInveqs = self.parse_all_eqs(self.negInv, [])



        # # current inv:
        # adding current invs:
        current_variables = list(self.variables.keys())
        # neg_neg_inv_f = False
        for ori_inv in self.ori_inv:
            ori_inv_vars = self.getOpVars(ori_inv,[])
            if set(ori_inv_vars).issubset(set(current_variables)):
                self.variables, self.boundStates = self.getVars(ori_inv, self.variables, self.boundStates)

        for dvar in self.dataVars:
            equalStates = []
            for data in const_pmurphi_map[dvar.rstrip("'")].keys():
                val = self.getVal(data)
                equalStates.append(self.smtOP(self.variables[str(dvar)][0], val, '='))
            if len(equalStates) == 1:
                self.boundStates.extend(equalStates)
            elif len(equalStates) > 1:
                self.boundStates.append(self.disjoin_z3_statements(equalStates))


        self.cti = {k: v for k, v in self.variables.items() if not k.endswith("'")}

        for state in self.boundStates:
            self.solver.add(state)

        aux_inv_list = []
        all_invs_list = []

        checkSat = self.solver.check() == sat

        global callSmt

        test_e = time.time()
        global test_time
        test_time += test_e - test_s

        while_time = 0
        while checkSat:
            
            s_smt = time.time()
            while_time = while_time + 1
          

            callSmt = callSmt + 1
            model = self.solver.model()
 
            global smt_solutions
            smt_solutions = smt_solutions + 1
            current_solutions = self.construct_aux_lists(model)

            

            if self.protocol_name == "flash" or self.protocol_name == "flashNodata": start_result = True
            else: start_result, _ = self.call_NuSMV(current_solutions, self.protocol_name)
            # else: start_result, _ = self.call_BMC(current_solutions, self.protocol_name)

            if start_result:

                if USE_HEURISTIC_GENERALIZE == True:
                    join_list = [elem for elem in self.negInveqs if elem  in current_solutions]
                    diff_list = [elem for elem in current_solutions if elem not in self.negInveqs]


                    join_current_inv = None
                    join_inv4smt = None

                    if len(join_list) > 0 :
                        if current_solutions:
                            join_current_inv, join_inv4smt = self.search_join_aux_invs(join_list, diff_list)
                        
                        if join_current_inv:
                            symm_invs = self.getallSymmetryInvs_partition(copy.deepcopy(join_current_inv))
                            all_invs_list.extend(symm_invs)

                            # cancel symmentric for total order:
                            # all_invs_list.append(join_current_inv)

                            current_variables = list(self.variables.keys())
                            for symm_inv in symm_invs:
                                symm_inv_vars = self.getOpVars(symm_inv,[])
                                if set(symm_inv_vars).issubset(set(current_variables)):
                                    self.variables, join_symm_inv_bound = self.getVars(symm_inv, self.variables, self.boundStates)
                                    self.solver.add(join_symm_inv_bound)



                            aux_inv_list.append(join_current_inv)

                            self.invnums = self.invnums + 1

                            # _, join_current_inv_bound = self.getVars(join_current_inv, self.variables, [])
                            # self.solver.add(join_current_inv_bound)



                if USE_HEURISTIC_GENERALIZE == False or (len(join_list) == 0 or (join_current_inv == None and join_inv4smt == None)):
                    current_inv = None
                    if current_solutions:
                        current_inv, inv4smt = self.search_aux_invs(current_solutions)
                        self.aux_inv = None


                    if current_inv:

                        # should fix with module total_order
                        symm_invs = self.getallSymmetryInvs_partition(copy.deepcopy(current_inv))
                        all_invs_list.extend(symm_invs)

                        # cancel symmentric for total order:
                        # all_invs_list.append(current_inv)


                        current_variables = list(self.variables.keys())
                        for symm_inv in symm_invs:
                            symm_inv_vars = self.getOpVars(symm_inv,[])
                            if set(symm_inv_vars).issubset(set(current_variables)):
                                self.variables, symm_inv_bound = self.getVars(symm_inv, self.variables, self.boundStates)
                                self.solver.add(symm_inv_bound)

                        aux_inv_list.append(current_inv)

                        self.invnums = self.invnums + 1

                        # _, current_inv_bound = self.getVars(current_inv, self.variables, [])
                        # self.solver.add(current_inv_bound)

                        


            
            blocking_clause = [d() != model[d] for d in model]
            self.solver.add(Or(blocking_clause))
            checkSat = self.solver.check() == sat
            e_smt = time.time()
            global t_smt
            t_smt += e_smt - s_smt

        if not checkSat:
            callSmt = callSmt + 1

        return aux_inv_list, self.name, all_invs_list

    def construct_aux_lists(self, model):
        s_constructlist = time.time()

        inv_list = []

        digitNum = 0
        digitVar = None
        for k, v in self.cti.items():
            value = ""
            if isinstance(model[v[0]], BoolRef):
                value = str(is_true(model[v[0]]))
            elif isinstance(model[v[0]], DatatypeRef) or isinstance(model[v[0]], IntNumRef):
                value = str(model[v[0]])
                if isinstance(model[v[0]], IntNumRef):
                    digitNum += 1
            elif model[v[0]] == None:
                pass
            else:
                value = model[v[0]].as_string()

            if value != "":
                pattern = r'\S*\[.*?\]\S*'

                if value == "False":
                    inv_list.append(murphi.OpExpr('=', v[1], murphi.BooleanExpr(False)))
                elif value == "True":
                    inv_list.append(murphi.OpExpr('=', v[1], murphi.BooleanExpr(True)))
                elif value in all_pmurphi.keys():
                    inv_list.append(murphi.OpExpr('=', v[1], all_pmurphi[value]))
                elif value.isdigit():
                    assert isinstance(murphi.specific_var[str(v[1])], murphi.ScalarSetType) or isinstance(murphi.specific_var[str(v[1])], murphi.RngType)
                    inv_list.append(
                        murphi.OpExpr('=', v[1], const_pmurphi_map[str(v[1]).rstrip("'")][value]))



        e_constructlist = time.time()
        global t_constructlist
        t_constructlist += e_constructlist - s_constructlist
        return inv_list


    def getOpVars(self, statement, subcon):
        if isinstance(statement, murphi.NegExpr):
            self.getOpVars(statement.expr, subcon)
        elif isinstance(statement, murphi.OpExpr) and not (statement.op == '=' or statement.op == '!='):
                self.getOpVars(statement.expr1, subcon)
                self.getOpVars(statement.expr2, subcon)
        elif isinstance(statement, murphi.OpExpr) and (statement.op == '=' or statement.op == '!='):
            if str(statement.expr1) in all_ins_vars and str(statement.expr1) not in subcon:
                subcon.append(str(statement.expr1))
            if str(statement.expr2) in all_ins_vars and str(statement.expr2) not in subcon:
                subcon.append(str(statement.expr2))
        return subcon


    def search_join_aux_invs(self, join_list, diff_list):
        s_smv = time.time()
        join_inv4smt = None

        global listnum_of_callSMV
        listnum_of_callSMV = listnum_of_callSMV + 1

        findjoin_S, join_aux_inv = self.call_Check_join_increase(copy.deepcopy(join_list), copy.deepcopy(diff_list))
        if findjoin_S:
            join_inv4smt = copy.deepcopy(join_aux_inv)
            if self.dataVars:
                types_list = self.getAuxinvIdxtype(join_aux_inv, [])
                genericList, ScalarVarsDict, ScalarVars_values = self.rematchScalarVars(join_aux_inv, [],
                                                                                                    {}, types_list, {})
                if ScalarVarsDict:
                    if self.cnt_listDictlength(ScalarVarsDict, types_list) == False:
                        join_aux_inv = None
                    else:
                        genericList.extend(self.linkage4ScalarVars(ScalarVarsDict, ScalarVars_values))
                        join_aux_inv = murphi.NegExpr(self.join_statements(genericList))
            if join_aux_inv!=None:
                global all_auxinv
                all_auxinv = all_auxinv + 1
                global symm_auxinv
                symm_auxinv = symm_auxinv + 1
                with open(self.inv_path + "_invs.txt", "a") as file:
                    file.write(f"invariant \"{self.name}_{self.invnums}\"\n")
                    file.write(murphi.indent(str(join_aux_inv) + ";", 2))
                    file.write("\n")
            else:
                join_aux_inv = None
        e_smv = time.time()
        global t_smv
        t_smv += e_smv - s_smv

        if join_aux_inv != None:
            join_inv4smt = None

        return join_aux_inv, join_inv4smt



    def search_aux_invs(self, solution):
        s_smv = time.time()
        inv4smt = None

        global listnum_of_callSMV
        listnum_of_callSMV = listnum_of_callSMV + 1

        findS = self.call_Check_increase(solution)


        if findS:
            inv4smt = copy.deepcopy(self.aux_inv)
            if self.dataVars:
                # types_list = list()
                types_list = self.getAuxinvIdxtype(self.aux_inv, [])
                genericList, ScalarVarsDict, ScalarVars_values = self.rematchScalarVars(self.aux_inv, [],
                                                                                                    {}, types_list, {})
                if ScalarVarsDict:
                    if self.cnt_listDictlength(ScalarVarsDict, types_list) == False:
                        self.aux_inv = None
                    else:
                        genericList.extend(self.linkage4ScalarVars(ScalarVarsDict, ScalarVars_values))
                        self.aux_inv = murphi.NegExpr(self.join_statements(genericList))
        if findS and self.aux_inv != None:
            if self.aux_inv != None:
                global all_auxinv
                all_auxinv = all_auxinv + 1
                global symm_auxinv
                symm_auxinv = symm_auxinv + 1
                with open(self.inv_path + "_invs.txt", "a") as file:
                    file.write(f"invariant \"{self.name}_{self.invnums}\"\n")
                    file.write(murphi.indent(str(self.aux_inv) + ";", 2))
                    file.write("\n")        
            else:
                self.aux_inv = None


        else:
            self.aux_inv = None

        e_smv = time.time()
        global t_smv
        t_smv += e_smv - s_smv


        if self.aux_inv != None:
            inv4smt = None
        return self.aux_inv, inv4smt

    def idx_replace(self, expr, symm_map, specificVars = []):
        if isinstance(expr, murphi.ArrayIndex):
            if isinstance(expr.v, murphi.FieldName):
                self.idx_replace(expr.v, symm_map, specificVars)
            elif isinstance(expr.v, murphi.ArrayIndex):
                self.idx_replace(expr.v, symm_map, specificVars)

            if murphi.digitType_map[str(expr.idx.typ)].const_name in symm_map.keys():
                pattern = r'\[([^\]]*)\]'
                varPattern = re.sub(pattern, r"[]", str(expr))
                # print("varPattern:",varPattern)
                if (not specificVars) | (varPattern[:-2] + str(expr)[-3:] in specificVars):
                    if expr.idx.name in symm_map[murphi.digitType_map[str(expr.idx.typ)].const_name].keys():
                        expr.idx.name = expr.idx.name.replace(expr.idx.name, str(symm_map[murphi.digitType_map[str(expr.idx.typ)].const_name][expr.idx.name]))
        elif isinstance(expr, murphi.FieldName):
            if isinstance(expr.v, murphi.FieldName):
                self.idx_replace(expr.v, symm_map, specificVars)
            elif isinstance(expr.v, murphi.ArrayIndex):
                self.idx_replace(expr.v, symm_map, specificVars)
            
        return expr

    def digitvalue_replace(self, expr, symm_map):
        if isinstance(expr, murphi.VarExpr) and expr.name.isdigit():
            expr.name = expr.name.replace(expr.name, str(symm_map[expr.typ.const_name][expr.name]))
        return expr


    def count_digits(self, expr, digitdict, paradict, vardict):
        if isinstance(expr, murphi.NegExpr):
            self.count_digits(expr.expr, digitdict, paradict, vardict)
        if isinstance(expr, murphi.ArrayIndex):
            if isinstance(expr.v, murphi.FieldName):
                self.count_digits(expr.v, digitdict, paradict, vardict)
            elif isinstance(expr.v, murphi.ArrayIndex):
                self.count_digits(expr.v, digitdict, paradict, vardict)

            if expr.idx.name not in digitdict[murphi.digitType_map[str(expr.idx.typ)].const_name]:
                paradict[murphi.digitType_map[str(expr.idx.typ)].const_name] = str(expr.idx.typ)
                digitdict[murphi.digitType_map[str(expr.idx.typ)].const_name].append(expr.idx.name)
            
            if expr not in vardict[murphi.digitType_map[str(expr.idx.typ)].const_name][expr.idx.name]:
                vardict[murphi.digitType_map[str(expr.idx.typ)].const_name][expr.idx.name].append(expr)

        elif isinstance(expr, murphi.FieldName):
            if isinstance(expr.v, murphi.FieldName):
                self.count_digits(expr.v, digitdict, paradict, vardict)
            elif isinstance(expr.v, murphi.ArrayIndex):
                self.count_digits(expr.v, digitdict, paradict, vardict)
        elif isinstance(expr, murphi.VarExpr) and expr.name.isdigit():
            if isinstance(expr.typ, murphi.VarExpr):
                self.count_digits(expr, digitdict, paradict, vardict)
            else:
                if isinstance(expr.typ,murphi.ScalarSetType):
                    if expr.name not in digitdict[expr.typ.const_name]:
                        paradict[expr.typ.const_name] = str(expr.typ)
                        digitdict[expr.typ.const_name].append(expr.name)
                    if expr not in vardict[expr.typ.const_name][expr.name]:
                        vardict[expr.typ.const_name][expr.name].append(expr)
                else:
                    if expr.name not in digitdict[murphi.digitType_map[str(expr.typ)].const_name]:
                        paradict[murphi.digitType_map[str(expr.typ)].const_name] = str(expr.typ)
                        digitdict[murphi.digitType_map[str(expr.typ)].const_name].append(expr.name)
                    if expr not in vardict[murphi.digitType_map[str(expr.typ)].const_name][expr.name]:
                        vardict[murphi.digitType_map[str(expr.typ)].const_name][expr.name].append(expr)
        elif isinstance(expr, murphi.OpExpr):
            self.count_digits(expr.expr1, digitdict, paradict, vardict)
            self.count_digits(expr.expr2, digitdict, paradict, vardict)
        return digitdict,paradict, vardict


    def getsymmform(self, statement, symm_map, specificVars = []):
        if isinstance(statement, murphi.NegExpr):
            statement.expr = self.getsymmform(statement.expr, symm_map,specificVars)
        else:
            if isinstance(statement.expr1, murphi.OpExpr):
                statement.expr1 = self.getsymmform(statement.expr1, symm_map, specificVars)
            if isinstance(statement.expr2, murphi.OpExpr):
                statement.expr2 = self.getsymmform(statement.expr2, symm_map, specificVars)

            if not isinstance(statement.expr1, murphi.OpExpr) and not isinstance(statement.expr2, murphi.OpExpr):
                statement.expr1 = self.idx_replace(statement.expr1, symm_map,specificVars)
                if isinstance(statement.expr2, murphi.VarExpr) and statement.expr2.name.isdigit():
                    statement.expr2 = self.digitvalue_replace(statement.expr2, symm_map)
                else:
                    statement.expr2 = self.idx_replace(statement.expr2, symm_map,specificVars)
        
        return statement
    
    def heuristicComb(self,toComb,exdict,fldict):
        for i,diffD in enumerate(toComb):
            for diffV in diffD:
                if diffV in exdict:
                    toComb[i] = [diffV]
                    break
                if diffV in fldict:
                    toComb[i].remove(diffV)
        return toComb




    def cntInxConcretes(self, vars, cond=[]):
        for var in vars:
            assert isinstance(var, murphi.ArrayIndex)
            if str(var.idx) not in cond:
                cond.append(str(var.idx))
        return cond

    def getallSymmetryInvs_partition(self, ori_inv, subsidiary = False):
        # for ori safety properties
        if self.current_inv not in flpartitionsRecord.keys():
            _, _, vd= self.count_digits(self.inv,defaultdict(list),{},defaultdict(lambda: defaultdict(list)))
            subdict = dict()
            for t,v in vd.items():
                subdict[t] = [value for sublist in vd[t].values() for value in sublist]
            flpartitionsRecord[self.current_inv] = subdict
        symminvs = []
        statements = copy.deepcopy(self.parse_statements(ori_inv,[]))

        def generate_combinations(data):
            keys = list(data.keys())
            values = [data[key] for key in keys]

            for combination in product(*values):
                yield dict(zip(keys, combination))

        def calculate_permutations(m, n):
            elements = list(range(1, m+1))
            permutations = list(itertools.permutations(elements, n))
            return permutations
        
        def calculate_permutationsbygiven(m, n):
            permutations = list(itertools.permutations(m, n))
            return permutations

        digitdict = defaultdict(list)
        vardict = defaultdict(lambda: defaultdict(list))
        digitdict, pd, vardict= self.count_digits(ori_inv,digitdict,{},vardict)
        # print("digitdict:",digitdict)
        # print("pd:", pd)
        # print("vardict:",vardict)


        existsTypes = []
        ori_existsTypes = []
        ori_digitdict = defaultdict(list)
        allvardict = dict()
        for t,v in vardict.items():
            allvardict[t] = [value for sublist in vardict[t].values() for value in sublist]

        symmpartition = dict()
        specificVarPatterns = defaultdict(list)


        if EXISTENTIAL_QUANTIFICATION == True:
            for var,key in digitdict.items():
                if len(key) == murphi.const_map[var]:
                    largerpn = "larger" + var + "_" + self.protocol_name
                    if not self.call_NuSMV(statements,largerpn)[0]:
                    # if not self.call_BMC(statements,largerpn)[0]:
                        existsTypes.append(var)
        


        ori_existsTypes = copy.deepcopy(existsTypes)
        ori_digitdict = copy.deepcopy(digitdict)
        for existType in copy.deepcopy(existsTypes):
            diffpartitionFlag = False
            for item in vardict[existType].values():
                if len(item) > 1:
                    diffpartitionFlag = True
            if diffpartitionFlag == False:
                existsTypes.remove(existType)


        if existsTypes:
            for existsType in existsTypes:
                exdict = []
                if self.current_inv in expartitionsRecord.keys():
                    exdict = expartitionsRecord[self.current_inv][existsType]
                toComb = copy.deepcopy(list(vardict[existsType].values()))
                combed = self.heuristicComb(toComb,exdict,flpartitionsRecord[self.current_inv][existsType])
                value_combinations = list(itertools.product(*[d for d in combed]))

                partitionrecord = []
                for combination in value_combinations:
                    symmFlag = True
                    subpattern = []
                    for convar in combination:
                        pattern = r"\[(\d+)\]"
                        varPattern = re.sub(pattern, r"[]", str(convar))
                        subpattern.append(varPattern[:-2] + str(convar)[-3:])
                    cond = self.cntInxConcretes(combination,[])
                    n = len(cond)
                    m = [int(x) for x in cond]
                    symm_maps = list(generate_combinations({existsType:[{key: value for key, value in zip(cond, tup)} for tup in calculate_permutationsbygiven(m,n)]}))
                    for symm_map in symm_maps:
                        new_statements = []
                        ori_statements = copy.deepcopy(statements)
                        for statement_ in ori_statements:
                            new_statement = self.getsymmform(statement_, symm_map, subpattern)
                            new_statements.append(new_statement)
                        checkpass = self.call_NuSMV(new_statements,self.protocol_name)[0]
                        if checkpass == False:
                            symmFlag = False
                            break
                    if symmFlag == True:
 
                        partitionrecord.append(list(combination))
                        expartitionsRecord[self.name + "_" + str(self.invnums)] = {existsType:list(combination)}
                        specificVarPatterns[existsType].append(subpattern)

                        allvars = [value for sublist in vardict[existsType].values() for value in sublist]
                        forall = []
                        forallpattern = []
                        for statement in allvars:
                            if statement not in combination:
                                forall.append(statement)
                                pattern = r"\[(\d+)\]"
                                varPattern = re.sub(pattern, r"[]", str(statement))
                                forallpattern.append(varPattern[:-2] + str(statement)[-3:])
                        specificVarPatterns[existsType].append(forallpattern)
                        partitionrecord.append(forall)
                        symmpartition[existsType] = partitionrecord
                        allvardict[existsType] = forall
                        break
                assert existsType in digitdict
                del digitdict[existsType]


        flpartitionsRecord[self.name + "_" + str(self.invnums)] = allvardict


        # for concreted to parameterized
        paramapF = dict()
        paramapE = dict()
        paramapEF = dict()
        folvars = defaultdict(list)
        exvars = defaultdict(list)
        exidxpattern = []
        
        # permutation1
        regularpermutations = []
        regulardict = dict()
        for type,digits in digitdict.items():
            m = murphi.const_map[type]
            n = len(digits)
            regulardict[type] = [{key: value for key, value in zip(digits, tup)} for tup in calculate_permutations(m,n)]
        regularpermutations = list(generate_combinations(regulardict))
        


        for type,digits in digitdict.items():
            if type in ori_existsTypes:
                subdictE = dict()
                for digit in digits:
                    paraAlp = paraAlpdict[type][1]
                    subdictE[digit] = paraAlp
                    if paraAlp not in exvars[type]:
                        exvars[type].append(paraAlp)
                        exidxpattern.append("["+paraAlp+"]")
                paramapE[type] = subdictE
            else:
                subdict = dict()
                for digit in digits:
                    paraAlp = paraAlpdict[type][0] + str(digit)
                    subdict[digit] = paraAlp
                    if paraAlp not in folvars[type]:
                        folvars[type].append(paraAlp)
                paramapF[type] = subdict
                

        # permutation2 & 3 for special type with both exists & forall
        existspermutations = []
        forallpermutations = []
        existsdict = dict()
        foralldict = dict()
        for type,partition in symmpartition.items():
            existsvars = partition[0]
            existscond = self.cntInxConcretes(existsvars,[])
            m = murphi.const_map[type]
            n = len(existscond)
            subdictE = dict()
            for digit in existscond:
                paraAlp = paraAlpdict[type][1]
                subdictE[digit] = paraAlp
                if paraAlp not in exvars[type]:
                    exvars[type].append(paraAlp)
                    exidxpattern.append("["+paraAlp+"]")
            paramapE[type] = subdictE

            existsdict[type] = [{key: value for key, value in zip(existscond, tup)} for tup in calculate_permutations(m,n)]
            if partition[1]:
                forallvars = partition[1]
                forallcond = self.cntInxConcretes(forallvars,[])
                m = murphi.const_map[type]
                n = len(forallcond)

                subdictF = dict()
                for digit in forallcond:
                    paraAlp = paraAlpdict[type][0] + str(digit)
                    subdictF[digit] = paraAlp
                    if paraAlp not in folvars[type]:
                        folvars[type].append(paraAlp)
                paramapEF[type] = subdictF

                foralldict[type] = [{key: value for key, value in zip(forallcond, tup)} for tup in calculate_permutations(m,n)]
        if existsdict:
            existspermutations = list(generate_combinations(existsdict))
        if foralldict:
            forallpermutations = list(generate_combinations(foralldict))


        for regularp in regularpermutations:

            ori_statements = copy.deepcopy(statements)
            for statement1 in ori_statements:
                self.getsymmform(statement1, regularp, [])

            #
            if existspermutations:
                for existsp in existspermutations:

                    ori_statements1 = copy.deepcopy(ori_statements)
                    spvp = [specificVarPatterns[key][0] for key in existsp.keys()]
                    for statement2 in ori_statements1:
                        self.getsymmform(statement2, existsp, [element for sublist in spvp for element in sublist])
 
                    #
                    if forallpermutations:
                        for forallp in forallpermutations:

                            ori_statements2 = copy.deepcopy(ori_statements1)
                            spvp = [specificVarPatterns[key][1] for key in forallp.keys()]
                            for statement3 in ori_statements2:
                                self.getsymmform(statement3, forallp, [element for sublist in spvp for element in sublist])
                            symm_inv = murphi.NegExpr(self.join_statements(ori_statements2))
                            symminvs.append(symm_inv)
                    else:
                        symm_inv = murphi.NegExpr(self.join_statements(ori_statements1))
                        symminvs.append(symm_inv)
            else:
                symm_inv = murphi.NegExpr(self.join_statements(ori_statements))
                symminvs.append(symm_inv)




        if not subsidiary: 
            ori_parastatements = copy.deepcopy(statements)
            for statement1 in ori_parastatements:
                self.getsymmform(statement1, paramapF, [])
            if not existspermutations:
                for statement2 in ori_parastatements:
                    self.getsymmform(statement2, paramapE, [])
            else:
                spvp = [specificVarPatterns[key][0] for key in paramapE.keys()]
                for statement3 in ori_parastatements:
                    self.getsymmform(statement3, paramapE, [element for sublist in spvp for element in sublist])
                if forallpermutations:
                    spvp = [specificVarPatterns[key][1] for key in paramapEF.keys()]
                    for statement4 in ori_parastatements:
                        self.getsymmform(statement4, paramapEF, [element for sublist in spvp for element in sublist])


            parainvdict = dict()
            if ori_existsTypes:
                exitems = []
                folitems = []
                for statement in ori_parastatements:
                    if any(idx in str(statement) for idx in exidxpattern):
                        if statement not in exitems:
                            exitems.append(statement)
                    else:
                        folitems.append(statement)
                parainvdict['existsitem'] = exitems
                parainvdict['folitem'] = folitems
                parainvdict['existsvars'] = exvars
                parainvdict['folvars'] = folvars
                exfolparainvs.append(parainvdict)
            else:
                parainvdict['folstatements'] = copy.deepcopy(ori_parastatements)
                parainvdict['folvars'] = folvars
                allparainvs.append(parainvdict)


        return symminvs



    def cnt_validVars(self, subOps):
        validVars = []
        for subOp in subOps:
            assert isinstance(subOp, murphi.OpExpr)
            assert subOp.op == '=' or subOp.op == '!='
            if str(subOp.expr1) not in validVars:
                if isinstance(subOp.expr1, murphi.ArrayIndex) or isinstance(subOp.expr1, murphi.FieldName):
                    validVars.append(str(subOp.expr1))
                elif str(subOp.expr1) in c.prot.var_map:
                    validVars.append(str(subOp.expr1))

                if isinstance(subOp.expr2, murphi.ArrayIndex) or isinstance(subOp.expr2, murphi.FieldName):
                    validVars.append(str(subOp.expr2))
                elif str(subOp.expr2) in c.prot.var_map:
                    validVars.append(str(subOp.expr2))

        return len(validVars)

    def smvform_act(self, form):
        global EnumType_vars
        if isinstance(form, murphi.NegExpr):
            self.smvform_act(form.expr)
        elif isinstance(form, murphi.OpExpr):
            if isinstance(form.expr1, murphi.OpExpr) | isinstance(form.expr2, murphi.OpExpr):
                if isinstance(form.expr1, murphi.OpExpr):
                    self.smvform_act(form.expr1)
                if isinstance(form.expr2, murphi.OpExpr):
                    self.smvform_act(form.expr2)
            else:
                if str(form.expr1) in EnumType_vars.keys() and isinstance(form.expr2, murphi.EnumValExpr):
                    form.expr2.enum_val = form.expr2.enum_val.replace(form.expr2.enum_val, form.expr2.enum_val.lower())
        return form

    def getidxtyp(self, idxvar, types_list):
        if isinstance(idxvar, murphi.ArrayIndex):
            if str(idxvar.idx.typ) not in types_list:
                types_list.append(str(murphi.digitType_map[str(idxvar.idx.typ)]))
        elif isinstance(idxvar, murphi.FieldName):
            self.getidxtyp(idxvar.v, types_list)


    def getAuxinvIdxtype(self, OpExpr, types_list=[]):
        types_list = types_list
        if isinstance(OpExpr, murphi.NegExpr):
            self.getAuxinvIdxtype(OpExpr.expr, types_list)
        elif isinstance(OpExpr, murphi.OpExpr):
            if OpExpr.op == '&' or OpExpr.op == '|' or OpExpr.op == '->':
                self.getAuxinvIdxtype(OpExpr.expr1, types_list)
                self.getAuxinvIdxtype(OpExpr.expr2, types_list)
            else:
                if "[" in str(OpExpr.expr1) and "]" in str(OpExpr.expr1):
                    self.getidxtyp(OpExpr.expr1, types_list)
        return types_list


    def rematchScalarVars(self, OpExpr, invlist, ScalarVarsDict, types_list, ScalarVars_values={}):
        ScalarVars_values = ScalarVars_values
        if isinstance(OpExpr, murphi.NegExpr):
            self.rematchScalarVars(OpExpr.expr, invlist, ScalarVarsDict, types_list, ScalarVars_values)
        elif isinstance(OpExpr, murphi.OpExpr):
            if OpExpr.op == '&' or OpExpr.op == '|' or OpExpr.op == '->':
                self.rematchScalarVars(OpExpr.expr1, invlist, ScalarVarsDict, types_list, ScalarVars_values)
                self.rematchScalarVars(OpExpr.expr2, invlist, ScalarVarsDict, types_list, ScalarVars_values)
            else:
                if "[" in str(OpExpr.expr1) and "]" in str(OpExpr.expr1):
                    self.getidxtyp(OpExpr.expr1, types_list)

                if str(OpExpr.expr2).isdigit() and str(OpExpr.expr2.typ) not in types_list:
                    ScalarVars_values[str(OpExpr.expr1)] = OpExpr.expr2

                    assert isinstance(OpExpr.expr2, murphi.VarExpr)
                    if str(OpExpr.expr2.typ) not in ScalarVarsDict.keys():
                        ScalarVarsDict[str(OpExpr.expr2.typ)] = {str(OpExpr.expr2): [OpExpr.expr1]}
                    else:
                        if str(OpExpr.expr2) not in ScalarVarsDict[str(OpExpr.expr2.typ)].keys():
                            ScalarVarsDict[str(OpExpr.expr2.typ)][str(OpExpr.expr2)] = [OpExpr.expr1]
                        else:
                            ScalarVarsDict[str(OpExpr.expr2.typ)][str(OpExpr.expr2)].append(OpExpr.expr1)
                else:
                    invlist.append(OpExpr)
        return invlist, ScalarVarsDict, ScalarVars_values


    def linkage4ScalarVars(self, ScalarVarsDict, ScalarVars_values):
        ScalarVarsLinkage = []
        Neglist = []

        def constructEqual(Varlist):
            if len(Varlist) == 1:
                return Varlist[0]
            return murphi.OpExpr('=', Varlist[-1], constructEqual(Varlist[:-1]))

        def constructNegEqual(Varlist):
            if len(Varlist) == 1:
                return Varlist[0]
            return murphi.OpExpr('!=', Varlist[-1], constructNegEqual(Varlist[:-1]))

        for typ, values in ScalarVarsDict.items():
            equals = False
            for num, vars in values.items():
                Neglist.append(vars[0])
                if len(vars) > 1:
                    equals = True
                    ScalarVarsLinkage.append(constructEqual(vars))
            if len(Neglist) > 1:
                ScalarVarsLinkage.append(constructNegEqual(Neglist))
            elif len(Neglist) == 1 and equals == False:
                ScalarVarsLinkage.append(murphi.OpExpr('=', Neglist[0], ScalarVars_values[str(Neglist[0])]))
        return ScalarVarsLinkage

    def call_Check(self, inv_list):

        pass_check, can_inv = self.call_NuSMV(inv_list, self.protocol_name)

        # pass_check, can_inv = self.call_BMC(inv_list, self.protocol_name)

        # pass_check, can_inv = self.call_cmurphi(inv_list)
        
        if pass_check:
            self.join_aux_inv = can_inv
            if len(inv_list) > 1:
                for sublist in self.get_sublists(inv_list, len(inv_list) - 1):
                    if self.call_Check(sublist):
                        break
            return True
        else:
            return False


    def generate_n_length_sublist(self, inv_list, n):
        if len(inv_list) < n:
            return []
        
        n_length_sublists = []
        self.generate_sublists([], inv_list, n, n_length_sublists)
        return n_length_sublists


    def generate_sublists(self, current_sublist, remaining_elements, n, result):
        if n == 0: 
            result.append(current_sublist)
            return
        if not remaining_elements:
            return

        self.generate_sublists(current_sublist + [remaining_elements[0]], remaining_elements[1:], n - 1, result)
        self.generate_sublists(current_sublist, remaining_elements[1:], n, result)




    def call_Check_join_increase(self, join_list, diff_list):
        findjoinS = False
        join_aux_invs = None
        n = 1
        while n <= len(diff_list):
            if findjoinS:
                break
            n_length_sublists = self.generate_n_length_sublist(diff_list, n)

            for sublist in n_length_sublists:
                validFlag = True
                joindigitlist = defaultdict(list)
                ready_to_check = sublist + join_list
                heuristicFlag = self.protocol_name == "flash" or self.protocol_name == "flashNodata"
                if heuristicFlag:
                    for item in ready_to_check:
                        assert isinstance(item, murphi.OpExpr)
                        joindigitlist,_,_ = self.count_digits(item.expr1, joindigitlist, {}, defaultdict(lambda: defaultdict(list)))
                        joindigitlist,_,_ = self.count_digits(item.expr2, joindigitlist, {}, defaultdict(lambda: defaultdict(list)))
                    if any(len(lst) > 2 for lst in joindigitlist.values()):
                        pass_check, can_inv = False, None
                        validFlag = False
                    else:
                        inv_to_symm = str(murphi.NegExpr(self.join_statements(sublist + join_list)))
                        if "[4]" in inv_to_symm or "= 4" in inv_to_symm or "[3]" in inv_to_symm or "= 3" in inv_to_symm:
                            ready_to_check = self.parse_statements(self.getallSymmetryInvs_partition(murphi.NegExpr(self.join_statements(sublist + join_list)),subsidiary=True)[0], [])
                if validFlag:
                    pass_check, can_inv = self.call_NuSMV(ready_to_check, self.protocol_name)
                    # pass_check, can_inv = self.call_BMC(ready_to_check, self.protocol_name)
                # pass_check, can_inv = self.call_cmurphi(ready_to_check)
                if pass_check:
                    # fix : should check again
                    findjoinSnd = self.call_Check(ready_to_check)
                    join_aux_invs = copy.deepcopy(self.join_aux_inv)
                    self.join_aux_inv = None
                    invitems = self.parse_statements(join_aux_invs, [])
                    findjoinS = True
                    break

            n = n + 1
        
        return findjoinS, join_aux_invs





    def call_Check_increase(self, inv_list):
        findS = False
        inv_list_length = len(inv_list)
        for n in range(1, inv_list_length+1):
            if findS:
                break
            n_length_sublists = self.generate_n_length_sublist(inv_list, n)
            for sublist in n_length_sublists:
                validFlag = True
                digitlist = defaultdict(list)
                ready_to_check = sublist
                heuristicFlag = self.protocol_name == "flash" or self.protocol_name == "flashNodata"
                if heuristicFlag:
                    for statement in sublist:
                        assert isinstance(statement, murphi.OpExpr)
                        digitlist,_,_ = self.count_digits(statement.expr1, digitlist, {}, defaultdict(lambda: defaultdict(list)))
                        digitlist,_,_ = self.count_digits(statement.expr2, digitlist, {}, defaultdict(lambda: defaultdict(list)))
                    if any(len(lst) > 2 for lst in digitlist.values()):
                        pass_check, can_inv = False, None
                        validFlag = False
                    else:
                        inv_to_symm = str(murphi.NegExpr(self.join_statements(sublist)))
                        if "[4]" in inv_to_symm or "= 4" in inv_to_symm or "[3]" in inv_to_symm or "= 3" in inv_to_symm:
                            ready_to_check = self.parse_statements(self.getallSymmetryInvs_partition(murphi.NegExpr(self.join_statements(sublist)),subsidiary=True)[0], [])
                if validFlag:
                    pass_check, can_inv = self.call_NuSMV(ready_to_check, self.protocol_name)
                    # pass_check, can_inv = self.call_BMC(ready_to_check, self.protocol_name)
                # pass_check, can_inv = self.call_cmurphi(ready_to_check)
                if pass_check:
                    self.aux_inv = can_inv
                    findS = True
                    break
        return findS


    def parse_all_eqs(self, statement, subcon):
        if isinstance(statement, murphi.NegExpr):
            self.parse_all_eqs(statement.expr, subcon)
        elif isinstance(statement, murphi.OpExpr) and statement.op in ('&', '->', '|'):
            if isinstance(statement.expr1, murphi.OpExpr) and statement.expr1.op in ('&', '->', '|'):
                self.parse_all_eqs(statement.expr1, subcon)
            elif isinstance(statement.expr1, murphi.NegExpr):
                self.parse_all_eqs(statement.expr1.expr, subcon)
            else:
                if statement.expr1 not in subcon:
                    subcon.append(statement.expr1)
            if isinstance(statement.expr2, murphi.OpExpr) and statement.expr2.op in ('&', '->', '|'):
                self.parse_all_eqs(statement.expr2, subcon)
            elif isinstance(statement.expr2, murphi.NegExpr):
                self.parse_all_eqs(statement.expr2.expr, subcon)
            else:
                if statement.expr2 not in subcon:
                    subcon.append(statement.expr2)
        elif isinstance(statement, murphi.OpExpr) and (statement.op == '=' or statement.op == '!='):
            if statement not in subcon:
                subcon.append(statement)
        return subcon

    def parse_statements(self, statement, subcon):
        if isinstance(statement, murphi.NegExpr):
            self.parse_statements(statement.expr, subcon)
        elif isinstance(statement, murphi.OpExpr) and statement.op == '&':
            if isinstance(statement.expr1, murphi.OpExpr) and statement.expr1.op == '&':
                self.parse_statements(statement.expr1, subcon)
            else:
                subcon.append(statement.expr1)
            if isinstance(statement.expr2, murphi.OpExpr) and statement.expr2.op == '&':
                self.parse_statements(statement.expr2, subcon)
            else:
                subcon.append(statement.expr2)
        elif isinstance(statement, murphi.OpExpr) and (statement.op == '=' or statement.op == '!='):
            subcon.append(statement)
        return subcon

    def OpExprEq(self, OpExpr, patternlist, pattern, patternDict, newPattern, symmnewPattern):
        # varitems = len(OpExpr)
        Oplist = []
        symmOplist = []
        var_pattern = r'\S*\[.*?\]\S*'
        self.var_list = []
        # vardict = dict()

        def replace_with_underscores(match):
            number = match.group(1)
            underscore = '_' * int(number)
            return '= ' + underscore

        def reverse_replace_with_underscores(match):
            number = match.group(1)
            underscore = '_' * (3 - int(number))
            return '= ' + underscore

        def replace_with_underscores_idx(match):
            number = match.group(1)
            underscore = '_' * int(number)
            return '[' + underscore + ']'

        def reverse_replace_with_underscores_idx(match):
            number = match.group(1)
            underscore = '_' * (3 - int(number))
            return '[' + underscore + ']'

        matches = []
        for item in OpExpr:
            # print(item)
            right_digit_pattern = r"=\s*(\d+)"
            match = re.search(right_digit_pattern, str(item))
            if match:
                result = re.sub(right_digit_pattern, replace_with_underscores, str(item))
                symmresult = re.sub(right_digit_pattern, reverse_replace_with_underscores, str(item))
                Oplist.append(re.sub(pattern, replace_with_underscores_idx, str(result)))
                symmOplist.append(re.sub(pattern, reverse_replace_with_underscores_idx, str(symmresult)))
            else:
                # print(re.sub(pattern, replace_with_underscores_1, str(item)))
                Oplist.append(re.sub(pattern, replace_with_underscores_idx, str(item)))
                symmOplist.append(re.sub(pattern, reverse_replace_with_underscores_idx, str(item)))
            # Oplist.append(re.sub(pattern, r'[_]', str(item)))
            matches.extend(re.findall(var_pattern, str(item)))

        matches = set(matches)
        # print("matches:",matches)

        for var in self.paraVars:
            if list(var.keys())[0] in set(matches):
                self.var_list.append(var)
        # vardict = self.count_values(self.var_list)
        varitems = dict(Counter(Oplist))
        symmvaritems = dict(Counter(symmOplist))


        pattern_value = varitems
        symmpattern_value = symmvaritems

        # vardict_flattern = ', '.join([f"{key}: {value}" for key, value in vardict.items()])

        varitems_flattern = ', '.join([f"{key}: {value}" for key, value in varitems.items()])
        symmvaritems_flattern = ', '.join([f"{key}: {value}" for key, value in symmvaritems.items()])


        for pattern in patternlist:
            if set(pattern) == set(Oplist) and pattern_value in patternDict[tuple(pattern)]:
                exist_pattern_value = patternDict[tuple(pattern)][patternDict[tuple(pattern)].index(pattern_value)]
                sub_pattern_value_flattern = ', '.join([f"{key}: {value}" for key, value in exist_pattern_value.items()])
                newPattern.append(sub_pattern_value_flattern)

                return True, newPattern, symmnewPattern
            elif set(pattern) == set(Oplist) and pattern_value not in patternDict[tuple(pattern)]:

                newPattern.append(varitems_flattern)
                # newPattern.append(vardict_flattern)

                symmnewPattern.append(symmvaritems_flattern)

                patternDict[tuple(pattern)].append(pattern_value)
                for symmpattern in patternlist:
                    if set(symmpattern) == set(symmOplist) and symmpattern_value not in patternDict[tuple(symmpattern)]:
                        patternDict[tuple(symmOplist)].append(symmpattern_value)
                return False, newPattern, symmnewPattern


        newPattern.append(varitems_flattern)
        # newPattern.append(vardict_flattern)

        symmnewPattern.append(symmvaritems_flattern)
        # symmnewPattern.append(vardict_flattern)

        patternlist.append(list(set(Oplist)))

        patternDict[tuple(list(set(Oplist)))].append(pattern_value)

        patternlist.append(list(set(symmOplist)))

        patternDict[tuple(list(set(symmOplist)))].append(symmpattern_value)

        return False, newPattern, symmnewPattern

    def symmetry_statute(self, inv, patternForInv, patternDict, newPattern, symmnewPattern):
        pattern = r'\[([^]]+)\]'

        inv_cons = self.parse_statements(inv, [])
        result, newPatternlist, symmnewPatternlist = self.OpExprEq(inv_cons, patternForInv, pattern, patternDict, newPattern, symmnewPattern)
        if result:
            return False
        return True

    def cnt_listDictlength(self, listdict, types_list):
        for name, values in listdict.items():
            specific_length = 0
            for value in values.values():
                if isinstance(value, list):
                    specific_length += len(value)
            if specific_length == 1 and name not in types_list:
                return False
        return True

    def call_NuSMV(self, inv_list, protocol_name):

        

        # 对称list避免调用SMV
        tmp_inv = murphi.NegExpr(self.join_statements(inv_list))

        global callNuSMV
        callNuSMV = callNuSMV + 1
        inv_to_check = str(self.smvform_act(copy.deepcopy(tmp_inv))).replace("true", "TRUE")
        inv_to_check = str(self.smvform_act(inv_to_check)).replace("false", "FALSE")
        
        is_true = client.check_invariants(protocol_name, inv_to_check)

        return is_true, tmp_inv


    def call_BMC(self, inv_list, protocol_name):
        # 对称list避免调用SMV
        tmp_inv = murphi.NegExpr(self.join_statements(inv_list))

        global callNuSMV
        callNuSMV = callNuSMV + 1

        inv_to_check = str(self.smvform_act(copy.deepcopy(tmp_inv))).replace("true", "TRUE")
        inv_to_check = str(self.smvform_act(inv_to_check)).replace("false", "FALSE")
                
        # is_true = client.is_inv_bmc(self.protocol_name, inv_to_check)
        is_true = client.is_inv_bmc(protocol_name, inv_to_check)
        

        return is_true, tmp_inv

    def call_cmurphi(self, inv_list):
        global callLS
        callLS = callLS + 1
        can_inv = murphi.NegExpr(self.join_statements(inv_list))
        new_inv = f"invariant \"{self.name}\"\n {murphi.indent(str(can_inv), 2)};"
        self.appendInv_and_save(self.inv_path + "_withoutInv.m", new_inv, self.inv_path + "_newTmp.m")

        cmurphi_path = '../cmurphi_LS/cmurphi_LS'
        # file = '../protocols/mutualEx/mutualEx.m'
        file = self.inv_path
        process1 = subprocess.Popen("{0}/src/mu {1}_newTmp.m".format(cmurphi_path, file), shell=True,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE)
        (stdout, stderr) = process1.communicate()
        if not re.search(r'Code generated', stdout.decode('utf-8')):
            raise ValueError

        command2 = "g++ -ggdb -o {0}_newTmp.o {0}_newTmp.cpp -I {1}/include -lm".format(file, cmurphi_path)
        process2 = subprocess.Popen(command2, shell=True,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE)
        process2.communicate()
        if not os.path.exists("./{0}_newTmp.o".format(file)): raise FileExistsError

        process3 = subprocess.Popen("./{0}_newTmp.o".format(file), shell=True,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE)

        (stdoutdata, stderrdata) = process3.communicate()

        lsOutput = stdoutdata.decode('utf-8')
        pattern_counter = re.compile(r'Invariant\s"(\w+).*"\sfailed')
        counter_ex = re.findall(pattern_counter, lsOutput)

        pattern_pass = "No error found."

        pattern_undefined = re.compile(r'The undefined value at (\w+).* is referenced')
        undefined_ex = re.findall(pattern_undefined, lsOutput)

        pattern_overload = re.compile(r'(\w+).* Too many active states')
        overload_ex = re.findall(pattern_overload, lsOutput)

        os.remove('%s_newTmp.cpp' % file)
        os.remove('%s_newTmp.o' % file)
        # os.remove('%s_newTmp.m' % file)

        

        if undefined_ex:
            raise ValueError(f"var {undefined_ex} is undefined at candidate invariant:\n{new_inv}\n!")
        
        if counter_ex:
            print("check :", can_inv, False)
            print("lsOutput:")
            print(lsOutput)
            return False, can_inv

        if overload_ex:
            print("check :", can_inv, True)
            return True,can_inv

        if not counter_ex and pattern_pass in lsOutput:
            print("check :", can_inv, True)
            # print('No cti found. The invariants are OK.')
            return True, can_inv
        elif not counter_ex and pattern_pass not in lsOutput:
            print("check :", can_inv, True)
            return True,can_inv
        else:
            raise ValueError(f"error when LS check the following candidate invariant:\n{new_inv}\n")


    def appendInv_and_save(self, file_path, new_inv, new_file_path):
        with open(file_path, 'r') as file:
            content = file.read()

        updated_protocol = content + new_inv

        with open(new_file_path, 'w') as new_file:
            new_file.write(updated_protocol)

    def get_sublists(self, lst, sublist_length):
        sublists = list(itertools.combinations(lst, sublist_length))
        sublists = [list(sublist) for sublist in sublists]  # 转换为列表形式
        return sublists

    def dedoubleNeg(self, fomula):
        if isinstance(fomula, murphi.NegExpr) and isinstance(fomula.expr, murphi.NegExpr):
            return fomula.expr.expr
        else:
            return fomula

    def get_inv_var_length(self, inv, inv_var_length):
        assert isinstance(inv, murphi.OpExpr)
        if isinstance(inv.expr1, murphi.OpExpr):
            inv_var_length = self.get_inv_var_length(inv.expr1, inv_var_length)
        if isinstance(inv.expr2, murphi.OpExpr):
            inv_var_length = self.get_inv_var_length(inv.expr2, inv_var_length)
        if isinstance(inv.expr1, murphi.ArrayIndex):
            return inv_var_length + 1
        if isinstance(inv.expr2, murphi.ArrayIndex):
            return inv_var_length + 1
        return inv_var_length

        # if isinstance(inv.expr2, murphi.OpExpr):
        #     self.get_inv_var_map(inv.expr2)

    def get_inv_var_map(self, inv, inv_list):
        assert isinstance(inv, murphi.OpExpr)
        if isinstance(inv.expr1, murphi.OpExpr):
            self.get_inv_var_map(inv.expr1, inv_list)
        elif isinstance(inv.expr1, murphi.EnumValExpr) or isinstance(inv.expr1, murphi.BooleanExpr) or str(inv.expr1).isdigit():
            pass
        else:
            if inv.expr1 not in inv_list:
                inv_list.append(inv.expr1)
        if isinstance(inv.expr2, murphi.OpExpr):
            self.get_inv_var_map(inv.expr2, inv_list)
        elif isinstance(inv.expr2, murphi.EnumValExpr) or isinstance(inv.expr2, murphi.BooleanExpr) or str(inv.expr2).isdigit():
            pass
        else:
            if inv.expr2 not in inv_list:
                inv_list.append(inv.expr2)

        return inv_list


    def murphi_paraInv(self, ori_inv):
        murphilines = ""
        largestletter = ord("i") -1 
        def gen_parameters(digits, startletter, largestletter):
            parameters = {}
            letter = startletter 
            letterlist = []

            for item in digits:
                parameters[item] = chr(letter)  # 将列表中的每一项映射到字母
                letterlist.append(chr(letter))
                letter += 1  # 递增字母的ASCII码值
                largestletter += 1

            return parameters,letterlist, largestletter
        
        def join_parameters_items(dictionary):
            result = []

            for value in dictionary.values():
                if len(value) > 1:
                    items = " != ".join(value)  # 使用 "!=" 连接列表中的元素
                    result.append(items)
            if result:
                joined_str = " & ".join(result)  + " -> " # 使用 "&" 连接不同项
            else:
                joined_str = " & ".join(result) 

            return joined_str

        def expand_parameters(dictionary):
            result = ""
            fornum = 0

            for key, value in dictionary.items():
                for item in value:
                    expanded_str = f"forall {item} : {key} do "
                    fornum = fornum + 1
                    result += expanded_str

            return result,fornum


        digitdict = defaultdict(list)
        digitdict, typedict = self.count_digits(ori_inv,digitdict,{},{})

        parametersdict = dict()
        parametersinv = None
        letterdict = dict()
        

        if digitdict:
            for type,digits in digitdict.items():
                parametersdict[type],letterdict[typedict[type]],largestletter = gen_parameters(digits,largestletter+1,largestletter)
            new_statements = []
            ori_statements = copy.deepcopy(self.parse_statements(ori_inv,[]))
            for statement_ in ori_statements:
                new_statement = self.getsymmform(statement_, parametersdict)
                new_statements.append(new_statement)
            parametersinv = murphi.NegExpr(self.join_statements(new_statements))
            forallLine,forallNum = expand_parameters(letterdict)
            murphilines += forallLine + "\n"
            murphilines += join_parameters_items(letterdict) + "\n"
            murphilines += str(parametersinv) + "\n"
            murphilines += "end " * forallNum + ";\n"
        else:
            murphilines += str(ori_inv) + ";\n"

        return murphilines



    def parainvsMerger(self):
        ivyINVs = ""
        # 公共项相同 + exists类型相同的，合并
        classifiedMergers = dict()
        for exinv in exfolparainvs:
            exfolitem_value = str(exinv['folitem']) + str(exinv['existsvars'])
            if exfolitem_value not in classifiedMergers.keys():
                classifiedMergers[exfolitem_value] = [exinv]
            else:
                classifiedMergers[exfolitem_value].append(exinv)
        for classifiedMerger in classifiedMergers.values():
            folstatements = []
            exstatements = []
            folvardict = defaultdict(list)
            existsvardict = defaultdict(list)
            for value in classifiedMerger:
                for exitem in value['existsitem']:
                    if exitem not in exstatements:
                        exstatements.append(exitem)
                for folitem in value['folitem']:
                    if folitem not in folstatements:
                        folstatements.append(folitem)
                for type,exidx in value['existsvars'].items():
                    for idx in exidx:
                        if idx not in existsvardict[type]:
                            existsvardict[type].append(idx)
                for type,folidx in value['folvars'].items():
                    for idx in folidx:
                        if idx not in folvardict[type]:
                            folvardict[type].append(idx)
            allparainvs.append({'folstatements' : folstatements, 'exstatements' : exstatements, 'folvars' : folvardict, 'exvars' : existsvardict})
        for allparainv in allparainvs:
            # print("allparainv:",allparainv)
            ivyINV = "conjecture "
            vars = ""
            varsbound = []
            for folvars in allparainv['folvars'].values():
                if len(folvars) == 1:
                    vars += "forall " + folvars[0] + "."
                else:
                    vars += "forall "
                    vars += ','.join(folvars)
                    vars += '.'
                    varsbound.extend('~='.join(pair) for pair in [(x, y) for i, x in enumerate(folvars) for j, y in enumerate(folvars) if i < j])
            if 'exstatements' in allparainv.keys():
                for exvars in allparainv['exvars'].values():
                    for exvar in exvars:
                        vars += "exists " + exvar + "."
            ivyINV += vars
            if varsbound:
                ivyINV += ' & '.join(varsbound)
                ivyINV += " -> ~("
            else:
                ivyINV += " ~("
            if allparainv['folstatements']:
                folst = self.ivyform(allparainv['folstatements'])
                ivyINV += ' & '.join(folst)
            if 'exstatements' in allparainv.keys():
                if allparainv['folstatements']:
                    ivyINV += " & "
                    ivyINV += "("
                exst = self.ivyform(allparainv['exstatements'])
                ivyINV += ' | '.join(exst)
                if allparainv['folstatements']:
                    ivyINV += ")"
            ivyINV += ")"

            # ivyINV = ivyINV.replace("][",",")
            # ivyINV = ivyINV.replace("[","(")
            # ivyINV = ivyINV.replace("]",")")
            ivyINVs += ivyINV + "\n"
        
        shutil.copyfile(self.inv_path + ".ivy", self.inv_path + "_proved.ivy")
        with open(self.inv_path + "_proved.ivy", "a") as file:
            file.write(ivyINVs + "\n")
            file.write("\n")

    
    def ivyform(self,stlist):
        
        def ivyVar(opexpr):
            matches = re.findall(r'\[[^\]]+\]', str(opexpr))
            ivyexpr = re.sub(r'\[[^\]]+\]', '', str(opexpr)) + ''.join(matches)
            ivyexpr = ivyexpr.replace(".","_")
            ivyexpr = ivyexpr.replace("!","~")
            ivyexpr = ivyexpr.replace("][",",")
            ivyexpr = ivyexpr.replace("[","(")
            ivyexpr = ivyexpr.replace("]",")")
            return ivyexpr

        ivylist = []
        for st in stlist:
            assert isinstance(st,murphi.OpExpr)
            expr1 = ivyVar(st.expr1)
            expr2 = ivyVar(st.expr2)
            op = str(st.op).replace("!=","~=")
            ivylist.append(str(expr1) + " " + op + " " + str(expr2))
        return ivylist




def defEnum(c):
    for enum_typ, enum_value in c.enum_typ_map.items():
        if enum_typ in enum_value_map.keys():
            pass
        else:
            assert isinstance(enum_value, murphi.EnumType)
            sub_enumValue = dict()
            enumDef = ""
            valueDef = []
            sub_enumValue[enum_typ] = z3.DatatypeSortRef
            for index, name in enumerate(enum_value.names):
                sub_enumValue[name] = z3.DatatypeRef
                if index == len(enum_value.names) - 1:
                    enumDef = enumDef + f"sub_enumValue[\"{name}\"]"
                else:
                    enumDef = enumDef + f"sub_enumValue[\"{name}\"], "
                valueDef.append(name)
            # like enumType["CACHE_STATE"],(enumValue["I"], enumValue["S"], enumValue["E"]) = EnumSort('CACHE_STATE',['I', 'S', 'E'])
            exec_line = "sub_enumValue[enum_typ], " + "(" + enumDef + ")" + "=" + "EnumSort" + "(enum_typ, valueDef)"
            exec(exec_line)
            enum_value_map[enum_typ] = sub_enumValue


def search4new_auxInv(c, constructF, inv_name, new_inv):
    c.inv_instance = {}
    c.inv_var_length = {}
    c.rule_var_ins = {}
    c.ins_var_dict = {}
    c.formula_instances = {}

    c.inv_instance = {inv_name: new_inv}
    new_inv = constructF.dedoubleNeg(new_inv)
    inv_var_length = constructF.get_inv_var_length(new_inv.expr, 0)
    c.inv_var_length[inv_name] = inv_var_length

    inv_var_map = {}
    inv_var_list = []
    inv_var_map[inv_name] = constructF.get_inv_var_map(new_inv.expr, inv_var_list)
    c.ins_var_dict = inv_var_map

    c.getRules()



def trans2IVY(parse_path, ivyselect):
    prot = parse_file(parse_path + ".m", ivyselect)
    if ivyselect:
        save = parse_path + ".ivy"
    else:
        save = parse_path + "_out.m"
    with open(save, "w") as f:
        f.write(str(prot))


def run_ivy(ivyFilePath):
    ivy_process = subprocess.Popen("ivy_check {0}".format(ivyFilePath), shell=True,
                                   stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE)
    (stdout, stderr) = ivy_process.communicate()
    stdout = "OK."  #tmp
    if "OK" in str(stdout):
        print("\n\n")
        print("Inductive invariants already generated ! \n")
        print("Pass IVY's check ! \n")
    else:
        print("Can't pass IVY's check ! \n")
        print("Error messages during the runtime are as follows:")
        print(stdout.decode())


def Verification(protocol_path):

    t_calRchset = -1
    t_constructF = -1



    try:
        with open(os.path.dirname(protocol_path) + "/config", "r") as file:
            for line in file:
                parts = line.strip().split("=")
                if len(parts) == 2:
                    var_name = parts[0].strip()
                    var_value_str = parts[1].strip()

                    if var_name == "EXISTENTIAL_QUANTIFICATION":
                        EXISTENTIAL_QUANTIFICATION = var_value_str.lower() == 'true'
                    elif var_name == "USE_HEURISTIC_GENERALIZE":
                        USE_HEURISTIC_GENERALIZE = var_value_str.lower() == 'true'
    except FileNotFoundError:
        print(f"File '{os.path.dirname(protocol_path)}' not found.")

    # sys.stdout = open(inv_path + '.log', 'w')
    # sys.stderr = open(inv_path + '_debug.log', 'w')

    protocol_name = protocol_path.split("/")[-1]


    # using smv as checker
    smv_content = ""
    with open(protocol_path + ".smv", "r") as file:
        smv_content = file.read()


    try:
        s_calRchset = time.time()
        client.calculate_protocol_reachability(protocol_name, smv_content)
        e_calRchset = time.time()
        t_calRchset = e_calRchset - s_calRchset
    except ValueError:
        print("calculate_protocol_reachability failed. Please check if the Server is ready for communication.")


    try:
        for root, dirs, files in os.walk(os.path.dirname(protocol_path)):
            for file in files:
                if file.endswith(".smv"):
                    file_path = os.path.join(root, file)
                    with open(file_path, "r") as file:
                        smv_content = file.read()
                        client.set_bmc(os.path.splitext(os.path.basename(file_path))[0], smv_content)
    except ValueError:
        print("set bmc failed. Please check if the Server is ready for communication")


    open(protocol_path + "_invs.txt", 'w').close()

    s_constructF = time.time()
    c = concretedF.GetSMTformula(parse_name=protocol_path)
    c.getInvs()

    e_constructF = time.time()
    t_constructF = e_constructF - s_constructF

    ori_inv = defaultdict(list)
    all_ori_invs = list()

    for key, value in c.inv_instance.items():
        all_ori_invs.append(value)
        ori_inv[key.split("_")[0]].append(value)

    defEnum(c)

    specific_var = murphi.specific_var
    ScalarSetType_vars = []
    BooleanType_vars = []

    for var, typ in specific_var.items():
        if isinstance(typ, murphi.ScalarSetType) or isinstance(typ, murphi.RngType):
            ScalarSetType_vars.append(var)
        elif isinstance(typ, murphi.BooleanType):
            BooleanType_vars.append(var)
        elif isinstance(typ, murphi.EnumType):
            if str(var) in murphi.specific_enum_var.keys():
                EnumType_vars[str(var)] = murphi.specific_enum_var[str(var)]
                EnumType_vars[str(var) + "'"] = murphi.specific_enum_var[str(var)]

    for var, typ in specific_var.items():
        if var in c.all_ins_vars.keys():
            all_vars[var] = setKey(c.all_ins_vars[var], "", isbool=isinstance(typ, murphi.BooleanType),
                                   isdigit=isinstance(typ, murphi.ScalarSetType) or isinstance(typ,murphi.RngType),
                                   isenum=isinstance(typ, murphi.EnumType))
            all_vars[var + "'"] = setKey(c.all_ins_vars[var], "'", isbool=isinstance(typ, murphi.BooleanType),
                                         isdigit=isinstance(typ, murphi.ScalarSetType) or isinstance(typ,murphi.RngType),
                                         isenum=isinstance(typ, murphi.EnumType))
            all_ins_vars.append(var)
        elif "[_]" not in var:
            all_vars[var] = setKey(murphi.VarExpr(name=var,typ=specific_var[var]), "", isbool=isinstance(typ, murphi.BooleanType),
                                   isdigit=isinstance(typ, murphi.ScalarSetType) or isinstance(typ,murphi.RngType),
                                   isenum=isinstance(typ, murphi.EnumType))
            all_vars[var + "'"] = setKey(murphi.VarExpr(name=var,typ=specific_var[var]), "", isbool=isinstance(typ, murphi.BooleanType),
                                   isdigit=isinstance(typ, murphi.ScalarSetType) or isinstance(typ,murphi.RngType),
                                   isenum=isinstance(typ, murphi.EnumType))
            all_ins_vars.append(var)
            

    test_map = dict()

    test1 = dict()
    for const_var, const_values_typ in murphi.specific_var.items():
        downRng = 0
        upRng = 0
        sub_const_map = dict()
        if isinstance(const_values_typ, murphi.ScalarSetType):
            downRng = 1
            upRng = 1 + murphi.const_map[const_values_typ.const_name]
            for i in range(downRng,upRng):
                
                # subtyp = murphi.VarType(name=(key for key, val in murphi.digitType_map.items() if val == value))
                sub_const_map[str(i)] = murphi.VarExpr(name=str(i),typ=const_values_typ)
            const_pmurphi_map[str(const_var)] = sub_const_map
        elif isinstance(const_values_typ, murphi.RngType):
            if const_values_typ.downRng in murphi.const_map.keys():
                downRng = int(murphi.const_map[const_values_typ.downRng])
            else:
                downRng = int(const_values_typ.downRng)
            if const_values_typ.upRng in murphi.const_map.keys():
                upRng = 1 + int(murphi.const_map[const_values_typ.upRng])
            else:
                upRng = 1 + int(const_values_typ.upRng)
            for i in range(downRng,upRng):
                sub_const_map[str(i)] = murphi.VarExpr(name=str(i),typ=const_values_typ)
            const_pmurphi_map[str(const_var)] = sub_const_map
        
    
    start_alphabet = ord('A')
    for constType in murphi.const_map:
        paraAlpdict[str(constType)] = [chr(start_alphabet),chr(start_alphabet + 1)]
        start_alphabet = start_alphabet + 2



    for enum_name, enum_typ in c.enum_typ_map.items():
        for enum_typ_name in enum_typ.names:
            if enum_typ_name not in all_pmurphi.keys():
                all_pmurphi[enum_typ_name] = murphi.EnumValExpr(enum_typ, enum_typ_name)


    auxInv_dict = dict()
    get_ori_symm_invs = False

    firstCheck = True
    s_constructF = time.time()
    while (True):
        for name, instance in c.formula_instances.items():
            current_inv = instance["inv_name"]

            # 将所有的aux_inv都当成前提


            constructF = ConstructF(protocol_name, name, instance, protocol_path, current_inv, all_ori_invs,
                                    BooleanType_vars, c.enum_typ_map, c.typ_map, ScalarSetType_vars)


            if firstCheck:
                start_time = time.time()
                firstCheck = False
            #     all_ori_symm_invs = []
            #     for all_ori_inv in all_ori_invs:
            #         all_ori_symm_invs.extend(constructF.getallSymmetryInvs_1(copy.deepcopy(all_ori_inv)))
            #         # constructF.symmetry_statute(all_ori_inv, invPattern, invPattern_dict, [], [])
            #     constructF.ori_inv = all_ori_symm_invs


            new_inv_list, inv_name, all_invs_list = constructF.smtFormula()

            if len(new_inv_list) > 0:
                # all_ori_invs.extend(new_inv_list)
                all_ori_invs.extend(all_invs_list)
                # ori_inv[current_inv].extend(new_inv_list)
                ori_inv[current_inv].extend(all_invs_list)
                for i, new_inv in enumerate(new_inv_list):
                    auxInv_dict[inv_name + '_' + str(i + 1)] = new_inv
        if len(auxInv_dict) != 0:
            first_key = next(iter(auxInv_dict))
            search4new_auxInv(c, constructF, first_key, auxInv_dict[first_key])
            auxInv_dict.pop(first_key)
        else:
            break

    
    constructF.parainvsMerger()
    run_ivy(protocol_path + "_proved" + ".ivy")
    end_time = time.time()
    elapsed_time = end_time - start_time
    print(f"program runtime: {elapsed_time:.6f} s")
    print(f"The proved concrete inductive invariants saved to {protocol_name}_invs.txt\n")
    print(f"The corresponding parameterized inductive invariants saved to {protocol_name}_proved.ivy\n")
    # sys.stdout.close()
    # sys.stderr.close()



if __name__ == "__main__":
    protocol_name = sys.argv[1]
    protocol_path = f"protocols/{protocol_name}/{protocol_name}"
    Verification(protocol_path)