import sys
import murphi
from murphiparser import *
from murphi import *
import string
import re
from itertools import combinations
import copy
import itertools


# specific_var = {}

class GetSMTformula:
    def __init__(self,parse_name):
        self.parse_name = parse_name
        self.prot = parse_file(parse_name+".m")
        self.rule_para = dict()
        self.rule_var_map = dict()
        self.inv_para = dict()
        self.inv_var_map = dict()
        self.inv_array_var_map = dict()
        self.inv_var_length = dict()
        self.inv_var_ins = dict()
        self.inv_instance = dict()
        self.rule_var_ins = dict()
        self.rule_instance = dict()
        self.ins_var = None
        self.ins_var4rule = list()
        self.ins_var_dict = dict()
        self.formula_instances = dict()

        self.deduction = dict()

        self.arrayVar_insLength = dict()

        self.enum_typ_map = self.prot.enum_typ_map

        self.typ_map = self.prot.typ_map

        # self.data_permutations = list()

        self.all_ins_vars = dict()



    def join_statements(self,statement):
        if len(statement) == 1:
            return statement[0]
        else:
            # return (str(statement[-1]) + "& (" + self.join_statements(statement[:-1]) + ")")
            return murphi.OpExpr('&',statement[-1],self.join_statements(statement[:-1]))
        
    def disjoin_statements(self,statement):
        if len(statement) == 1:
            return statement[0]
        else:
            # return (str(statement[-1]) + "& (" + self.join_statements(statement[:-1]) + ")")
            return murphi.OpExpr('|',statement[-1],self.disjoin_statements(statement[:-1]))


    def mathOp2ins(self, mathOp, inv_var_ins, inv_var_map,var_typ):
        expr1_digit = False
        expr2_digit = False
        if isinstance(mathOp.expr1, murphi.OpExpr):
            self.mathOp2ins(mathOp.expr1, inv_var_ins, inv_var_map,var_typ)
        else:
            expr1_digit = True
            if str(mathOp.expr1).isdigit():
                pass
            else:
                if mathOp.expr1.name in inv_var_map.keys() and mathOp.expr1.name in inv_var_ins.keys():
                    var_typ = inv_var_map[mathOp.expr1.name]
                    mathOp.expr1.name = mathOp.expr1.name.replace(mathOp.expr1.name,
                                                                          str(inv_var_ins[mathOp.expr1.name]))

        if isinstance(mathOp.expr2, murphi.OpExpr):
            self.mathOp2ins(mathOp.expr2, inv_var_ins, inv_var_map,var_typ)
        else:
            expr2_digit = True
            if str(mathOp.expr2).isdigit():
                pass
            else:
                if mathOp.expr2.name in inv_var_map.keys() and mathOp.expr2.name in inv_var_ins.keys():
                    var_typ = inv_var_map[mathOp.expr2.name]
                    mathOp.expr2.name = mathOp.expr2.name.replace(mathOp.expr2.name,
                                                                          str(inv_var_ins[mathOp.expr2.name]))
        if expr1_digit and expr2_digit:
            mathOp = str(mathOp).replace('/','//')
            mathVal = eval(mathOp)
            murphi_idx = murphi.VarExpr(name=str(mathVal),typ=var_typ)
            return murphi_idx
        

    def defscalars(self):
        # pass
        # print(self.typ_map)
        # print(murphi.const_map)
        for type, const in self.typ_map.items():
            # print("type:",type)
            upRngF = False
            if isinstance(const, murphi.ScalarSetType):
                upRng = 1 + const_map[const.const_name]
                upRngF = True
            elif isinstance(const, murphi.RngType):
                upRngF = True
                if const.upRng in const_map.keys():
                    upRng = 1 + int(const_map[const.upRng])
                else:
                    upRng = 1 + int(const.upRng)
            if upRngF:
                # print("upRng:",upRng)
                self.arrayVar_insLength[str(type)] = upRng - 1        
        # print("1-self.arrayVar_insLength:",self.arrayVar_insLength)


    # Converting formulas from parameterized form to instantiated formulas
    def para2ins(self, OpExpr, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv=False):     
        if isinstance(OpExpr, murphi.ArrayIndex):
            # 多维数组
            if isinstance(OpExpr.v, FieldName):
                self.para2ins(OpExpr.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
            if isinstance(OpExpr.v, murphi.ArrayIndex):
                self.para2ins(OpExpr.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)

            # assert isinstance(OpExpr.idx, murphi.VarExpr)
            if isinstance(OpExpr.idx, murphi.VarExpr):
                if OpExpr.idx.name in inv_var_map.keys() and OpExpr.idx.name in inv_var_ins.keys():
                    OpExpr.idx.name = OpExpr.idx.name.replace(OpExpr.idx.name, str(inv_var_ins[OpExpr.idx.name]))
                # self.ins_var4rule = OpExpr.var
            if OpExpr not in self.ins_var4rule and str(OpExpr) in murphi.specific_var.keys():
                self.ins_var4rule.append(OpExpr)
            if OpExpr not in ins_var_list2 and str(OpExpr) in murphi.specific_var.keys():
                ins_var_list2.append(OpExpr)
            if forinv:
                self.ins_var = ins_var_list2

        elif isinstance(OpExpr, murphi.FieldName):
            if isinstance(OpExpr.v, FieldName):
                self.para2ins(OpExpr.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                
            if isinstance(OpExpr.v, murphi.ArrayIndex):
                if isinstance(OpExpr.v, ArrayIndex):
                    self.para2ins(OpExpr.v.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                elif isinstance(OpExpr.v.v, FieldName):
                    self.para2ins(OpExpr.v.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                
                if isinstance(OpExpr.v.idx, murphi.OpExpr):
                    OpExpr.v.idx = self.mathOp2ins(OpExpr.v.idx, inv_var_ins, inv_var_map, None)
                # assert isinstance(OpExpr.expr1.v.idx, murphi.VarExpr)
                elif isinstance(OpExpr.v.idx, murphi.VarExpr):
                    if OpExpr.v.idx.name in inv_var_map.keys() and OpExpr.v.idx.name in inv_var_ins.keys():
                        OpExpr.v.idx.name = OpExpr.v.idx.name.replace(OpExpr.v.idx.name,
                                                                        str(inv_var_ins[OpExpr.v.idx.name]))
            if OpExpr not in self.ins_var4rule and str(OpExpr) in murphi.specific_var.keys():
                self.ins_var4rule.append(OpExpr)
            if OpExpr not in ins_var_list2 and str(OpExpr) in murphi.specific_var.keys():
                ins_var_list2.append(OpExpr)
            if forinv:
                self.ins_var = ins_var_list2

        elif isinstance(OpExpr, murphi.AssignCmd):
            if isinstance(OpExpr.expr, murphi.FieldName):
                if isinstance(OpExpr.expr.v, FieldName):
                    self.para2ins(OpExpr.expr.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                
                if isinstance(OpExpr.expr.v, murphi.ArrayIndex):
                    if isinstance(OpExpr.expr.v.v, ArrayIndex):
                        self.para2ins(OpExpr.expr.v.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                    elif isinstance(OpExpr.expr.v.v, FieldName):
                        self.para2ins(OpExpr.expr.v.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                    
                    if isinstance(OpExpr.expr.v.idx, murphi.OpExpr):
                        OpExpr.expr.v.idx = self.mathOp2ins(OpExpr.expr.v.idx, inv_var_ins, inv_var_map, None)
                    # assert isinstance(OpExpr.expr.v.idx, murphi.VarExpr)
                    elif isinstance(OpExpr.expr.v.idx, murphi.VarExpr):
                        if OpExpr.expr.v.idx.name in inv_var_map.keys() and OpExpr.expr.v.idx.name in inv_var_ins.keys():
                            OpExpr.expr.v.idx.name = OpExpr.expr.v.idx.name.replace(OpExpr.expr.v.idx.name,
                                                                                str(inv_var_ins[OpExpr.expr.v.idx.name]))

                if OpExpr.expr not in ins_var_list2 and str(OpExpr.expr) in murphi.specific_var.keys():
                    ins_var_list2.append(OpExpr.expr)

            elif isinstance(OpExpr.expr, murphi.VarExpr):
                if OpExpr.expr.name in inv_var_map.keys() and OpExpr.expr.name in inv_var_ins.keys():
                    OpExpr.expr.name = OpExpr.expr.name.replace(OpExpr.expr.name,
                                                                      str(inv_var_ins[OpExpr.expr.name]))

                    if OpExpr.expr not in ins_var_list2 and not str(OpExpr.expr).isdigit() and str(OpExpr.expr) in murphi.specific_var.keys():
                        ins_var_list2.append(OpExpr.expr)

            elif isinstance(OpExpr.expr, murphi.ArrayIndex):
                # 多维数组
                if isinstance(OpExpr.expr.v, FieldName):
                    self.para2ins(OpExpr.expr.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                if isinstance(OpExpr.expr.v, murphi.ArrayIndex):
                    self.para2ins(OpExpr.expr.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)

                assert isinstance(OpExpr.expr.idx, murphi.VarExpr)
                if OpExpr.expr.idx.name in inv_var_map.keys() and OpExpr.expr.idx.name in inv_var_ins.keys():
                    OpExpr.expr.idx.name = OpExpr.expr.idx.name.replace(OpExpr.expr.idx.name,
                                                                      str(inv_var_ins[OpExpr.expr.idx.name]))
                    if OpExpr.expr not in ins_var_list2 and str(OpExpr.expr) in murphi.specific_var.keys():
                        ins_var_list2.append(OpExpr.expr)

            elif isinstance(OpExpr.expr, murphi.OpExpr):
                mathpattern = r'[-+*/%]'
                logicpattern = r'[!&|=->]'
                if re.search(mathpattern, str(OpExpr.expr)) is not None and re.search(logicpattern, str(OpExpr.expr)) is None:
                    OpExpr.expr = self.mathOp2ins(OpExpr.expr,inv_var_ins, inv_var_map, None)
                else:
                    self.para2ins(OpExpr.expr, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                # self.para2ins(OpExpr.expr, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)

            if isinstance(OpExpr.var, murphi.ArrayIndex):
                # 多维数组
                if isinstance(OpExpr.var.v, FieldName):
                    self.para2ins(OpExpr.var.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                if isinstance(OpExpr.var.v, murphi.ArrayIndex):
                    self.para2ins(OpExpr.var.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)

                assert isinstance(OpExpr.var.idx, murphi.VarExpr)

                if OpExpr.var.idx.name in inv_var_map.keys() and OpExpr.var.idx.name in inv_var_ins.keys():
                    OpExpr.var.idx.name = OpExpr.var.idx.name.replace(OpExpr.var.idx.name, str(inv_var_ins[OpExpr.var.idx.name]))
                    # self.ins_var4rule = OpExpr.var
                    if OpExpr.var not in self.ins_var4rule and str(OpExpr.var) in murphi.specific_var.keys():
                        self.ins_var4rule.append(OpExpr.var)
                    if OpExpr.var not in ins_var_list2 and str(OpExpr.var) in murphi.specific_var.keys():
                        ins_var_list2.append(OpExpr.var)

            elif isinstance(OpExpr.var, murphi.FieldName):
                if isinstance(OpExpr.var.v, FieldName):
                    self.para2ins(OpExpr.var.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                                
                if isinstance(OpExpr.var.v, murphi.ArrayIndex):
                    if isinstance(OpExpr.var.v.v, ArrayIndex):
                        self.para2ins(OpExpr.var.v.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                    elif isinstance(OpExpr.var.v.v, FieldName):
                        self.para2ins(OpExpr.var.v.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                                        
                    if isinstance(OpExpr.var.v.idx, murphi.OpExpr):
                        OpExpr.var.v.idx = self.mathOp2ins(OpExpr.var.v.idx, inv_var_ins, inv_var_map, None)
                    # assert isinstance(OpExpr.var.v.idx, murphi.VarExpr)
                    elif isinstance(OpExpr.var.v.idx, murphi.VarExpr):
                        if OpExpr.var.v.idx.name in inv_var_map.keys() and OpExpr.var.v.idx.name in inv_var_ins.keys():
                            OpExpr.var.v.idx.name = OpExpr.var.v.idx.name.replace(OpExpr.var.v.idx.name,
                                                                            str(inv_var_ins[OpExpr.var.v.idx.name]))
                        # self.ins_var4rule = OpExpr.var
                if OpExpr.var not in self.ins_var4rule and str(OpExpr.var) in murphi.specific_var.keys():
                    self.ins_var4rule.append(OpExpr.var)
                if OpExpr.var not in ins_var_list2 and str(OpExpr.var) in murphi.specific_var.keys():
                    ins_var_list2.append(OpExpr.var)
            elif isinstance(OpExpr.var, murphi.VarExpr):
                # self.ins_var4rule = OpExpr.var
                if OpExpr.var not in self.ins_var4rule and not str(OpExpr.var).isdigit() and str(OpExpr.var) in murphi.specific_var.keys():
                    self.ins_var4rule.append(OpExpr.var)
                if OpExpr.var not in ins_var_list2 and not str(OpExpr.var).isdigit() and str(OpExpr.var) in murphi.specific_var.keys():
                    ins_var_list2.append(OpExpr.var)

            elif isinstance(OpExpr.var, murphi.OpExpr):
                self.para2ins(OpExpr.var, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)

        elif isinstance(OpExpr, murphi.ForallCmd):
            # if OpExpr.typ in inv_var_map.values():
            expandingExpr = []
            var_length = self.arrayVar_insLength[str(OpExpr.typ)]
            for i in range(1, var_length + 1):
                ep_dp = copy.deepcopy(OpExpr.cmds)
                ins_dict_ep = copy.deepcopy(inv_var_ins)
                var_map_ep = copy.deepcopy(inv_var_map)
                ins_dict_ep[str(OpExpr.var)] = i
                var_map_ep[str(OpExpr.var)] = OpExpr.typ
                for sub_ep in ep_dp:
                    ins_ep = self.para2ins(sub_ep, ins_dict_ep, var_map_ep, ins_var_list2, inv_allVars_map, forinv)
                    # expandingExpr.append(ins_ep)
                    if isinstance(ins_ep, list):
                        expandingExpr.extend(ins_ep)
                    else:
                        expandingExpr.append(ins_ep)
            OpExpr = expandingExpr
        
        elif isinstance(OpExpr, murphi.ExistsExpr):
            # print("ExistsExpr")
            # print("self.arrayVar_insLength:",self.arrayVar_insLength)
            expandingExpr = []
            var_length = self.arrayVar_insLength[str(OpExpr.typ)]
            for i in range(1,var_length+1):
                ep2_dp = copy.deepcopy(OpExpr.expr)
                ins_dict_ep2 = copy.deepcopy(inv_var_ins)
                var_map_ep2 = copy.deepcopy(inv_var_map)
                ins_dict_ep2[str(OpExpr.var)] = i
                var_map_ep2[str(OpExpr.var)] = OpExpr.typ
                ins_ep2 = self.para2ins(ep2_dp, ins_dict_ep2, var_map_ep2, ins_var_list2, inv_allVars_map, forinv)
                # expandingExpr.append(ins_ep2)
                if isinstance(ins_ep2, list):
                    expandingExpr.extend(ins_ep2)
                else:
                    expandingExpr.append(ins_ep2)
                # print("expandingExpr:",expandingExpr)
            disjoin_statements = self.disjoin_statements(expandingExpr)

            OpExpr = disjoin_statements
            # print(OpExpr)

        elif isinstance(OpExpr, murphi.ForallExpr):
            # if OpExpr.typ in inv_var_map.values():
            
            expandingExpr = []
            var_length = self.arrayVar_insLength[str(OpExpr.typ)]
            for i in range(1,var_length+1):
                ep2_dp = copy.deepcopy(OpExpr.expr)
                ins_dict_ep2 = copy.deepcopy(inv_var_ins)
                var_map_ep2 = copy.deepcopy(inv_var_map)
                ins_dict_ep2[str(OpExpr.var)] = i
                var_map_ep2[str(OpExpr.var)] = OpExpr.typ
                ins_ep2 = self.para2ins(ep2_dp, ins_dict_ep2, var_map_ep2, ins_var_list2, inv_allVars_map, forinv)
                # expandingExpr.append(ins_ep2)
                if isinstance(ins_ep2, list):
                    expandingExpr.extend(ins_ep2)
                else:
                    expandingExpr.append(ins_ep2)
            join_statements = self.join_statements(expandingExpr)

            OpExpr = join_statements


        elif isinstance(OpExpr, murphi.OpExpr):
            if isinstance(OpExpr.expr1, murphi.OpExpr):
                self.para2ins(OpExpr.expr1, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
            elif isinstance(OpExpr.expr1, murphi.NegExpr):
                OpExpr.expr1.expr = self.para2ins(OpExpr.expr1.expr, inv_var_ins, inv_var_map, ins_var_list2, inv_allVars_map, forinv)
            elif isinstance(OpExpr.expr1, murphi.ArrayIndex):
                # 多维数组
                if isinstance(OpExpr.expr1.v, FieldName):
                    self.para2ins(OpExpr.expr1.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                if isinstance(OpExpr.expr1.v, murphi.ArrayIndex):
                    self.para2ins(OpExpr.expr1.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)

                # assert isinstance(OpExpr.expr1.idx, murphi.VarExpr)
                if isinstance(OpExpr.expr1.idx, murphi.VarExpr):
                    if OpExpr.expr1.idx.name in inv_var_map.keys() and OpExpr.expr1.idx.name in inv_var_ins.keys():
                        OpExpr.expr1.idx.name = OpExpr.expr1.idx.name.replace(OpExpr.expr1.idx.name,
                                                                        str(inv_var_ins[OpExpr.expr1.idx.name]))
                if OpExpr.expr1 not in ins_var_list2 and str(OpExpr.expr1) in murphi.specific_var.keys():
                    ins_var_list2.append(OpExpr.expr1)
                if forinv:
                    self.ins_var = ins_var_list2
            elif isinstance(OpExpr.expr1, murphi.VarExpr):
                if OpExpr.expr1.name in inv_var_map.keys() and OpExpr.expr1.name in inv_var_ins.keys():
                    OpExpr.expr1.name = OpExpr.expr1.name.replace(OpExpr.expr1.name, str(inv_var_ins[OpExpr.expr1.name]))
                elif OpExpr.expr1.name in inv_allVars_map.keys():
                    if OpExpr.expr1 not in ins_var_list2 and not str(OpExpr.expr1).isdigit() and str(OpExpr.expr1) in murphi.specific_var.keys():
                        ins_var_list2.append(OpExpr.expr1)
                    if forinv:
                        self.ins_var = ins_var_list2
            elif isinstance(OpExpr.expr1, murphi.FieldName):
                if isinstance(OpExpr.expr1.v, FieldName):
                    self.para2ins(OpExpr.expr1.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                
                if isinstance(OpExpr.expr1.v, murphi.ArrayIndex):
                    if isinstance(OpExpr.expr1.v.v, ArrayIndex):
                        self.para2ins(OpExpr.expr1.v.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                    elif isinstance(OpExpr.expr1.v.v, FieldName):
                        self.para2ins(OpExpr.expr1.v.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                    
                    if isinstance(OpExpr.expr1.v.idx, murphi.OpExpr):
                        OpExpr.expr1.v.idx = self.mathOp2ins(OpExpr.expr1.v.idx, inv_var_ins, inv_var_map, None)
                    # assert isinstance(OpExpr.expr1.v.idx, murphi.VarExpr)
                    elif isinstance(OpExpr.expr1.v.idx, murphi.VarExpr):
                        if OpExpr.expr1.v.idx.name in inv_var_map.keys() and OpExpr.expr1.v.idx.name in inv_var_ins.keys():
                            OpExpr.expr1.v.idx.name = OpExpr.expr1.v.idx.name.replace(OpExpr.expr1.v.idx.name,
                                                                            str(inv_var_ins[OpExpr.expr1.v.idx.name]))
                if OpExpr.expr1 not in ins_var_list2 and str(OpExpr.expr1) in murphi.specific_var.keys():
                    ins_var_list2.append(OpExpr.expr1)
                if forinv:
                    self.ins_var = ins_var_list2
            elif isinstance(OpExpr.expr1, murphi.ForallExpr):
                # if OpExpr.expr1.typ in inv_var_map.values():
                expandingExpr = []
                var_length = self.arrayVar_insLength[str(OpExpr.expr1.typ)]
                for i in range(1, var_length + 1):
                    ep1_dp = copy.deepcopy(OpExpr.expr1.expr)
                    ins_dict_ep1 = copy.deepcopy(inv_var_ins)
                    var_map_ep1 = copy.deepcopy(inv_var_map)
                    ins_dict_ep1[str(OpExpr.expr1.var)] = i
                    var_map_ep1[str(OpExpr.expr1.var)] = OpExpr.expr1.typ
                    ins_ep1 = self.para2ins(ep1_dp, ins_dict_ep1, var_map_ep1, ins_var_list2, inv_allVars_map, forinv)
                    # expandingExpr.append(ins_ep1)
                    if isinstance(ins_ep1, list):
                        expandingExpr.extend(ins_ep1)
                    else:
                        expandingExpr.append(ins_ep1)
                join_statements = self.join_statements(expandingExpr)
                OpExpr.expr1 = join_statements
            elif isinstance(OpExpr.expr1, murphi.ExistsExpr):
                OpExpr.expr1 = self.para2ins(OpExpr.expr1, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
            else:
                pass

            if isinstance(OpExpr.expr2, murphi.OpExpr):
                mathpattern = r'[-+*/%]'
                logicpattern = r'[!&|=->]'
                if re.search(mathpattern, str(OpExpr.expr2)) is not None and re.search(logicpattern, str(OpExpr.expr2)) is None:
                    OpExpr.expr2 = self.mathOp2ins(OpExpr.expr2,inv_var_ins, inv_var_map, None)
                else:
                    self.para2ins(OpExpr.expr2, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
            elif isinstance(OpExpr.expr2, murphi.NegExpr):
                OpExpr.expr2.expr = self.para2ins(OpExpr.expr2.expr, inv_var_ins, inv_var_map, ins_var_list2, inv_allVars_map, forinv)
            elif isinstance(OpExpr.expr2, murphi.ArrayIndex):
                # 多维数组
                if isinstance(OpExpr.expr2.v, FieldName):
                    self.para2ins(OpExpr.expr2.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                if isinstance(OpExpr.expr2.v, murphi.ArrayIndex):
                    self.para2ins(OpExpr.expr2.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)

                # print(OpExpr.expr2, OpExpr.expr2.idx)
                # assert isinstance(OpExpr.expr1.idx, murphi.VarExpr)
                if isinstance(OpExpr.expr2.idx, murphi.VarExpr):
                    if OpExpr.expr2.idx.name in inv_var_map.keys() and OpExpr.expr2.idx.name in inv_var_ins.keys():
                        OpExpr.expr2.idx.name = OpExpr.expr2.idx.name.replace(OpExpr.expr2.idx.name,
                                                                        str(inv_var_ins[OpExpr.expr2.idx.name]))
                if OpExpr.expr2 not in ins_var_list2 and str(OpExpr.expr2) in murphi.specific_var.keys():
                    ins_var_list2.append(OpExpr.expr2)
                if forinv:
                    self.ins_var = ins_var_list2
            elif isinstance(OpExpr.expr2, murphi.VarExpr):
                # print("inv_var_ins:",inv_var_ins)
                if OpExpr.expr2.name in inv_var_map.keys() and OpExpr.expr2.name in inv_var_ins.keys():
                    OpExpr.expr2.name = OpExpr.expr2.name.replace(OpExpr.expr2.name, str(inv_var_ins[OpExpr.expr2.name]))
                elif OpExpr.expr2.name in inv_allVars_map.keys():
                    if OpExpr.expr2 not in ins_var_list2 and not str(OpExpr.expr2).isdigit() and str(OpExpr.expr2) in murphi.specific_var.keys():
                        ins_var_list2.append(OpExpr.expr2)
                    if forinv:
                        self.ins_var = ins_var_list2
            elif isinstance(OpExpr.expr2, murphi.FieldName):
                if isinstance(OpExpr.expr2.v, FieldName):
                    self.para2ins(OpExpr.expr2.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                             
                if isinstance(OpExpr.expr2.v, murphi.ArrayIndex):
                    if isinstance(OpExpr.expr2.v.v, ArrayIndex):
                        self.para2ins(OpExpr.expr2.v.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                    elif isinstance(OpExpr.expr2.v.v, FieldName):
                        self.para2ins(OpExpr.expr2.v.v, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
                    
                    if isinstance(OpExpr.expr2.v.idx, murphi.OpExpr):
                        OpExpr.expr2.v.idx = self.mathOp2ins(OpExpr.expr2.v.idx, inv_var_ins, inv_var_map, None)            
                    # assert isinstance(OpExpr.expr2.v.idx, murphi.VarExpr)
                    elif isinstance(OpExpr.expr2.v.idx, murphi.VarExpr):
                        if OpExpr.expr2.v.idx.name in inv_var_map.keys() and OpExpr.expr2.v.idx.name in inv_var_ins.keys():
                            OpExpr.expr2.v.idx.name = OpExpr.expr2.v.idx.name.replace(OpExpr.expr2.v.idx.name,
                                                                            str(inv_var_ins[OpExpr.expr2.v.idx.name]))
                if OpExpr.expr2 not in ins_var_list2 and str(OpExpr.expr2) in murphi.specific_var.keys():
                    ins_var_list2.append(OpExpr.expr2)
                if forinv:
                    self.ins_var = ins_var_list2
            elif isinstance(OpExpr.expr2, murphi.ForallExpr):
                # if OpExpr.expr2.typ in inv_var_map.values():
                expandingExpr = []
                var_length = self.arrayVar_insLength[str(OpExpr.expr2.typ)]
                for i in range(1,var_length+1):
                    ep2_dp = copy.deepcopy(OpExpr.expr2.expr)
                    ins_dict_ep2 = copy.deepcopy(inv_var_ins)
                    var_map_ep2 = copy.deepcopy(inv_var_map)
                    ins_dict_ep2[str(OpExpr.expr2.var)] = i
                    var_map_ep2[str(OpExpr.expr2.var)] = OpExpr.expr2.typ
                    ins_ep2 = self.para2ins(ep2_dp, ins_dict_ep2, var_map_ep2, ins_var_list2, inv_allVars_map, forinv)
                    # expandingExpr.append(ins_ep2)
                    if isinstance(ins_ep2, list):
                        expandingExpr.extend(ins_ep2)
                    else:
                        expandingExpr.append(ins_ep2)
                join_statements = self.join_statements(expandingExpr)
                OpExpr.expr2 = join_statements
            elif isinstance(OpExpr.expr2, murphi.ExistsExpr):
                OpExpr.expr2 = self.para2ins(OpExpr.expr2, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
            else:
                pass

        elif isinstance(OpExpr, IfCmd):
            self.para2ins(OpExpr.if_branches[0][0], inv_var_ins, inv_var_map, ins_var_list2, inv_allVars_map, forinv)
            for ifassign in OpExpr.if_branches[0][1]:
                self.para2ins(ifassign, inv_var_ins, inv_var_map, ins_var_list2, inv_allVars_map, forinv)
            if OpExpr.else_branch:
                for elseassign in OpExpr.else_branch:
                    self.para2ins(elseassign, inv_var_ins, inv_var_map, ins_var_list2, inv_allVars_map, forinv)

        elif isinstance(OpExpr, murphi.NegExpr):
            OpExpr.expr = self.para2ins(OpExpr.expr, inv_var_ins, inv_var_map,ins_var_list2,inv_allVars_map, forinv)
        else:
            pass

        return OpExpr


    def getRules(self):

        sub_rule_ins = dict()
        for name, rule in self.prot.rule_map.items():
            

            global permutation_type

            # print(name)
            sub_rule_dict = dict()
            # for var: name and type
            if isinstance(rule, murphi.MurphiRuleSet):
                sub_rule_dict["var"] = rule.var_map
                self.rule_var_map[name] = rule.var_map
                # for guard: OpExpr
                sub_rule_dict["guard"] = rule.rule.cond
                # for assignments
                sub_rule_dict["assign"] = rule.rule.cmds
            elif isinstance(rule, murphi.MurphiRule):
                # for guard: OpExpr
                sub_rule_dict["var"] = {}
                self.rule_var_map[name] = {}
                sub_rule_dict["guard"] = rule.cond
                # for assignments
                sub_rule_dict["assign"] = rule.cmds
            self.rule_para[name] = sub_rule_dict

            # for construct instantiated rule vars
            # m:不变式参数个数 的n:规则的参数个数 排列
            # print("self.inv_var_map:",self.inv_var_map, self.inv_var_length)
            inv_name=""

            sub_var_ins = dict()
            for inv in self.inv_var_length.keys():
                inv_name = inv
                # permutations = [(1,),(2,)]

                # 实例化

                for var,type in sub_rule_dict["var"].items():
                    assert isinstance(type, murphi.VarType)
                    if isinstance(self.typ_map[type.name], murphi.ScalarSetType):
                        downRng = 1
                        upRng = 1 + const_map[self.typ_map[str(type)].const_name]
                    elif isinstance(self.typ_map[type.name], murphi.RngType):
                        if self.typ_map[str(type)].downRng in const_map.keys():
                            downRng = int(const_map[self.typ_map[str(type)].downRng])
                        else:
                            downRng = int(self.typ_map[str(type)].downRng)
                        if self.typ_map[str(type)].upRng in const_map.keys():
                            upRng = 1 + int(const_map[self.typ_map[str(type)].upRng])
                        else:
                            upRng = 1 + int(self.typ_map[str(type)].upRng)

                    sub_var_ins[var] = [i for i in range(downRng, upRng)]
                    # var_maxConstNum = murphi.const_map[murphi.digitType_map[str(type)]]
                    # sub_var_ins[var] = [i for i in range(1, var_maxConstNum+1)]

                    # self.arrayVar_insLength[str(type)] = upRng - 1
            sub_rule_ins[name] = sub_var_ins
            self.rule_var_ins[inv_name] = sub_rule_ins

        # for inv:all rules
        for inv,rules in self.rule_var_ins.items():

            rule_vars_dict = dict()
            # for inv-one rule:instantiated rule vars
            for rule,rule_vars in rules.items():
                # print("rule:",rule)

                # for each var
                i = 1

                ins_permutations = list(itertools.product(*rule_vars.values()))
                ins_permutations = [{key: value for key, value in zip(rule_vars.keys(), combo)} for combo in ins_permutations]

                for ins_permutation in ins_permutations:
                    sub_rule_instance_dict = dict()
                    ins_var4rule_list = list()
                    instance_name = inv + "_" + rule + str(i)

                    ins_dict = ins_permutation
                    # for guard
                    guard_dp = copy.deepcopy(self.rule_para[rule]["guard"])
                    guard_var = []
                    sub_rule_instance_dict["guard"] = self.para2ins(guard_dp, ins_dict, self.rule_var_map[rule], guard_var, {})
                    for var in guard_var:
                        if str(var) not in self.all_ins_vars:
                            self.all_ins_vars[str(var)] = var

                    # for assignment
                    sub_assign_list = list()
                    for assignment in self.rule_para[rule]["assign"]:

                        assign_dp = copy.deepcopy(assignment)
                        self.ins_var4rule = list()
                        if isinstance(assignment, murphi.UndefineCmd):
                            pass
                        else:
                            subassignvars = []
                            assignCmds = self.para2ins(assign_dp, ins_dict, self.rule_var_map[rule], subassignvars, {})
                            for var in subassignvars:
                                if str(var) not in self.all_ins_vars:
                                    self.all_ins_vars[str(var)] = var

                            if isinstance(assignCmds, list):
                                sub_assign_list.extend(assignCmds)
                            else:
                                sub_assign_list.append(assignCmds)
                        if self.ins_var4rule:
                            ins_var4rule_list.extend(self.ins_var4rule)
                    assign_vars = ins_var4rule_list

                    # print("ins_var4rule_list:",ins_var4rule_list)

                    sub_rule_instance_dict["assign"] = sub_assign_list
                    sub_rule_instance_dict["assumption"] = [elem for elem in self.ins_var_dict[inv] if
                                                            elem not in ins_var4rule_list]
                    


                    sub_rule_instance_dict["!inv"] = murphi.NegExpr(self.inv_instance[inv])

                    sub_rule_instance_dict["inv"] = self.inv_instance[inv]

                    sub_rule_instance_dict["inv_name"] = inv

                    sub_rule_instance_dict["rule_name"] = rule


                    # self.formula_instances[instance_name] = sub_rule_instance_dict
                    # using invHoldForRule2 from paraverifier
                    if self.invHoldForRule2(assign_vars, self.ins_var_dict[inv]):
                        self.formula_instances[instance_name] = sub_rule_instance_dict
                    else:
 
                        self.deduction[instance_name] = sub_rule_instance_dict

                    i += 1




        # 打开文件并写入内容
        # with open(self.parse_name+'_formula.txt', 'w') as file:
        #     file.write("\n\n")
        #     file.write("All parameterized rules:\n")
        #     file.write(str(self.rule_para))
        #     file.write("\n\n")
        #     file.write("All parameterized invariants:\n")
        #     file.write(str(self.inv_para))
        #     file.write("\n\n")
        #     file.write("All instantiated invariants:\n")
        #     file.write(str(self.inv_instance))
        #     file.write("\n\n")
        #     file.write("Invalid F:\n")
        #     file.write(str(self.deduction))
        #     file.write("\n\n")
        #     file.write("Valid F:\n")
        #     file.write(str(self.formula_instances))
        #     file.write("\n\n")

    def invHoldForRule2(self,assignVars,invVars):
        for invVar in invVars:
            for assignVar in assignVars:
                if invVar == assignVar:
                    return True
        return False


    def getInvVars(self, inv, inv_name, sub_var_dict, sub_inv_dict, sub_array_var):
        if isinstance(inv, murphi.ForallExpr):
            sub_var_dict[inv.var] = inv.typ
            sub_array_var[inv.var] = inv.typ
            # cp_inv_expr = copy.deepcopy(inv.expr)
            # print("cp_inv_expr:",cp_inv_expr)
            # inv = inv.expr
            if isinstance(inv.expr, murphi.ForallExpr):
                # inv.expr = cp_inv_expr.expr
                # print("inv.expr:",inv.expr)
                self.getInvVars(inv.expr, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
            else:
                self.getInvVars(inv.expr, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
                sub_inv_dict["invs"] = inv.expr
        elif isinstance(inv, murphi.VarExpr):
            sub_var_dict[inv.name] = inv.typ

        elif isinstance(inv, murphi.OpExpr):
            if isinstance(inv.expr1,murphi.ForallExpr) | isinstance(inv.expr2, murphi.ForallExpr):
                if isinstance(inv.expr1, murphi.ForallExpr):
                    _, half_inv,_ = self.getInvVars(inv.expr1, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
                    sub_inv_dict["invs"] = murphi.OpExpr(inv.op, half_inv["invs"], inv.expr2)
                elif isinstance(inv.expr1, murphi.OpExpr):
                    self.getInvVars(inv.expr1.expr1, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
                    self.getInvVars(inv.expr1.expr2, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
                if isinstance(inv.expr2, murphi.ForallExpr):
                    # print("2-forall:",inv.expr2)
                    _, half_inv,_ = self.getInvVars(inv.expr2, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
                    # print("after:",inv.expr2)
                    # print("half_inv:",half_inv)
                    sub_inv_dict["invs"] = murphi.OpExpr(inv.op, inv.expr1, half_inv["invs"])
                elif isinstance(inv.expr2, murphi.OpExpr):
                    self.getInvVars(inv.expr2.expr1, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
                    self.getInvVars(inv.expr2.expr2, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
            else:
                self.getInvVars(inv.expr1, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)
                self.getInvVars(inv.expr2, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)

            # sub_inv_dict["invs"] = inv

        elif isinstance(inv, murphi.NegExpr):
            self.getInvVars(inv.expr, inv_name, sub_var_dict, sub_inv_dict, sub_array_var)

        return sub_var_dict, sub_inv_dict, sub_array_var


    def getInvs(self):
        self.defscalars()
        inv_name = ""
        for inv in self.prot.inv_map.values():

            inv_name = inv.name

            assert isinstance(inv, MurphiInvariant)

            # for var: name and type
            sub_var_dict, sub_inv_dict, sub_array_var = self.getInvVars(inv.inv, inv_name, {}, {}, {})
            sub_inv_dict["var"] = sub_var_dict
            self.inv_var_map[inv_name] = sub_var_dict
            self.inv_array_var_map[inv_name] = sub_array_var
            self.inv_var_length[inv_name] = len(sub_var_dict)

            self.inv_para[inv_name] = sub_inv_dict



        # instances for parameters
            inv_insNum = {}
            # to fix: inv_insNum要改成一个dict，key是变量类型，存的是已经该变量类型已经实例化的最大值
            sub_insVar = dict()
            # 带参形式的实例化
            for var in sub_array_var.keys():
                if sub_array_var[var].name not in inv_insNum.keys():
                    # print("sub_array_var[var]:",sub_array_var[var],isinstance(self.typ_map[sub_array_var[var].name], murphi.ScalarSetType))
                    if isinstance(self.typ_map[sub_array_var[var].name], murphi.ScalarSetType):
                        inv_insNum[sub_array_var[var].name] = 1
                    elif isinstance(self.typ_map[sub_array_var[var].name], murphi.RngType):

                        if self.typ_map[sub_array_var[var].name].downRng in const_map.keys():
                            downRng = int(const_map[self.typ_map[sub_array_var[var].name].downRng])
                        else:
                            downRng = int(self.typ_map[sub_array_var[var].name].downRng)
                        inv_insNum[sub_array_var[var].name] = downRng
                else:
                    inv_insNum[sub_array_var[var].name] = inv_insNum[sub_array_var[var].name] + 1
                sub_insVar[var] = inv_insNum[sub_array_var[var].name]
            self.inv_var_ins[inv_name] = sub_insVar

            dp = copy.deepcopy(self.inv_para[inv_name]["invs"])
            # print("dp:",dp)
            # print("self.inv_var_map[inv_name]:",self.inv_var_map[inv_name])
            self.ins_var = None
            self.inv_instance[inv_name] = self.para2ins(dp, self.inv_var_ins[inv_name],self.inv_array_var_map[inv_name],[],self.inv_var_map[inv_name],True)


            if not self.ins_var==None:
                ins_var = copy.deepcopy(self.ins_var)
                if ins_var:
                    for var in ins_var:
                        if str(var) not in self.all_ins_vars.keys():
                            self.all_ins_vars[str(var)] = var
                self.ins_var_dict[inv_name] = ins_var

            # print("self.inv_instance[inv_name]:",inv_name,self.inv_instance[inv_name])
            self.getRules()

if __name__ == "__main__":
    # parse_name = "../protocols/mutualEx/mutualEx"
    # parse_name = "../protocols/mutdata/mutdata"
    parse_name = "protocols/german/german"
    # parse_name = "protocols/test/testFlash"
    # parse_name = "protocols/decentralized_lock/decentralized_lock"
    # parse_name = "protocols/godsont/godsont"
    # parse_name = "protocols/M_mutualEx/mutualEx_M2"
    # with open(parse_name + ".m", "r") as file:
    #     print(file.read())
    # parse_name = "../protocols/german_withoutData/german_withoutData"
    # GetSMTformula(parse_name=parse_name).getRules()
    smv_prot = parse_file(parse_name + ".m", smvSelect=True)
    silence_smvprot = str(smv_prot)
    # print("spev:")
    # print(murphi.specific_var)
    # print(str(smv_prot))
    # print("digitmap:", murphi.digitType_map)
    GetSMTformula(parse_name=parse_name).getInvs()



