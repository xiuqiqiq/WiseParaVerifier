import re
import random
import string
import copy
import lark
from collections import defaultdict


# from constructSMT import

from itertools import product




def indent(s, num_space, first_line=None):
    lines = s.split('\n')
    if first_line is None:
        return '\n'.join(' ' * num_space + line for line in lines)
    else:
        res = ' ' * first_line + lines[0]
        if len(lines) > 1:
            res += '\n' + '\n'.join(' ' * num_space + line for line in lines[1:])
        return res

ivySelect = ""
smvSelect = False

# record_map = dict()
# record_vars_map = dict()



const_map = dict()
digitType_map = dict()
re_digitType_map = dict()
SMVObj = None
specific_typ = {}
specific_var = {}
specific_enum_var = {}
class toSMV:
    def __init__(self, typ_map, vars, rules, start_state):
        global const_map
        self.const_map = const_map
        self.typ_map = typ_map
        self.var_map = vars
        self.rule_map = rules
        self.insVars = dict()
        self.ruleInsVars = dict()
        self.start_state = start_state
        self.rule_statements = ""

        self.paraVasIns = dict()

    def form_act(self, form, insmap = {}):
        if isinstance(form, BooleanExpr):
            return str(form).upper()
        elif isinstance(form, EnumValExpr):
            return form.enum_val
        elif str(form) in insmap.keys():
            return insmap[str(form)]
        else:
            # print("else:",form,type(form))
            return form

    def init_statement_act(self, var, expr, cond = None, is_init = False):
        if is_init:
            return f"init({var}) := case\nTRUE : {expr};\nesac;\n"
        else:
            return f"next({var}) := case\n{cond} : {expr};\nTRUE : {var};\nesac;"

    def rule_statement_act(self, var, exprs):
        assign_lines = ""
        for expr in exprs:
            # print("expr[0]:",expr[0],type(expr[0]))
            assign_lines += f"({self.rule_var_act(expr[1])}) : {self.rule_var_act(expr[0])};\n"

        return f"next({var}) := case\n{assign_lines}TRUE : {var};\nesac;"


    def new_cmd_act(self, cmd, assign_vars, ins_map):
        if isinstance(cmd, AssignCmd):
            assign_vars.append([str(cmd.var), self.form_act(cmd.expr, ins_map)])
        elif isinstance(cmd, ForallCmd):
            # print("forall:\n")
            assert isinstance(cmd.var_decl, MurphiVarDecl)
            key_value_pair = str(cmd.var_decl).split(':')
            # paraverifier中的init模块也只是给了一个值，初始值应该不影响
            ins_map[key_value_pair[0].strip()] = key_value_pair[1].strip()[1]
            for line in cmd.cmds:
                if isinstance(line, ForallCmd):
                    self.new_cmd_act(line, assign_vars, ins_map)
                else:
                    assert isinstance(line,AssignCmd)
                    pattern = re.sub(r'\[.*?\]', '[_]', str(line.var))
                    if pattern in self.paraVasIns.keys():
                        for ins in self.paraVasIns[pattern]:
                            assign_vars.append([ins, self.form_act(line.expr, ins_map)])
                    else:
                        assign_vars.append([str(line.var), self.form_act(line.expr, ins_map)])
        # print("assign_vars:",assign_vars)
        return assign_vars

    # 涉及 smv 部分的 init 没有改
    def init_act(self):
        init_statements = ""
        init_vars = []
        if isinstance(self.start_state, MurphiRuleSet):
            self.start_state = self.start_state.rule
        if isinstance(self.start_state, StartState):
            for start_state in self.start_state.cmds:
                init_vars.extend(self.new_cmd_act(start_state, [], {}))
                # init_vars.extend(self.cmd_act(start_state,{}, []))
            # print("new_init_vars:", new_init_vars)
            # print("init_vars:",init_vars)
            # init_vars: [['n[1]', 'i'], ['n[2]', 'i'], ['n[3]', 'i'], ['x', 'TRUE']]
            for init_var in init_vars:
                # print("init_var[0], init_var[1]:",init_var[0], init_var[1])
                init_statements += self.init_statement_act(init_var[0], init_var[1], is_init=True)
        # get all vars for cmds
        return init_statements

    def paraVar_insConstruct(self, pattern, insVarlist):
        pattern = re.sub(r'\[.*?\]', '[_]', pattern)
        for insVar in insVarlist:
            if pattern in self.paraVasIns.keys():
                if insVar not in self.paraVasIns[pattern]:
                    self.paraVasIns[pattern].append(insVar)
            else:
                self.paraVasIns[pattern] = [insVar]

    def type_ins_act(self, var, typ):
        global specific_var
        if isinstance(typ, BooleanType):
            specific_var[str(var)] = typ
            specific_var[re.sub(r'\[.*?\]', '[_]', str(var))] = typ
            return "%s : boolean;\n" % var
        elif isinstance(typ, ArrayType) or isinstance(self.typ_map[str(typ)], ArrayType):
            return self.type_act(var, typ)
        elif isinstance(self.typ_map[str(typ)], RecordType):
            res = ""
            for typ_del in self.typ_map[str(typ)].typ_decls:
                assert isinstance(typ_del, MurphiTypeDecl)
                name = var + f".{typ_del.name}"
                self.paraVar_insConstruct(name, [name])
                res += self.type_ins_act(name, typ_del.typ)
            return res
        elif isinstance(self.typ_map[str(typ)], EnumType):
            specific_var[str(var)] = self.typ_map[str(typ)]
            specific_enum_var[str(var)] = str(typ)
            specific_var[re.sub(r'\[.*?\]', '[_]', str(var))] = self.typ_map[str(typ)]
            return "%s : {%s}" % (var, ', '.join(name for name in self.typ_map[str(typ)].names)) + ";\n"
        elif isinstance(self.typ_map[str(typ)], ScalarSetType):
            specific_var[str(var)] = self.typ_map[str(typ)]
            specific_var[re.sub(r'\[.*?\]', '[_]', str(var))] = self.typ_map[str(typ)]
            res = "%s : {" % var
            for i in range(1, 1 + const_map[self.typ_map[str(typ)].const_name]):
                res += str(i) + ", "
            res = res[:-2] + "};\n"
            return res
        elif isinstance(self.typ_map[str(typ)], RngType):
            specific_var[str(var)] = self.typ_map[str(typ)]
            specific_var[re.sub(r'\[.*?\]', '[_]', str(var))] = self.typ_map[str(typ)]
            if self.typ_map[str(typ)].downRng in const_map.keys():
                downRng = const_map[self.typ_map[str(typ)].downRng]
            else:
                downRng = self.typ_map[str(typ)].downRng

            if self.typ_map[str(typ)].upRng in const_map.keys():
                upRng = const_map[self.typ_map[str(typ)].upRng]
            else:
                upRng = self.typ_map[str(typ)].upRng

            res = "%s : {" % var
            for i in range(int(downRng), 1 + int(upRng)):
                res += str(i) + ", "
            res = res[:-2] + "};\n"
            return res
        else:
            print("not cover-type:",var, typ)
        return ""

    def type_act(self, varName, typ):
        res = ""
        assert isinstance(typ, ArrayType) or isinstance(self.typ_map[str(typ)], ArrayType)
        if str(typ) in self.typ_map.keys() and isinstance(self.typ_map[str(typ)], ArrayType):
            typ = self.typ_map[str(typ)]
        insVar = []

        downRng = 0
        upRng = 0
        rngflag = False

        if isinstance(self.typ_map[typ.idx_typ.name], RngType):
                 
            rngflag = True
            if self.typ_map[str(typ.idx_typ.name)].downRng in const_map.keys():
                downRng = int(const_map[self.typ_map[str(typ.idx_typ.name)].downRng])
            else:
                downRng = int(self.typ_map[str(typ.idx_typ.name)].downRng)

            if self.typ_map[str(typ.idx_typ.name)].upRng in const_map.keys():
                upRng = int(const_map[self.typ_map[str(typ.idx_typ.name)].upRng]) + 1
            else:
                upRng = int(self.typ_map[str(typ.idx_typ.name)].upRng) + 1
            # downRng = int(self.typ_map[typ.idx_typ.name].downRng)
            # upRng = self.const_map[self.typ_map[typ.idx_typ.name].upRng]+1
        elif isinstance(self.typ_map[typ.idx_typ.name], ScalarSetType):
            downRng = 1
            upRng = self.const_map[self.typ_map[typ.idx_typ.name].const_name] + 1
        insvar_list = []
        for i in range(downRng, upRng):
            insVar.append(varName + '[' + str(i) + ']')
            name = varName + '[' + str(i) + ']'
            res += self.type_ins_act(name, typ.ele_typ)
            if name not in insvar_list:
                insvar_list.append(name)
        # print("res:",res)
        
                

        if insvar_list:
            if isinstance(typ.ele_typ, ArrayType):
                # print("typ.ele_typ:",typ.ele_typ)
                if isinstance(typ.ele_typ.ele_typ, BooleanType) or not isinstance(self.typ_map[typ.ele_typ.ele_typ.name], RecordType):
                    self.paraVar_insConstruct(insvar_list[0], insvar_list)
                # print("arrtype:",typ)
                # print("arrtype.ele_typ:",typ.ele_typ)
                # print("arrtype.ele_typ.ele_typ:",typ.ele_typ.ele_typ)
                # print(str(typ.ele_typ.ele_typ) in self.typ_map.keys())
                # print("insvar_list[0]:",insvar_list[0])
            elif isinstance(typ.ele_typ, BooleanType) or not isinstance(self.typ_map[typ.ele_typ.name], RecordType):
                self.paraVar_insConstruct(insvar_list[0], insvar_list)

        self.insVars[typ.idx_typ.name] = insVar
        return res

    def getFixedRuleVars(self, rule):
        def getOpVars(fomula, vars):
            # print("op:",fomula)
            global specific_var
            if isinstance(fomula, OpExpr):
                getOpVars(fomula.expr1, vars)
                getOpVars(fomula.expr2, vars)
            elif isinstance(fomula, NegExpr):
                getOpVars(fomula.expr, vars)
            elif str(fomula) in specific_var.keys() and not("[" in str(fomula)) and str(fomula) not in vars:
            # elif not("[" in str(fomula)) and not(isinstance(fomula, EnumValExpr) or isinstance(fomula, BooleanExpr)) and str(fomula) not in vars:
                vars.append(str(fomula))
            return vars

        def getAssignVars(assign, assign_vars):
            if isinstance(assign, AssignCmd):
                global specific_var
                if str(assign.var) in specific_var.keys() and not ("[" in str(assign.var)) and str(assign.var) not in vars:
                # if not("[" in str(assign.var) and "]" in str(assign.var)) and not(isinstance(assign.var, EnumValExpr) or isinstance(assign.var, BooleanExpr)) and str(assign.var) not in assign_vars:
                    assign_vars.append(str(assign.var))
                if str(assign.expr) in specific_var.keys() and not ("[" in str(assign.expr)) and str(assign.expr) not in vars:
                # if not("[" in str(assign.expr) and "]" in str(assign.expr)) and not(isinstance(assign.expr, EnumValExpr) or isinstance(assign.expr, BooleanExpr)) and str(assign.expr) not in assign_vars:
                    assign_vars.append(str(assign.expr))

            elif isinstance(assign, IfCmd):
                # print("assign.if_branches[0][0]:",assign.if_branches[0][0])
                getOpVars(assign.if_branches[0][0], assign_vars)
                for ifassign in assign.if_branches[0][1]:
                    getAssignVars(ifassign, assign_vars)
                if assign.else_branch:
                    for elseassign in assign.else_branch:
                        getAssignVars(elseassign, assign_vars)

            elif isinstance(assign, OpExpr):
                getOpVars(assign, assign_vars)
            return assign_vars

        vars = []
        assert isinstance(rule, MurphiRule)

        guardVars = getOpVars(rule.cond, [])

        if guardVars:
            vars.extend(guardVars)
        for assign in rule.cmds:
            if isinstance(assign, ForallCmd):
                for cmd in assign.cmds:
                    getAssignVars(cmd, vars)
            else:
                getAssignVars(assign, vars)
        return vars

    def traverse_dict_combinations(self, ins_dict, keys=None, current_combination=None, result_list=None):
        if keys is None:
            keys = list(ins_dict.keys())

        if current_combination is None:
            current_combination = {}

        if result_list is None:
            result_list = []

        if not keys:
            # 当没有剩余的键时，将当前组合添加到结果字典中
            result_list.append(copy.deepcopy(current_combination))
            # result_list[len(result_list) + 1] = copy.deepcopy(current_combination)
            return

        current_key = keys[0]
        remaining_keys = keys[1:]

        for value in ins_dict[current_key]:
            current_combination[current_key] = value
            self.traverse_dict_combinations(ins_dict, remaining_keys, current_combination, result_list)
            del current_combination[current_key]

    def join_statements(self,statement):
        if len(statement) == 1:
            return statement[0]
        else:
            return OpExpr('&',statement[-1],self.join_statements(statement[:-1]))


    def getRng(self,type):
        assert isinstance(type, VarType)
        if isinstance(self.typ_map[type.name], ScalarSetType):
            downRng = 1
            upRng = 1 + const_map[self.typ_map[str(type)].const_name]
        elif isinstance(self.typ_map[type.name], RngType):
            if self.typ_map[str(type)].downRng in const_map.keys():
                downRng = int(const_map[self.typ_map[str(type)].downRng])
            else:
                downRng = int(self.typ_map[str(type)].downRng)
            if self.typ_map[str(type)].upRng in const_map.keys():
                upRng = 1 + int(const_map[self.typ_map[str(type)].upRng])
            else:
                upRng = 1 + int(self.typ_map[str(type)].upRng)
        return downRng,upRng




    def para2ins(self, Expr, ins_var_type, ins_var_map, var_list):
        global specific_var
        # print("specific_var:",specific_var)
        if isinstance(Expr, ArrayIndex):
            if isinstance(Expr.v, FieldName):
                self.para2ins(Expr.v, ins_var_type, ins_var_map, var_list)
            if isinstance(Expr.v, ArrayIndex):
                self.para2ins(Expr.v, ins_var_type, ins_var_map, var_list)

            # assert isinstance(Expr.idx, VarExpr)
            if isinstance(Expr.idx, VarExpr):
                if Expr.idx.name in ins_var_map.keys() and ins_var_type[Expr.idx.name] == str(
                        Expr.idx.typ):
                    Expr.idx.name = Expr.idx.name.replace(Expr.idx.name,
                                                                        str(ins_var_map[Expr.idx.name]))
            if str(Expr) in specific_var.keys() and str(Expr) not in var_list:
                var_list.append(str(Expr))

        if isinstance(Expr, AssignCmd):
            if isinstance(Expr.expr, ArrayIndex):
                # multi-demansion
                if isinstance(Expr.expr.v, ArrayIndex):
                    self.para2ins(Expr.expr.v, ins_var_type, ins_var_map, var_list)
                if isinstance(Expr.expr.v, FieldName):
                    self.para2ins(Expr.expr.v, ins_var_type, ins_var_map, var_list)

                assert isinstance(Expr.expr.idx, VarExpr)
                if Expr.expr.idx.name in ins_var_map.keys() and ins_var_type[Expr.expr.idx.name] == str(
                        Expr.expr.idx.typ):
                    Expr.expr.idx.name = Expr.expr.idx.name.replace(Expr.expr.idx.name,
                                                                      str(ins_var_map[Expr.expr.idx.name]))
                if str(Expr.expr) in specific_var.keys() and str(Expr.expr) not in var_list:
                    var_list.append(str(Expr.expr))
            elif isinstance(Expr.expr, FieldName):
                if isinstance(Expr.expr.v, FieldName):
                    self.para2ins(Expr.expr.v, ins_var_type, ins_var_map, var_list)
                if isinstance(Expr.expr.v, ArrayIndex):
                    if isinstance(Expr.expr.v.v, ArrayIndex):
                        self.para2ins(Expr.expr.v.v, ins_var_type, ins_var_map, var_list)
                    if isinstance(Expr.expr.v.v, FieldName):
                        self.para2ins(Expr.expr.v.v, ins_var_type, ins_var_map, var_list)
                    
                    # assert isinstance(Expr.expr.v.idx, VarExpr)
                    if isinstance(Expr.expr.v.idx, VarExpr):
                        if Expr.expr.v.idx.name in ins_var_map.keys() and ins_var_type[Expr.expr.v.idx.name] == str(
                                Expr.expr.v.idx.typ):
                            Expr.expr.v.idx.name = Expr.expr.v.idx.name.replace(Expr.expr.v.idx.name,
                                                                                str(ins_var_map[Expr.expr.v.idx.name]))
                if str(Expr.expr) in specific_var.keys() and "[" in str(Expr.expr) and "]" in str(Expr.expr) and str(Expr.expr) not in var_list:
                    var_list.append(str(Expr.expr))
            elif isinstance(Expr.expr, VarExpr):
                if Expr.expr.name in ins_var_map.keys() and ins_var_type[Expr.expr.name] == str(Expr.expr.typ):
                    Expr.expr.name = Expr.expr.name.replace(Expr.expr.name,
                                                                      str(ins_var_map[Expr.expr.name]))
            elif isinstance(Expr.expr, OpExpr):
                self.para2ins(Expr.expr, ins_var_type, ins_var_map, var_list)
            else:
                pass

            if isinstance(Expr.var, ArrayIndex):
                # multi-demansion
                if isinstance(Expr.var.v, ArrayIndex):
                    self.para2ins(Expr.var.v, ins_var_type, ins_var_map, var_list)
                if isinstance(Expr.var.v, FieldName):
                    self.para2ins(Expr.var.v, ins_var_type, ins_var_map, var_list)

                assert isinstance(Expr.var.idx, VarExpr)
                if Expr.var.idx.name in ins_var_map.keys() and ins_var_type[Expr.var.idx.name] == str(
                        Expr.var.idx.typ):
                    Expr.var.idx.name = Expr.var.idx.name.replace(Expr.var.idx.name,
                                                                      str(ins_var_map[Expr.var.idx.name]))
                if str(Expr.var) in specific_var.keys() and str(Expr.var) not in var_list:
                    var_list.append(str(Expr.var))
            elif isinstance(Expr.var, FieldName):
                if isinstance(Expr.var.v, FieldName):
                    self.para2ins(Expr.var.v, ins_var_type, ins_var_map, var_list)
                if isinstance(Expr.var.v, ArrayIndex):
                    if isinstance(Expr.var.v.v, ArrayIndex):
                        self.para2ins(Expr.var.v.v, ins_var_type, ins_var_map, var_list)
                    if isinstance(Expr.var.v.v, FieldName):
                        self.para2ins(Expr.var.v.v, ins_var_type, ins_var_map, var_list)
                    
                    # assert isinstance(Expr.var.v.idx, VarExpr)
                    if isinstance(Expr.var.v.idx, VarExpr):
                        if Expr.var.v.idx.name in ins_var_map.keys() and ins_var_type[Expr.var.v.idx.name] == str(
                                Expr.var.v.idx.typ):
                            Expr.var.v.idx.name = Expr.var.v.idx.name.replace(Expr.var.v.idx.name,
                                                                                str(ins_var_map[Expr.var.v.idx.name]))

                if "[" in str(Expr.var) and "]" in str(Expr.var) and str(Expr.var) in specific_var.keys() and str(Expr.var) not in var_list:
                    var_list.append(str(Expr.var))
            elif isinstance(Expr.var, VarExpr):
                if Expr.var.name in ins_var_map.keys() and ins_var_type[Expr.var.name] == str(Expr.var.typ):
                    Expr.var.name = Expr.var.name.replace(Expr.var.name,
                                                                      str(ins_var_map[Expr.var.name]))
            elif isinstance(Expr.var, OpExpr):
                self.para2ins(Expr.var, ins_var_type, ins_var_map, var_list)
            else:
                pass

        elif isinstance(Expr, ForallCmd):
            expandingExpr = []
            downRng,upRng = self.getRng(Expr.typ)
            for i in range(downRng, upRng):
                ep_dp = copy.deepcopy(Expr.cmds)
                ins_var_map_ep = copy.deepcopy(ins_var_map)
                ins_var_type_ep = copy.deepcopy(ins_var_type)
                ins_var_map_ep[str(Expr.var)] = i
                ins_var_type_ep[str(Expr.var)] = str(Expr.typ)
                for ep in ep_dp:
                    ins_ep = self.para2ins(ep, ins_var_type_ep, ins_var_map_ep, var_list)
                    # expandingExpr.append(ins_ep)
                    if isinstance(ins_ep, list):
                        expandingExpr.extend(ins_ep)
                    else:
                        expandingExpr.append(ins_ep)
            Expr = expandingExpr


        elif isinstance(Expr, ForallExpr):
            expandingExpr = []
            downRng,upRng = self.getRng(Expr.typ)
            for i in range(downRng, upRng):
                ep_dp = copy.deepcopy(Expr.expr)
                ins_var_map_ep = copy.deepcopy(ins_var_map)
                ins_var_type_ep = copy.deepcopy(ins_var_type)
                ins_var_map_ep[str(Expr.var)] = i
                ins_var_type_ep[str(Expr.var)] = str(Expr.typ)
                ins_ep = self.para2ins(ep_dp, ins_var_type_ep, ins_var_map_ep, var_list)
                # expandingExpr.append(ins_ep)
                if isinstance(ins_ep, list):
                    expandingExpr.extend(ins_ep)
                else:
                    expandingExpr.append(ins_ep)
            join_statements = self.join_statements(expandingExpr)
            Expr = join_statements


        elif isinstance(Expr, OpExpr):
            if isinstance(Expr.expr1, OpExpr):
                self.para2ins(Expr.expr1, ins_var_type, ins_var_map, var_list)
            elif isinstance(Expr.expr1, NegExpr):
                Expr.expr1.expr = self.para2ins(Expr.expr1.expr, ins_var_type, ins_var_map, var_list)
            elif isinstance(Expr.expr1, ArrayIndex):
                # multi-demansion
                if isinstance(Expr.expr1.v, FieldName):
                    self.para2ins(Expr.expr1.v, ins_var_type, ins_var_map, var_list)
                if isinstance(Expr.expr1.v, ArrayIndex):
                    self.para2ins(Expr.expr1.v, ins_var_type, ins_var_map, var_list)
                
                # assert isinstance(Expr.expr1.idx, VarExpr)
                if isinstance(Expr.expr1.idx, VarExpr):
                    if Expr.expr1.idx.name in ins_var_map.keys() and ins_var_type[Expr.expr1.idx.name] == str(Expr.expr1.idx.typ):
                        Expr.expr1.idx.name = Expr.expr1.idx.name.replace(Expr.expr1.idx.name,
                                                                            str(ins_var_map[Expr.expr1.idx.name]))
                if str(Expr.expr1) in specific_var.keys() and str(Expr.expr1) not in var_list:
                    var_list.append(str(Expr.expr1))
            elif isinstance(Expr.expr1, FieldName):
                if isinstance(Expr.expr1.v, FieldName):
                    self.para2ins(Expr.expr1.v, ins_var_type, ins_var_map, var_list)
                if isinstance(Expr.expr1.v, ArrayIndex):
                    if isinstance(Expr.expr1.v.v, ArrayIndex):
                        self.para2ins(Expr.expr1.v.v, ins_var_type, ins_var_map, var_list)
                    if isinstance(Expr.expr1.v.v, FieldName):
                        self.para2ins(Expr.expr1.v.v, ins_var_type, ins_var_map, var_list)
                    
                    # assert isinstance(Expr.expr1.v.idx, VarExpr)
                    if isinstance(Expr.expr1.v.idx, VarExpr):
                        if Expr.expr1.v.idx.name in ins_var_map.keys() and ins_var_type[Expr.expr1.v.idx.name] ==str(Expr.expr1.v.idx.typ):
                            Expr.expr1.v.idx.name = Expr.expr1.v.idx.name.replace(Expr.expr1.v.idx.name,
                                                                                    str(ins_var_map[Expr.expr1.v.idx.name]))
                if "[" in str(Expr.expr1) and "]" in str(Expr.expr1) and str(Expr.expr1) in specific_var.keys() and str(Expr.expr1) not in var_list:
                    var_list.append(str(Expr.expr1))
            elif isinstance(Expr.expr1, ForallExpr):
                expandingExpr = []
                downRng,upRng = self.getRng(Expr.expr1.typ)
                for i in range(downRng, upRng):
                    ep_dp = copy.deepcopy(Expr.expr1.expr)
                    ins_var_map_ep = copy.deepcopy(ins_var_map)
                    ins_var_type_ep = copy.deepcopy(ins_var_type)
                    ins_var_map_ep[str(Expr.expr1.var)] = i
                    ins_var_type_ep[str(Expr.expr1.var)] = str(Expr.expr1.typ)
                    ins_ep = self.para2ins(ep_dp, ins_var_type_ep, ins_var_map_ep, var_list)
                    # expandingExpr.append(ins_ep)
                    if isinstance(ins_ep, list):
                        expandingExpr.extend(ins_ep)
                    else:
                        expandingExpr.append(ins_ep)
                join_statements = self.join_statements(expandingExpr)
                Expr.expr1 = join_statements
            elif isinstance(Expr.expr1, VarExpr):
                if Expr.expr1.name in ins_var_map.keys() and ins_var_type[Expr.expr1.name] == str(Expr.expr1.typ):
                    Expr.expr1.name = Expr.expr1.name.replace(Expr.expr1.name,
                                                                      str(ins_var_map[Expr.expr1.name]))
            else:pass

            if isinstance(Expr.expr2, OpExpr):
                self.para2ins(Expr.expr2, ins_var_type, ins_var_map, var_list)
            elif isinstance(Expr.expr2, NegExpr):
                Expr.expr2.expr = self.para2ins(Expr.expr2.expr, ins_var_type, ins_var_map, var_list)
            elif isinstance(Expr.expr2, ArrayIndex):
                # multi-demansion
                if isinstance(Expr.expr2.v, FieldName):
                    self.para2ins(Expr.expr2.v, ins_var_type, ins_var_map, var_list)
                if isinstance(Expr.expr2.v, ArrayIndex):
                    self.para2ins(Expr.expr2.v, ins_var_type, ins_var_map, var_list)

                assert isinstance(Expr.expr2.idx, VarExpr)
                if Expr.expr2.idx.name in ins_var_map.keys() and ins_var_type[Expr.expr2.idx.name] == str(Expr.expr2.idx.typ):
                    Expr.expr2.idx.name = Expr.expr2.idx.name.replace(Expr.expr2.idx.name,
                                                                          str(ins_var_map[Expr.expr2.idx.name]))
                if str(Expr.expr2) in specific_var.keys() and str(Expr.expr2) not in var_list:
                    var_list.append(str(Expr.expr2))
            elif isinstance(Expr.expr2, FieldName):
                if isinstance(Expr.expr2.v, FieldName):
                    self.para2ins(Expr.expr2.v, ins_var_type, ins_var_map, var_list)
                if isinstance(Expr.expr2.v, ArrayIndex):
                    if isinstance(Expr.expr2.v.v, ArrayIndex):
                        self.para2ins(Expr.expr2.v.v, ins_var_type, ins_var_map, var_list)
                    if isinstance(Expr.expr2.v.v, FieldName):
                        self.para2ins(Expr.expr2.v.v, ins_var_type, ins_var_map, var_list)
                    assert isinstance(Expr.expr2.v.idx, VarExpr)
                    if Expr.expr2.v.idx.name in ins_var_map.keys() and ins_var_type[Expr.expr2.v.idx.name] ==str(Expr.expr2.v.idx.typ):
                        Expr.expr2.v.idx.name = Expr.expr2.v.idx.name.replace(Expr.expr2.v.idx.name,
                                                                                  str(ins_var_map[Expr.expr2.v.idx.name]))
                if "[" in str(Expr.expr2) and "]" in str(Expr.expr2) and str(Expr.expr2) in specific_var.keys() and str(Expr.expr2) not in var_list:
                    var_list.append(str(Expr.expr2))
            elif isinstance(Expr.expr2, ForallExpr):
                # print("ForallExpr")
                # print(Expr.expr2)
                expandingExpr = []
                # var_length = const_map[self.typ_map[str(Expr.expr2.typ)].const_name]
                downRng,upRng = self.getRng(Expr.expr2.typ)
                for i in range(downRng,upRng):
                    ep_dp = copy.deepcopy(Expr.expr2.expr)
                    ins_var_map_ep = copy.deepcopy(ins_var_map)
                    ins_var_type_ep = copy.deepcopy(ins_var_type)
                    ins_var_map_ep[str(Expr.expr2.var)] = i
                    ins_var_type_ep[str(Expr.expr2.var)] = str(Expr.expr2.typ)
                    # print("ep_dp:", ep_dp)
                    # print("ins_var_map_ep:", ins_var_map_ep)
                    # print("ins_var_type_ep:", ins_var_type_ep)
                    ins_ep = self.para2ins(ep_dp, ins_var_type_ep, ins_var_map_ep, var_list)
                    # print("ins_ep:", ins_ep)
                    # expandingExpr.append(ins_ep)
                    if isinstance(ins_ep, list):
                        expandingExpr.extend(ins_ep)
                    else:
                        expandingExpr.append(ins_ep)
                join_statements = self.join_statements(expandingExpr)
                # print("expandingExpr:", expandingExpr)
                Expr.expr2 = join_statements
                # print("Expr:", Expr.expr2)
            elif isinstance(Expr.expr2, VarExpr):
                if Expr.expr2.name in ins_var_map.keys() and ins_var_type[Expr.expr2.name] == str(Expr.expr2.typ):
                    Expr.expr2.name = Expr.expr2.name.replace(Expr.expr2.name,
                                                                      str(ins_var_map[Expr.expr2.name]))
            else:
                pass

        elif isinstance(Expr, NegExpr):
            Expr.expr = self.para2ins(Expr.expr, ins_var_type, ins_var_map, var_list)

        elif isinstance(Expr, IfCmd):
            self.para2ins(Expr.if_branches[0][0], ins_var_type, ins_var_map, var_list)
            for ifassign in Expr.if_branches[0][1]:
                self.para2ins(ifassign, ins_var_type, ins_var_map, var_list)
            if Expr.else_branch:
                for elseassign in Expr.else_branch:
                    self.para2ins(elseassign, ins_var_type, ins_var_map, var_list)

        elif isinstance(Expr, FieldName):
            if isinstance(Expr.v, FieldName):
                self.para2ins(Expr.v, ins_var_type, ins_var_map, var_list)
            if isinstance(Expr.v, ArrayIndex):
                if isinstance(Expr.v.v, ArrayIndex):
                    self.para2ins(Expr.expr.v.v, ins_var_type, ins_var_map, var_list)
                if isinstance(Expr.v.v, FieldName):
                    self.para2ins(Expr.v.v, ins_var_type, ins_var_map, var_list)

                assert isinstance(Expr.v.idx, VarExpr)
                if Expr.v.idx.name in ins_var_map.keys() and ins_var_type[Expr.v.idx.name] == str(
                        Expr.v.idx.typ):
                    Expr.v.idx.name = Expr.v.idx.name.replace(Expr.v.idx.name,
                                                                          str(ins_var_map[Expr.v.idx.name]))
            if "[" in str(Expr) and "]" in str(Expr) and str(Expr) in specific_var.keys() and str(Expr) not in var_list:
                var_list.append(str(Expr))
        return Expr

    # simply fix struct if...else because there has no elif lines even for flash.m
    def if_else_act(self, ifblock, othercond, ifdict):
        assert isinstance(ifblock, IfCmd)
        ifcond = OpExpr('&', othercond, ifblock.if_branches[0][0])
        elsecond = OpExpr('&', othercond, NegExpr(ifblock.if_branches[0][0]))

        for ifassign in ifblock.if_branches[0][1]:
            assert isinstance(ifassign, AssignCmd)
            ifdict[self.rule_var_act(ifassign.var)].append([self.rule_var_act(ifassign.expr), ifcond])
        if ifblock.else_branch:
            for elseassign in ifblock.else_branch:
                assert isinstance(elseassign, AssignCmd)
                ifdict[self.rule_var_act(elseassign.var)].append([self.rule_var_act(elseassign.expr), elsecond])
        return ifdict

    def new_rule_act(self):

        def processDecl(name, var_strs):
            return f"n_{name} : process Proc__n_{name}({var_strs});" + "\n"

        def rule_proc(name, var_strs):
            return f"MODULE Proc__n_{name}({var_strs})\nASSIGN\n"

        ruleDecl = ""
        ruleStatements = ""
        for i, rule in enumerate(self.rule_map):
            # print(rule)
            rule_var_map = {}
            ins_var_type = {}
            fixed_vars = []
            specfic_rule = None
            if isinstance(self.rule_map[rule], MurphiRule):
                specfic_rule = self.rule_map[rule]

            elif isinstance(self.rule_map[rule], MurphiRuleSet):
                
                specfic_rule = self.rule_map[rule].rule
                for ins_var,typ in self.rule_map[rule].var_map.items():

                    if isinstance(self.typ_map[str(typ)], ScalarSetType):
                        downRng = 1
                        upRng = 1 + const_map[self.typ_map[str(typ)].const_name]
                    elif isinstance(self.typ_map[str(typ)], RngType):
                        if self.typ_map[str(typ)].downRng in const_map.keys():
                            downRng = int(const_map[self.typ_map[str(typ)].downRng])
                        else:
                            downRng = int(self.typ_map[str(typ)].downRng)
                        if self.typ_map[str(typ)].upRng in const_map.keys():
                            upRng = 1 + int(const_map[self.typ_map[str(typ)].upRng])
                        else:
                            upRng = 1 + int(self.typ_map[str(typ)].upRng)

                    ins_var_type[ins_var] = str(typ)
                    # rule_var_map[str(ins_var)] = list(range(0, 1 + const_map[self.typ_map[str(typ)].const_name]))
                    rule_var_map[str(ins_var)] = list(range(downRng, upRng))
                    # rule_var_map: {'d': [1, 2], 'i': [1, 2, 3]}

            fixed_vars = self.getFixedRuleVars(specfic_rule)


            all_ins_permutations = []
            self.traverse_dict_combinations(rule_var_map, result_list=all_ins_permutations)

            for permutation in all_ins_permutations:
                permutation_vars = []
                ruleStatements_vars = defaultdict(list)
                guard_dp = copy.deepcopy(specfic_rule.cond)
                cond = self.para2ins(guard_dp, ins_var_type, permutation, permutation_vars)
                # print("guard_dp:",guard_dp)
                # if guard_vars:
                #     permutation_vars.extend(guard_vars)
                assign_lines = []
                for cmd in specfic_rule.cmds:
                    assign_dp = copy.deepcopy(cmd)
                    assign_line = self.para2ins(assign_dp, ins_var_type, permutation, permutation_vars)
                    
                    # if cmd_vars:
                    #     permutation_vars.extend(cmd_vars)
                    if isinstance(assign_line, list):
                        assign_lines.extend(assign_line)
                    else:
                        assign_lines.append(assign_line)
                permutation_vars.extend(fixed_vars)


                # print("permutation:",permutation)
                permutation_vars = [s.strip("'") for s in permutation_vars]
                permutation_vars = ', '.join(permutation_vars)
                # print("permutation_vars:",permutation_vars)
                if permutation:
                    name = rule + '__' + '__'.join(map(str, permutation.values()))
                else:
                    name = rule
                # print(name)
                ruleDecl += processDecl(name, permutation_vars) + '\n'

                ruleVars = self.rule_var_act(permutation_vars)
                # print("ruleVars:",ruleVars)
                ruleStatements += rule_proc(name, ruleVars)

                # cond = self.rule_var_act(guard_dp)
                # cond = guard_dp
                for assign in assign_lines:
                    if isinstance(assign, IfCmd):
                        ruleStatements_vars = self.if_else_act(assign, cond, ruleStatements_vars)
                        # print("ruleStatements_vars:",ruleStatements_vars)
                        # print(assign.else_branch)
                    else:
                        var = self.rule_var_act(assign.var)
                        expr = self.rule_var_act(assign.expr)
                        ruleStatements_vars[var].append([expr, cond])
                        # ruleStatements += self.statement_act(var, expr, cond) + '\n'
                for var, expr in ruleStatements_vars.items():
                    # print(var)
                    # print(expr)
                    ruleStatements += self.rule_statement_act(var, expr) + '\n'
                ruleStatements += '\n---------\n\n'

            ruleStatements += "\n---------\n\n"

        return ruleDecl, ruleStatements

    def rule_var_act(self, var):
        return str(var).replace("[","__").replace("]","").replace(".","__")

    def rule_act(self):
        ruleDecl = ""
        ruleStatements = ""

        def processDecl(name, var_strs):
            return f"{name} : process Proc__{name}{var_strs};" + "\n"

        def rule_proc(name, var_strs):
            return f"MODULE Proc__{name}{var_strs}\nASSIGN\n"

        for i,rule in enumerate(self.rule_map):
            rule_vars = []
            rule_vars_map = {}

            assert isinstance(self.rule_map[rule], MurphiRuleSet)
            # print(self.rule_map[rule].var_map)
            for ins_var,typ in self.rule_map[rule].var_map.items():
                if str(typ) in self.insVars.keys():
                    rule_vars.append(self.insVars[str(typ)])
                    pattern = r'\[(.*?)\]'
                    match = re.search(pattern, self.insVars[str(typ)][0])
                    if match:
                        paraname = self.insVars[str(typ)][0].replace(match.group(1), ins_var)
                        # rule_vars_map[paraname] = self.insVars[str(typ)]
                        for vals in self.insVars[str(typ)]:
                            rule_vars_map[vals] = paraname



            fixed_vars = self.getFixedRuleVars(self.rule_map[rule])
            if fixed_vars:
                rule_vars.append(fixed_vars)
            # print(self.ruleInsVars[rule])
            # print("rule_vars:",rule_vars)
            combinations = list(product(*rule_vars))
            # print("combinations:",combinations)
            for j,comb in enumerate(combinations):
                # print("comb:",comb)
                name = ""
                var_strs = ""
                if len(comb) == 1:
                    name = comb[0].replace('[', '_' + rule + "__")
                    name = name.replace(']', '')
                    var_strs = "(" + comb[0] + ")"

                else:
                    for insVar in comb:
                        if insVar not in fixed_vars:
                            name += insVar.replace('[', '_' + rule + "__")
                            name = name.replace(']', '')
                    var_strs = str(comb).replace("'", "")
                ruleDecl += processDecl(name,var_strs) + "\n"


                var_paras = var_strs.replace('[', "__")
                var_paras = var_paras.replace(']', '')
                ruleStatements += rule_proc(name, var_paras)

                guard = str(self.rule_map[rule].rule.cond)
                initVars_map = {}
                for paras in comb:
                    if paras not in fixed_vars:
                        guard = guard.replace(rule_vars_map[paras], paras)
                        initVars_map[rule_vars_map[paras]] = paras
                guard = guard.replace('[', "__")
                guard = guard.replace(']', '')
                # print("rule_vars_map:",rule_vars_map)
                # print("guard:",guard)
                # print("initVars_map:",initVars_map)
                for cmd in self.rule_map[rule].rule.cmds:
                    # print("cmd:",cmd)
                    cmd_var = str(cmd.var)
                    for paravar, initvar in initVars_map.items():
                        cmd_var = cmd_var.replace(paravar, initvar)
                    cmd_var = cmd_var.replace('[', "__")
                    cmd_var = cmd_var.replace(']', '')
                    # print(self.statement_act(cmd_var, cmd.expr, guard))
                    ruleStatements += self.statement_act(cmd_var, cmd.expr, guard) + "\n"
                ruleStatements += "\n---------\n\n"

        # print("ruleStatements:\n",ruleStatements)

        return ruleDecl, ruleStatements


IVYObj = None



def check_ivy(string):
    match = re.search(r"ivy", string)
    if match:
        return True
    else:
        return False

def generate_random_letters(upper_or_lower):
    # letters = list(string.ascii_uppercase)
    # random_letters = random.sample(letters, n)
    if upper_or_lower == "upper":
        return random.choice(string.ascii_uppercase)
    if upper_or_lower == "lower":
        return random.choice(string.ascii_lowercase)

class toIVY:
    def __init__(self, type_map, var_map, start_state, rule_map, inv_map):
        self.type_map = type_map
        self.start_state = start_state
        self.rule_map = rule_map
        self.inv_map = inv_map
        self.specific_typ = dict()
        for type_name, typ in self.type_map.items():
            if not isinstance(typ, RecordType):
                self.specific_typ[type_name] = typ
            else:
                assert isinstance(typ, RecordType)
                for subitem in typ.typ_decls:
                    assert isinstance(subitem, MurphiTypeDecl)
                    self.specific_typ[type_name + "_" + subitem.name] = subitem.typ

        self.var_map = var_map
        self.specific_var_map = dict()
        self.record_map = defaultdict(list)

    def join_statements(self,statement):
        if len(statement) == 1:
            return statement[0]
        else:
            return OpExpr('&',statement[-1],self.join_statements(statement[:-1]))

    def type_act(self, name, typ):
        if isinstance(typ, ScalarSetType):
            return "%s" % name

        elif isinstance(typ, EnumType):
            enum_vars =  "{%s}" % (', '.join(v for v in typ.names))
            return f"{name} = {enum_vars}"

        elif isinstance(typ, UnionType):
            res = name + " = struct {\n"
            typ_list = list()
            for i in range(len(typ.typs) - 1):
                subtyp_name = name + "_" + typ.typs[i].name
                typ_list.append([typ.typs[i].name, subtyp_name])
                res += indent(subtyp_name, 2) + ":" + typ.typs[i].name + "," + "\n"
            subtyp_name = name + "_" + typ.typs[len(typ.typs) - 1].name
            typ_list.append([typ.typs[len(typ.typs) - 1].name, subtyp_name])
            global union_dict
            union_dict[name] = typ_list
            res += indent(subtyp_name, 2) + ":" + typ.typs[len(typ.typs) - 1].name + "\n" + "}"
            # print("union_dict:",union_dict)
            return res
        else:
            return "%s = %s" % (name, typ)

    def type_define(self):
        # print("self.type_map:",self.type_map)
        res = ""
        for name, typ in self.type_map.items():
            if isinstance(typ, RecordType):
                for typ_decl in typ.typ_decls:
                    self.record_map[name].append(typ_decl)
            else:
                res += "type " + self.type_act(name, typ) + "\n\n"
        return res

    def arrvardef(self,var_name, idx_typ, ele_typ):
        self.specific_var_map[var_name] = ele_typ
        return "individual %s(%s) : %s" % (var_name,random.choice(string.ascii_uppercase) + ":" + str(idx_typ), str(ele_typ))

    def var_act(self, var, typ):
        res = ""
        if isinstance(typ, ArrayType):
            if str(typ.ele_typ) not in self.record_map.keys():
                res += self.arrvardef(var, typ.idx_typ, typ.ele_typ)
            else:
                for sub_record_item in self.record_map[str(typ.ele_typ)]:
                    assert isinstance(sub_record_item, MurphiTypeDecl)
                    var_name = var + "_" + sub_record_item.name
                    res += self.arrvardef(var_name, typ.idx_typ, sub_record_item.typ) + "\n"
        elif str(typ) in self.record_map.keys():
            for sub_record_item in self.record_map[str(typ)]:
                assert isinstance(sub_record_item, MurphiTypeDecl)
                var_name = var + "_" + sub_record_item.name
                res += self.var_act(var_name, sub_record_item.typ)
        else:
            self.specific_var_map[str(var)] = typ
            res += "individual " + str(var) + " : " + str(typ)
        return res + "\n"

    def var_define(self):
        # print("specific_typ:",self.specific_typ)
        # print("self.record_map:", self.record_map)
        res = ""
        for var, typ in self.var_map.items():
            res += self.var_act(var, typ)
        # print("self.specific_var_map:",self.specific_var_map)
        return res

    def get_recordvar_idxtyp(self, field_var):
        arrtyp = None
        assert isinstance(field_var, FieldName)
        # print("v:",field_var.v, type(field_var.v))
        # print("f:",field_var.field, type(field_var.field))
        if isinstance(field_var.v, ArrayIndex):
            arrtyp = field_var.v.idx
        elif isinstance(field_var.v, FieldName):
            arrtyp = self.get_recordvar_idxtyp(field_var.v)
        return arrtyp

    def field_var_act(self, field_var):
        assert isinstance(field_var, FieldName)
        if isinstance(field_var.v, ArrayIndex):
            if not isinstance(field_var.v.v, FieldName):
                record_name = str(field_var.v.v) + "_" + str(field_var.field)
                record_typ = self.specific_var_map[record_name]
                sub_record_var = VarExpr(record_name, record_typ)
                field_var = ArrayIndex(sub_record_var, field_var.v.idx)
            else:
                assert isinstance(field_var.v.v, FieldName)
                record_name = str(field_var.v.v.v) + "_" + str(field_var.v.v.field) + "_" + str(field_var.field)
                record_typ = self.specific_var_map[record_name]
                sub_record_var = VarExpr(record_name, record_typ)
                field_var = ArrayIndex(sub_record_var, field_var.v.idx)
        else:
            record_name = str(field_var.v) + "_" + str(field_var.field)
            record_typ = self.specific_var_map[record_name]
            field_var = VarExpr(record_name, record_typ)
        return field_var

    def new_field_var_act(self, field_var):
        # print(str(field_var))
        isarr = '(' in str(field_var)
        if isarr == False:
            record_name = str(field_var).replace('.','_')
            record_typ = self.specific_var_map[record_name]
            field_var = VarExpr(record_name, record_typ)
        else:
            record_name = re.sub(r'\(.*?\)', '', str(field_var))
            record_name = record_name.replace('.', '_')
            record_typ = self.specific_var_map[record_name]
            idx_typ = self.get_recordvar_idxtyp(field_var)
            sub_record_var = VarExpr(record_name, record_typ)
            field_var = ArrayIndex(sub_record_var, idx_typ)
        return field_var

    def para2ins(self, Expr, ins_var_type, ins_var_map, forall_table = [], digitmap = {}):
        if isinstance(Expr, ArrayIndex):
            # 多维数组
            if isinstance(Expr.v, FieldName):
                self.para2ins(Expr.v, ins_var_type, ins_var_map, forall_table)
            if isinstance(Expr.v, ArrayIndex):
                self.para2ins(Expr.v, ins_var_type, ins_var_map, forall_table)

            # assert isinstance(OpExpr.idx, VarExpr)
            if isinstance(Expr.idx, VarExpr):
                if Expr.idx.name in ins_var_map.keys() and ins_var_type[Expr.idx.name] == str(Expr.idx.typ):
                    Expr.idx.name = Expr.idx.name.replace(Expr.idx.name, str(ins_var_map[Expr.idx.name]))
      
        
        if isinstance(Expr, AssignCmd):
            if isinstance(Expr.expr, ArrayIndex):
                assert isinstance(Expr.expr.idx, VarExpr)
                if Expr.expr.idx.name in ins_var_map.keys() and ins_var_type[Expr.expr.idx.name] == str(
                        Expr.expr.idx.typ):
                    Expr.expr.idx.name = Expr.expr.idx.name.replace(Expr.expr.idx.name,
                                                                      str(ins_var_map[Expr.expr.idx.name]))
            elif isinstance(Expr.expr, FieldName):
                if isinstance(Expr.expr.v, ArrayIndex):
                    assert isinstance(Expr.expr.v.idx, VarExpr)
                    if Expr.expr.v.idx.name in ins_var_map.keys() and ins_var_type[Expr.expr.v.idx.name] == str(
                            Expr.expr.v.idx.typ):
                        Expr.expr.v.idx.name = Expr.expr.v.idx.name.replace(Expr.expr.v.idx.name,
                                                                              str(ins_var_map[Expr.expr.v.idx.name]))
                Expr.expr = self.new_field_var_act(Expr.expr)
            elif isinstance(Expr.expr, VarExpr):
                if Expr.expr.name in ins_var_map.keys() and ins_var_type[Expr.expr.name] == str(Expr.expr.typ):
                    Expr.expr.name = Expr.expr.name.replace(Expr.expr.name,
                                                                      str(ins_var_map[Expr.expr.name]))
            else:
                pass

            if isinstance(Expr.var, ArrayIndex):
                assert isinstance(Expr.var.idx, VarExpr)
                if Expr.var.idx.name in ins_var_map.keys() and ins_var_type[Expr.var.idx.name] == str(
                        Expr.var.idx.typ):
                    Expr.var.idx.name = Expr.var.idx.name.replace(Expr.var.idx.name,
                                                                      str(ins_var_map[Expr.var.idx.name]))

            elif isinstance(Expr.var, FieldName):
                if isinstance(Expr.var.v, ArrayIndex):
                    assert isinstance(Expr.var.v.idx, VarExpr)
                    if Expr.var.v.idx.name in ins_var_map.keys() and ins_var_type[Expr.var.v.idx.name] == str(
                            Expr.var.v.idx.typ):
                        Expr.var.v.idx.name = Expr.var.v.idx.name.replace(Expr.var.v.idx.name,
                                                                              str(ins_var_map[Expr.var.v.idx.name]))

                    # print("Expr.var.v:",Expr.var.v.v, type(Expr.var.v.v))
                    # print(Expr.var.v.idx)
                    # print(Expr.var.field)
                    # record_name = str(Expr.var.v.v) + "_" + str(Expr.var.field)
                    # record_typ = self.specific_var_map[record_name]
                    # sub_record_var = VarExpr(record_name, record_typ)
                    # print(ArrayIndex(sub_record_var, Expr.var.v.idx))
                Expr.var = self.new_field_var_act(Expr.var)
            elif isinstance(Expr.var, VarExpr):
                if Expr.var.name in ins_var_map.keys() and ins_var_type[Expr.var.name] == str(Expr.var.typ):
                    Expr.var.name = Expr.var.name.replace(Expr.var.name,
                                                                      str(ins_var_map[Expr.var.name]))
            else:
                pass

        elif isinstance(Expr, OpExpr):
            if isinstance(Expr.expr1, OpExpr):
                self.para2ins(Expr.expr1, ins_var_type, ins_var_map, forall_table)
            elif isinstance(Expr.expr1, NegExpr):
                self.para2ins(Expr.expr1.expr, ins_var_type, ins_var_map, forall_table)
            elif isinstance(Expr.expr1, ArrayIndex):
                # 多维数组
                if isinstance(Expr.expr1.v, FieldName):
                    self.para2ins(Expr.expr1.v, ins_var_type, ins_var_map, forall_table)
                if isinstance(Expr.expr1.v, ArrayIndex):
                    self.para2ins(Expr.expr1.v, ins_var_type, ins_var_map, forall_table)

                assert isinstance(Expr.expr1.idx, VarExpr)
                if Expr.expr1.idx.name in ins_var_map.keys() and ins_var_type[Expr.expr1.idx.name] == str(Expr.expr1.idx.typ):
                    Expr.expr1.idx.name = Expr.expr1.idx.name.replace(Expr.expr1.idx.name,
                                                                          str(ins_var_map[Expr.expr1.idx.name]))
            elif isinstance(Expr.expr1, FieldName):
                if isinstance(Expr.expr1.v, ArrayIndex):
                    assert isinstance(Expr.expr1.v.idx, VarExpr)
                    if Expr.expr1.v.idx.name in ins_var_map.keys() and ins_var_type[Expr.expr1.v.idx.name] ==str(Expr.expr1.v.idx.typ):
                        Expr.expr1.v.idx.name = Expr.expr1.v.idx.name.replace(Expr.expr1.v.idx.name,
                                                                                  str(ins_var_map[Expr.expr1.v.idx.name]))
                Expr.expr1 = self.new_field_var_act(Expr.expr1)
            elif isinstance(Expr.expr1, ForallExpr):
                placeholder = chr(ord('A') + len(forall_table))
                forall_table.append(placeholder)
                ins_var_map[str(Expr.expr1.var)] = placeholder
                ins_var_type[str(Expr.expr1.var)] = str(Expr.expr1.typ)
                ins_ep = self.para2ins(Expr.expr1.expr, ins_var_type, ins_var_map, forall_table)
                Expr.expr1 = ins_ep
                # for cmd in Expr.expr1.expr:
                #     ins_ep = self.para2ins(cmd, ins_var_type, ins_var_map)
                #     expandingExpr.append(ins_ep)
                # join_statements = self.join_statements(expandingExpr)
                # Expr.expr1 = join_statements
            elif isinstance(Expr.expr1, VarExpr):
                if Expr.expr1.name in ins_var_map.keys() and ins_var_type[Expr.expr1.name] == str(Expr.expr1.typ):
                    Expr.expr1.name = Expr.expr1.name.replace(Expr.expr1.name,
                                                                      str(ins_var_map[Expr.expr1.name]))
            else:pass

            if isinstance(Expr.expr2, OpExpr):
                self.para2ins(Expr.expr2, ins_var_type, ins_var_map, forall_table)
            elif isinstance(Expr.expr2, NegExpr):
                self.para2ins(Expr.expr2.expr, ins_var_type, ins_var_map, forall_table)
            elif isinstance(Expr.expr2, ArrayIndex):
                if isinstance(Expr.expr2.v, FieldName):
                    self.para2ins(Expr.expr2.v, ins_var_type, ins_var_map, forall_table)
                if isinstance(Expr.expr2.v, ArrayIndex):
                    self.para2ins(Expr.expr2.v, ins_var_type, ins_var_map, forall_table)


                assert isinstance(Expr.expr2.idx, VarExpr)
                if Expr.expr2.idx.name in ins_var_map.keys() and ins_var_type[Expr.expr2.idx.name] == str(Expr.expr2.idx.typ):
                    Expr.expr2.idx.name = Expr.expr2.idx.name.replace(Expr.expr2.idx.name,
                                                                          str(ins_var_map[Expr.expr2.idx.name]))
            elif isinstance(Expr.expr2, FieldName):
                if isinstance(Expr.expr2.v, ArrayIndex):
                    assert isinstance(Expr.expr2.v.idx, VarExpr)
                    if Expr.expr2.v.idx.name in ins_var_map.keys() and ins_var_type[Expr.expr2.v.idx.name] ==str(Expr.expr2.v.idx.typ):
                        Expr.expr2.v.idx.name = Expr.expr2.v.idx.name.replace(Expr.expr2.v.idx.name,
                                                                                  str(ins_var_map[Expr.expr2.v.idx.name]))
                Expr.expr2 = self.new_field_var_act(Expr.expr2)
            elif isinstance(Expr.expr2, ForallExpr):
                placeholder = chr(ord('A') + len(forall_table))
                forall_table.append(placeholder)
                ins_var_map[str(Expr.expr2.var)] = placeholder
                ins_var_type[str(Expr.expr2.var)] = str(Expr.expr2.typ)
                ins_ep = self.para2ins(Expr.expr2.expr, ins_var_type, ins_var_map, forall_table)
                Expr.expr2 = ins_ep
                # for cmd in Expr.expr2.expr:
                #     ins_ep = self.para2ins(cmd, ins_var_type, ins_var_map)
                #     expandingExpr.append(ins_ep)
                # join_statements = self.join_statements(expandingExpr)
                # Expr.expr2 = join_statements
            elif isinstance(Expr.expr2, VarExpr):
                if Expr.expr2.name in ins_var_map.keys() and ins_var_type[Expr.expr2.name] == str(Expr.expr2.typ):
                    Expr.expr2.name = Expr.expr2.name.replace(Expr.expr2.name,
                                                                      str(ins_var_map[Expr.expr2.name]))
            else:
                pass

        elif isinstance(Expr, NegExpr):
            self.para2ins(Expr.expr, ins_var_type, ins_var_map, forall_table)

        elif isinstance(Expr, ForallCmd):
            placeholder = chr(ord('A') + len(forall_table))
            forall_table.append(placeholder)
            expandingExpr = []
            ins_var_map[str(Expr.var)] = placeholder
            ins_var_type[str(Expr.var)] = str(Expr.typ)
            for cmd in Expr.cmds:
                ins_ep = self.para2ins(cmd, ins_var_type, ins_var_map, forall_table)
                expandingExpr.append(ins_ep)
            return expandingExpr

        elif isinstance(Expr, ForallExpr):
            placeholder = chr(ord('A') + len(forall_table))
            forall_table.append(placeholder)
            ins_var_map[str(Expr.var)] = placeholder
            ins_var_type[str(Expr.var)] = str(Expr.typ)
            ins_ep = self.para2ins(Expr.expr, ins_var_type, ins_var_map, forall_table)
            Expr = ins_ep

        elif isinstance(Expr, IfCmd):
            self.para2ins(Expr.if_branches[0][0], ins_var_type, ins_var_map, forall_table)
            for ifassign in Expr.if_branches[0][1]:
                self.para2ins(ifassign, ins_var_type, ins_var_map, forall_table)
            if Expr.else_branch:
                for elseassign in Expr.else_branch:
                    self.para2ins(elseassign, ins_var_type, ins_var_map, forall_table)

        return Expr


    def forall_act(self, forall_cmd, init_forall_table):
        res = ""
        assert isinstance(forall_cmd, ForallCmd)
        placeholder = chr(ord('A') + len(init_forall_table))
        if placeholder not in init_forall_table:
            init_forall_table.append(placeholder)
        ins_var_map = {}
        ins_var_type = {}
        ins_var_map[str(forall_cmd.var)] = placeholder
        ins_var_type[str(forall_cmd.var)] = str(forall_cmd.typ)
        for cmd in forall_cmd.cmds:
            init_lines = self.para2ins(cmd, ins_var_type, ins_var_map, init_forall_table)
            if isinstance(init_lines, list):
                for init_line in init_lines:
                    res += "require " + str(init_line).replace('.','_').replace(':','') + "\n"
            else:
                res += "require " + str(init_lines).replace('.','_').replace(':','') + "\n"
            # res
        return res


    def init_act(self):
        init_forall_table = []
        res = "after init{\n"
        for cmd in self.start_state.cmds:
            if isinstance(cmd, ForallCmd):
                res += indent(f"{self.forall_act(cmd, init_forall_table)}", 4)
            else:
                # print("else:")
                # print(cmd)
                res += "require " + str(cmd).replace(':','') + "\n"
                # print("require " + str(cmd).replace(':',''))
        res += "}\n"
        return res


    def rule_act(self):
        res = ""
        # print("rule-map:",self.rule_map)
        export_names = []
        for rname, rule in self.rule_map.items():
            export_names.append(str(rname).lower())
            res += f"action {str(rname).lower()} = " + "{\n"
            rule_lines = None
            if isinstance(rule, MurphiRuleSet):
                local_vars = ', '.join([f"{key}: {value}" for key, value in rule.var_map.items()])
                res += indent(f"local {local_vars} " + "{\n", 4)
                assert isinstance(rule.rule, MurphiRule)
                rule_lines = rule.rule
            elif isinstance(rule, MurphiRule):
                rule_lines = rule

            res += f"require {self.para2ins(rule_lines.cond,{},{},[])};\n"
            # print(rule.rule.cmds)
            for cmd in rule_lines.cmds:
                assign = self.para2ins(cmd,{},{},[])
                if not isinstance(assign, list):
                    res += indent(str(assign),4)
                else:
                    for sub_assign in assign:
                        res += indent(str(sub_assign),4)
            if isinstance(rule, MurphiRuleSet):
                res += "}\n"
            res += "}\n\n\n\n"
        for export_name in export_names:
            res += f"export {export_name}\n"
        return res


    def inv_act(self):
        res = ""
        for _,inv in self.inv_map.items():
            assert isinstance(inv, MurphiInvariant)
            # print("inv:")
            # print(inv)
            res += f"conjecture {self.para2ins(inv.inv,{},{},[])}\n\n"

        return res


class MurphiConstDecl:
    def __init__(self, name, val):
        assert isinstance(name, str)
        self.name = name
        self.val = val
        const_map[name] = int(str(val))

    def __str__(self):
        return "%s : %s" % (self.name, self.val)

    def __repr__(self):
        return "MurphiConst(%s, %s)" % (self.name, self.val)

    def __eq__(self, other):
        return isinstance(other, MurphiConstDecl) and self.name == other.name and self.val == other.val

class RngConst:
    pass

class IntRngConst(RngConst):
    def __init__(self, val):
        #assert isinstance(name, str)
        self.val = val

    def __str__(self):
        return "%d" % ( self.val)

    def __repr__(self):
        return "IntRngConst(%d)" %  self.val

    def __eq__(self, other):
        return isinstance(other, IntRngConst) and self.val == other.val

class NameRngConst(RngConst):
    def __init__(self, name):
        assert isinstance(name, str)
        self.val = name

    def __str__(self):
        return "%s" % ( self.name)

    def __repr__(self):
        return "IntRngConst(%s)" %  self.name

    def __eq__(self, other):
        return isinstance(other, NameRngConst) and self.name == other.name

class MurphiType:
    pass

class VarType(MurphiType):
    def __init__(self, name):
        if check_ivy(ivySelect):
            self.name = name.lower()+"_t"
        else:
            self.name = name

    def __str__(self):
        return self.name

    def __repr__(self):
        return "VarType(%s)" % self.name

    def __eq__(self, other):
        return isinstance(other, VarType) and self.name == other.name

class RngType(MurphiType):
    def __init__(self, downRng:str,upRng:str):
        assert isinstance(downRng, str)
        assert isinstance(upRng, str)

        self.downRng = downRng
        self.upRng =upRng

    def __str__(self):
        #return(self.downRng+".."+self.upRng)
        return "%s..%s" % (self.downRng, self.upRng)

    def __repr__(self):
        return "RangeType (is %s .. %s)" % ( self.downRng, self.upRng)

    def __eq__(self, other):
        return isinstance(other, RngType) and self.downRng == other.downRng and self.upRng==other.upRng

class BooleanType(MurphiType):
    def __init__(self):
        pass

    def __str__(self):
        if check_ivy(ivySelect):
            return "bool"
        else:
            return "boolean"

    def __repr__(self):
        return "BooleanType()"

    def __eq__(self, other):
        return isinstance(other, BooleanType)

class ScalarSetType(MurphiType):
    def __init__(self, const_name: str):
        assert isinstance(const_name, str)
        self.const_name = const_name

    def __str__(self):
        return "scalarset(%s)" % self.const_name

    def __repr__(self):
        return "ScalarSetType(%s)" % self.const_name

    def __eq__(self, other):
        return isinstance(other, ScalarSetType) and self.const_name == other.const_name

class UnionType(MurphiType):
    def __init__(self, typs):
        self.typs = typs

    def __str__(self):
        # if check_ivy(ivySelect):
        #     # res = "struct {\n"
        #     # for var_typ in self.typs:
        #     #     union_sub_type = random.choice(string.ascii_lowercase)
        #     #     res += indent(union_sub_type,2) + ":" + var_typ.name + ","
        #     return ""
        #     # return "struct {\n%s\n}" % (', '.join(str(typ) for typ in self.typs))
        # else:
        return "union {%s}" % (', '.join(str(typ) for typ in self.typs))

    def __repr__(self):
        return "UnionType(%s)" % (', '.join(repr(typ) for typ in self.typs))

    def __eq__(self, other):
        return isinstance(other, UnionType) and self.typs == other.typs

class EnumType(MurphiType):
    def __init__(self, names):
        self.names = names

    def __str__(self):
        # if check_ivy(ivySelect):
        #         #     return "{%s}" % (', '.join(name for name in self.names))
        #         # else:
        return "enum {%s}" % (', '.join(name for name in self.names))

    def __repr__(self):
        return "EnumType(%s)" % (', '.join(repr(name) for name in self.names))

    def __eq__(self, other):
        return isinstance(other, EnumType) and self.names == other.names

class ArrayType(MurphiType):
    def __init__(self, idx_typ, ele_typ):
        self.idx_typ = idx_typ
        self.ele_typ = ele_typ

    def __str__(self):
        # if check_ivy(ivySelect):
        #     return "(%s) : %s" % (random.choice(string.ascii_uppercase) + ":" + str(self.idx_typ), self.ele_typ)
        #
        # # elif smvSelect:
        # #     return "smv"
        #
        # else:
        return "array [%s] of %s" % (self.idx_typ, self.ele_typ)
    def __repr__(self):
        return "ArrayType(%s, %s)" % (repr(self.idx_typ), repr(self.ele_typ))

    def __eq__(self, other):
        return isinstance(other, ArrayType) and self.idx_typ == other.idx_typ and \
            self.ele_typ == other.ele_typ

class RecordType(MurphiType):
    def __init__(self, typ_decls):
        self.typ_decls = typ_decls

    def __str__(self):
        return "record\n%s\nend" % ('\n'.join(indent(str(decl), 2) + ';' for decl in self.typ_decls))

    def __repr__(self):
        return "RecordType(%s)" % (', '.join(repr(decl) for decl in self.typ_decls))

    def __eq__(self, other):
        return isinstance(other, RecordType) and self.typ_decls == other.typ_decls

union_dict = dict()
class MurphiTypeDecl:
    def __init__(self, name, typ):
        # specific_typ[str(name)] = typ
        self.name = name
        self.typ = typ
        if isinstance(self.typ, ScalarSetType):
            digitType_map[self.name] = self.typ
            re_digitType_map[self.typ.const_name] = self.name
        elif isinstance(self.typ, RngType):
            digitType_map[self.name] = self.typ
            re_digitType_map[str(self.typ)] = self.name

    def __str__(self):
        # if check_ivy(ivySelect):
        #     print(self.typ, self.name)
        #     return IVYObj.type_act(self.typ, self.name)
        # else:
        return "%s : %s" % (self.name, self.typ)

    def __repr__(self):
        return "MurphiTypeDecl(%s, %s)" % (repr(self.name), repr(self.typ))

    def __eq__(self, other):
        return isinstance(other, MurphiTypeDecl) and self.name == other.name and \
            self.typ == other.typ




class MurphiVarDecl:
    def __init__(self, name, typ):
        self.name = name
        self.typ = typ

    def __str__(self):

        global SMVObj
        if smvSelect:
            if isinstance(self.typ, ArrayType):
                return SMVObj.type_act(self.name, self.typ)
            elif isinstance(self.typ, VarType):
                return SMVObj.type_ins_act(self.name, self.typ)
            else:
                global specific_var
                specific_var[str(self.name)] = self.typ
                return "%s : %s;\n" % (self.name, self.typ)

        # elif check_ivy(ivySelect):
        #     return IVYObj.var_define(self.name, self.typ)

        else:
            return "%s : %s" % (self.name, self.typ)

    def __repr__(self):
        return "MurphiVarDecl(%s, %s)" % (repr(self.name), repr(self.typ))

    def __eq__(self, other):
        return isinstance(other, MurphiVarDecl) and self.name == other.name and \
            self.typ == other.typ

class BaseExpr:
    pass

class UnknownExpr(BaseExpr):
    def __init__(self, s):
        self.s = s

    def priority(self):
        return 100

    def __str__(self):
        return "#%s#" % self.s

    def __repr__(self):
        return "UnknownExpr(%s)" % repr(self.s)

    def elaborate(self, prot, bound_vars):
        assert isinstance(prot, MurphiProtocol)
        if self.s == "true":
            return BooleanExpr(True)
        elif self.s == "false":
            return BooleanExpr(False)
        elif self.s in prot.enum_map and smvSelect == False:
            return EnumValExpr(prot.enum_map[self.s], self.s)
        elif smvSelect == True and self.s in prot.ori_enum_map and self.s.lower() in prot.enum_map:
            self.s = self.s.lower()
            return EnumValExpr(prot.enum_map[self.s], self.s)
        elif check_ivy(ivySelect) and self.s in prot.ori_enum_map and self.s.lower()+"_em" in prot.enum_map:
            self.s = self.s.lower()+"_em"
            return EnumValExpr(prot.enum_map[self.s], self.s)
        elif self.s in bound_vars:
            return VarExpr(self.s, bound_vars[self.s])
        elif check_ivy(ivySelect) == False and self.s in prot.var_map:
            return VarExpr(self.s, prot.var_map[self.s])
        elif check_ivy(ivySelect) == True and self.s.lower()+"_v" in prot.var_map:
            self.s = self.s.lower() + "_v"
            return VarExpr(self.s, prot.var_map[self.s])
        elif smvSelect == True and self.s.startswith("INT_"):
            print("---------------------------is number")
        else:
            return VarExpr(self.s, prot.var_map[self.s]) #revise raise AssertionError("elaborate: unrecognized name %s" % self.s)

class BooleanExpr(BaseExpr):
    def __init__(self, val):
        self.val = val

    def priority(self):
        return 100

    def __str__(self):
        if smvSelect:
            if self.val:
                return "TRUE"
            else:
                return "FALSE"
        else:
            if self.val:
                return "true"
            else:
                return "false"

    def __repr__(self):
        return "BooleanExpr(%s)" % repr(self.val)

    def __eq__(self, other):
        return isinstance(other, BooleanExpr) and self.val == other.val

    def elaborate(self, prot, bound_vars):
        return self

class EnumValExpr(BaseExpr):
    def __init__(self, enum_type, enum_val):
        self.enum_type = enum_type
        self.enum_val = enum_val


    def priority(self):
        return 100

    def __str__(self):
        return self.enum_val

    def __repr__(self):
        return "EnumValExpr(%s, %s)" % (repr(self.enum_type), repr(self.enum_val))

    def __eq__(self, other):
        return isinstance(other, EnumValExpr) and self.enum_type == other.enum_type and \
            self.enum_val == other.enum_val

    def elaborate(self, prot, bound_vars):
        return self

class VarExpr(BaseExpr):
    def __init__(self, name, typ):
        self.name = name
        self.typ = typ


    def priority(self):
        return 100

    def __str__(self):
        # global union_dict
        # if str(self.typ) in union_dict.keys():
        #     print(self.name,";",self.typ)
        return str(self.name)

    def __repr__(self):
        return "VarExpr(%s)" % repr(self.name)

    def __eq__(self, other):
        return isinstance(other, VarExpr) and self.name == other.name and self.typ == other.typ

    def elaborate(self, prot, bound_vars):
        return self

class FieldName(BaseExpr):
    def __init__(self, v, field):
        self.v = v
        self.field = field

    def priority(self):
        return 100

    def __str__(self):
        if check_ivy(ivySelect):
            return "%s_%s" % (self.v, self.field)
        else:
            return "%s.%s" % (self.v, self.field)

    def __repr__(self):
        return "FieldName(%s, %s)" % (repr(self.v), repr(self.field))

    def __eq__(self, other):
        return isinstance(other, FieldName) and self.v == other.v and self.field == other.field

    def elaborate(self, prot, bound_vars):
        return FieldName(self.v.elaborate(prot, bound_vars), self.field)

class ArrayIndex(BaseExpr):
    def __init__(self, v, idx):
        self.v = v
        self.idx = idx

    def priority(self):
        return 100

    def __str__(self):
        if check_ivy(ivySelect):
            return "%s(%s)" % (self.v, self.idx)
        else:
            return "%s[%s]" % (self.v, self.idx)

    def __repr__(self):
        return "ArrayIndex(%s, %s)" % (repr(self.v), repr(self.idx))

    def __eq__(self, other):
        return isinstance(other, ArrayIndex) and self.v == other.v and self.idx == other.idx

    def elaborate(self, prot, bound_vars):
        return ArrayIndex(self.v.elaborate(prot, bound_vars), self.idx.elaborate(prot, bound_vars))

invVars = dict()
class ForallExpr(BaseExpr):
    def __init__(self, var_decl, expr):
        self.var_decl = var_decl
        self.var, self.typ = self.var_decl.name, self.var_decl.typ
        self.expr = expr

    def priority(self):
        return 70

    def __str__(self):
        # if check_ivy(ivySelect):
        #     global invVars
        #     invVars.update({self.var:self.var.upper()})
        #     res = " " + str(self.expr) + "\n"
        #     if isinstance(self.expr, OpExpr):
        #         pattern = re.compile(r'\b(' + '|'.join(re.escape(key) for key in invVars.keys()) + r')\b')
        #         res = pattern.sub(lambda x: invVars[x.group()], res)
        #     return res
        # else:
        res = "forall %s do\n" % self.var_decl
        res += indent(str(self.expr), 2) + "\n"
        res += "end"
        return res

    def __repr__(self):
        return "ForallExpr(%s, %s)" % (repr(self.var_decl), repr(self.expr))

    def __eq__(self, other):
        return isinstance(other, ForallExpr) and self.var_decl == other.var_decl and \
            self.expr == other.expr

    def elaborate(self, prot, bound_vars):
        bound_vars[self.var] = self.typ
        res = ForallExpr(self.var_decl, self.expr.elaborate(prot, bound_vars))
        del bound_vars[self.var]
        return res


class ExistsExpr(BaseExpr):
    def __init__(self, var_decl, expr):
        self.var_decl = var_decl
        self.var, self.typ = self.var_decl.name, self.var_decl.typ
        self.expr = expr

    def priority(self):
        return 70

    def __str__(self):
        # if check_ivy(ivySelect):
        #     global invVars
        #     invVars.update({self.var:self.var.upper()})
        #     res = " " + str(self.expr) + "\n"
        #     if isinstance(self.expr, OpExpr):
        #         pattern = re.compile(r'\b(' + '|'.join(re.escape(key) for key in invVars.keys()) + r')\b')
        #         res = pattern.sub(lambda x: invVars[x.group()], res)
        #     return res
        # else:
        res = f"exists {self.var_decl} do {self.expr} end"
        # res += str(self.expr)
        # res += "end"
        return res

    def __repr__(self):
        return "ExistsExpr(%s, %s)" % (repr(self.var_decl), repr(self.expr))

    def __eq__(self, other):
        return isinstance(other, ExistsExpr) and self.var_decl == other.var_decl and \
            self.expr == other.expr

    def elaborate(self, prot, bound_vars):
        bound_vars[self.var] = self.typ
        res = ExistsExpr(self.var_decl, self.expr.elaborate(prot, bound_vars))
        del bound_vars[self.var]
        return res


class AxiomExpr(BaseExpr):
    def __init__(self, name, expr):
        self.name = name
        self.expr = expr
 
    def __str__(self):
        res = "axiom \"%s\"\n" % self.name
        res += indent(str(self.expr), 2)
        res +=";\n"
        return res
    
    def __repr__(self):
        return "Axiom(%s, %s)" % (repr(self.name), repr(self.expr))

    def __eq__(self, other):
        return isinstance(other, AxiomExpr) and self.name == other.name and self.expr == other.expr
    
    def elaborate(self, prot, bound_vars):
        return AxiomExpr(self.name, self.expr.elaborate(prot, bound_vars))



priority_map = {
    '*': 65,
    '/': 65,
    '%': 65,
    '<=': 62,
    '>=': 62,
    '<': 62,
    '>': 62,
    '+': 60,
    '-': 60,
    '=': 50,
    '!=': 50,
    '&': 35,
    '|': 30,
    '->': 25
}

# def isboolVar(formula):
#     if isinstance(formula, NegExpr):
#         return 1-isboolVar(formula.expr)
#     elif isinstance(formula, ArrayIndex):
#         return isboolVar(formula.v)
#     elif isinstance(formula, ArrayType):
#         return isboolVar(formula.ele_typ)
#     elif isinstance(formula, FieldName):
#         return isboolVar(formula.field)
#     elif isinstance(formula, lark.lexer.Token):
#         if str(formula) in specific_typ.keys():
#             return isboolVar(specific_typ[str(formula)])
#     elif isinstance(formula, BooleanType):
#         return 1
#     else:
#         print("isboolVar-else:",formula,type(formula))
#     return -1

class OpExpr(BaseExpr):
    def __init__(self, op, expr1, expr2):
        assert isinstance(op, str) and op in ("+","-",'*','/','%','<=','>=','>','<','=', '!=', '&', '|', '->', '+')
        assert isinstance(expr1, BaseExpr), "OpExpr: expr1 %s has type %s" % (expr1, type(expr1))
        assert isinstance(expr2, BaseExpr), "OpExpr: expr2 %s has type %s" % (expr2, type(expr2))
        self.op = op
        self.expr1 = expr1
        self.expr2 = expr2

    def priority(self):
        return priority_map[self.op]

    def __str__(self):
        s1, s2 = str(self.expr1), str(self.expr2)
        global specific_var
        if self.op in ('&', '|', '->'):
            if not (isinstance(self.expr1, OpExpr)):
                if isinstance(self.expr1, NegExpr):
                    negvar_pt = re.sub(r'\[.*?\]', '[_]', str(self.expr1.expr))
                    if (str(self.expr1.expr) in specific_var.keys() and isinstance(specific_var[str(self.expr1.expr)],
                                                                                  BooleanType)) or (negvar_pt in specific_var.keys() and isinstance(specific_var[negvar_pt], BooleanType)):
                        # s1 = "(" + str(self.expr1.expr) + " = FALSE)"
                        self.expr1 = OpExpr('=', self.expr1.expr, BooleanExpr(False))
                        s1 = str(self.expr1)
                else:
                    var_pt = re.sub(r'\[.*?\]', '[_]', str(self.expr1))
                    if (str(self.expr1) in specific_var.keys() and isinstance(specific_var[str(self.expr1)],
                                                                           BooleanType)) or (var_pt in specific_var.keys() and isinstance(specific_var[var_pt], BooleanType)):
                        # s1 = "(" + s1 + " = TRUE)"
                        self.expr1 = OpExpr('=', self.expr1, BooleanExpr(True))
                        s1 = str(self.expr1)
                # if isboolVar(self.expr1) == 1:
                #     s1 = "(" + s1 + " = True)"
                # elif isboolVar(self.expr1) == 0:
                #     s1 = "(" + s1 + " = False)"
                # print(print("neg1-2:",self.expr1))
            if not (isinstance(self.expr2, OpExpr)):
                if isinstance(self.expr2, NegExpr):
                    negvar_pt = re.sub(r'\[.*?\]', '[_]', str(self.expr2.expr))
                    if (str(self.expr2.expr) in specific_var.keys() and isinstance(specific_var[str(self.expr2.expr)],
                                                                                  BooleanType)) or (negvar_pt in specific_var.keys() and isinstance(specific_var[negvar_pt], BooleanType)):
                        # s2 = "(" + str(self.expr2.expr) + " = FALSE)"
                        self.expr2 = OpExpr('=', self.expr2.expr, BooleanExpr(False))
                        s2 = str(self.expr2)
                    # s2 = str(self.expr2.expr)
                else:
                    var_pt = re.sub(r'\[.*?\]', '[_]', str(self.expr2))
                    if (str(self.expr2) in specific_var.keys() and isinstance(specific_var[str(self.expr2)],
                                                                           BooleanType)) or (var_pt in specific_var.keys() and isinstance(specific_var[var_pt], BooleanType)):
                        # s2 = "(" + s2 + " = TRUE)"
                        self.expr2 = OpExpr('=', self.expr2, BooleanExpr(True))
                        s2 = str(self.expr2)
                # if isboolVar(self.expr2) == 1:
                #     s2 = "(" + s2 + " = True)"
                # elif isboolVar(self.expr2) == 0:
                #     s2 = "(" + s2 + " = False)"


        if self.expr1.priority() <= self.priority():
            if '\n' in s1:
                s1 = "(" + indent(s1, 2, first_line=1) + " )"
            else:
                s1 = "(" + s1 + ")"
        if self.expr2.priority() < self.priority():
            if '\n' in s2:
                s2 = "(" + indent(s2, 2, first_line=1) + " )"
            else:
                s2 = "(" + s2 + ")"
        if self.op in ("%"):
            if smvSelect:
                return "(%s %s %s)" % (s1, "mod", s2)
            else:
                return "%s %s %s" % (s1, self.op, s2)
        if self.op in ("=","+","-","*","/","<=",">=",">","<"):
            if smvSelect:
                return "%s %s %s" % (s1, self.op, s2)
            else:
                return "%s %s %s" % (s1, self.op, s2)
        if self.op in ("!="):
            if check_ivy(ivySelect):
                return "%s ~= %s" % (s1, s2)
            else:
                return "%s %s %s" % (s1, self.op, s2)
        elif self.op in ('&'):
            return "%s %s %s" % (s1, self.op, s2)
        elif self.op in ('|'):
            if smvSelect:
                ss1 = ''
                ss2 = ''
                if self.expr1.op == '|' or self.expr1.op == '&' or self.expr1.op == '->':
                    ss1 = "(%s)" % (s1)
                else:
                    ss1 = "%s" % (s1)
                if self.expr2.op == '|' or self.expr2.op == '&' or self.expr2.op == '->':
                    ss2 = "(%s)" % (s2)
                else:
                    ss2 = "%s" % (s2)
                return "%s %s %s" % (ss1, self.op, ss2)
            else:
                return "%s %s %s" % (s1, self.op, s2)
        elif self.op in ('->'):
            if isinstance(self.expr2, OpExpr) and self.expr2.op == '->':
                return "(%s) -> (%s)" % (s1, indent(s2, 2))
            else:
                return "(%s) -> %s" % (s1, indent(s2, 2))
        else:
            raise NotImplementedError

    def getVars(self):
        print(self.expr1,self.expr2)

    def __repr__(self):
        return "OpExpr(%s, %s, %s)" % (self.op, self.expr1, self.expr2)

    def __eq__(self, other):
        return isinstance(other, OpExpr) and self.op == other.op and self.expr1 == other.expr1 and \
            self.expr2 == other.expr2

    def elaborate(self, prot, bound_vars):
        return OpExpr(self.op, self.expr1.elaborate(prot, bound_vars), self.expr2.elaborate(prot, bound_vars))


class IntExpr(BaseExpr):
    def __init__(self, expr):
        self.expr = expr
    
    def priority(self):
        return 800
    
    def __str__(self):
        s = str(self.expr)

        return s
    
    def __eq__(self, other):
        return isinstance(other, IntExpr) and self.expr == other.expr
    
    def __repr__(self):
        return "INT(%s)" % self.expr
    
    def elaborate(self, prot, bound_vars):
        
        return IntExpr(self.expr)


class NegExpr(BaseExpr):
    def __init__(self, expr):
        self.expr = expr


    def priority(self):
        return 80

    def __str__(self):
        s = str(self.expr)
        if self.expr.priority() < self.priority():
            s = "(" + s + ")"

        if check_ivy(ivySelect):
            return "~" + s
        else:
            return "!" + s

    def __repr__(self):
        return "NegExpr(%s)" % self.expr

    def __eq__(self, other):
        return isinstance(other, NegExpr) and self.expr == other.expr

    def elaborate(self, prot, bound_vars):
        return NegExpr(self.expr.elaborate(prot, bound_vars))

class BaseCmd:
    pass

class Skip(BaseCmd):
    def __init__(self):
        pass

    def __str__(self):
        return "skip;"

    def __repr__(self):
        return "Skip()"

    def __eq__(self, other):
        return isinstance(other, Skip)

    def elaborate(self, prot, bound_vars):
        return self

class UndefineCmd(BaseCmd):
    def __init__(self, var):
        self.var = var

    def __str__(self):
        if check_ivy(ivySelect):
            return ""
        else:
            return "undefine %s;" % self.var

    def __repr__(self):
        return "UndefineCmd(%s)" % repr(self.var)

    def __eq__(self, other):
        return isinstance(other, UndefineCmd) and self.var == other.var

    def elaborate(self, prot, bound_vars):
        return UndefineCmd(self.var.elaborate(prot, bound_vars))

datas = dict()
equal_datas = dict()
class AssignCmd(BaseCmd):
    def __init__(self, var, expr):
        assert isinstance(var, BaseExpr)
        # print(record_map)
        self.var = var
        self.expr = expr

    def __str__(self):
        # if check_ivy(ivySelect):
        #     if isinstance(self.var, VarExpr) and isinstance(self.expr, VarExpr) and re.search("data",
        #                                                                                       self.expr.typ.name):
        #         # print(datas)
        #         return ""
        #     else:
        #         return indent("%s := %s;\n" % (self.var, self.expr), 2)
        # else:
        return indent("%s := %s;\n" % (self.var, self.expr), 0)

    def __repr__(self):
        return "AssignCmd(%s, %s)" % (repr(self.var), repr(self.expr))

    def __eq__(self, other):
        return isinstance(other, AssignCmd) and self.var == other.var and self.expr == other.expr

    def elaborate(self, prot, bound_vars):
        if isinstance(self.expr, lark.lexer.Token):
            return AssignCmd(self.var.elaborate(prot, bound_vars), self.expr)
        return AssignCmd(self.var.elaborate(prot, bound_vars), self.expr.elaborate(prot, bound_vars))

def paraDataVars(value,equal_vars):
    cmds = set()
    equal_vars = set(equal_vars)
    for i in range(len(equal_vars)-1,0,-1):
        cmds.add(f"{list(equal_vars)[i]} := {list(equal_vars)[i-1]}")
    return cmds


class ForallCmd(BaseCmd):
    def __init__(self, var_decl, cmds):
        self.var_decl = var_decl
        self.var, self.typ = self.var_decl.name, self.var_decl.typ
        self.cmds = cmds


    def __str__(self):
        # if check_ivy(ivySelect):
        #     res=''
        #     for cmd in self.cmds:
        #         if isinstance(cmd.var,VarExpr) and re.search("data", cmd.expr.typ.name):
        #             datas[cmd.var.name] = cmd.expr.name
        #         res += str(cmd)
        #         # pattern = r"\[(.*?)\]"
        #         # match = re.search(pattern, res)
        #         # if match:
        #         #     found_string = match.group(1)
        #         #     if found_string == self.var:
        #         #         replacement = "(" + found_string.upper() + ")"
        #         #         res = re.sub(re.escape(match.group(0)), replacement, res)
        #
        #     cmds = set()
        #     for var,value in datas.items():
        #         if value in equal_datas:
        #             equal_datas[value].append(var)
        #         else:
        #             equal_datas[value] = [var]
        #     for value, vars in equal_datas.items():
        #         cmds = cmds | paraDataVars(value,vars)
        #     # for value,vars in equal_datas.items():
        #     #     for cmd in self.cmds:
        #     #         if isinstance(cmd.var, VarExpr) and cmd.var.name in vars:
        #     #             if len(vars)>1:
        #     #                 print(cmd)
        #
        #         # if self.var in vars:
        #         #     print(self.var,",",value)
        #         # if len(vars) >1:
        #         #     print(f"值为 {value} 的键：{vars}")
        #     for cmd in cmds:
        #         res += indent(str(cmd), 2) + ";" + "\n"
        #     return res
        # else:
        res = "for %s do\n" % self.var_decl
        for cmd in self.cmds:
            res += indent(str(cmd), 2) + "\n"
        res += "end;"
        return res

    def __repr__(self):
        return "ForallCmd(%s, %s)" % (repr(self.var_decl), repr(self.cmds))

    def __eq__(self, other):
        return isinstance(other, ForallCmd) and self.var_decl == other.var_decl and \
            self.cmds == other.cmds

    def elaborate(self, prot, bound_vars):
        bound_vars[self.var] = self.typ
        res = ForallCmd(self.var_decl, [cmd.elaborate(prot, bound_vars) for cmd in self.cmds])
        del bound_vars[self.var]
        return res

class IfCmd(BaseCmd):
    def __init__(self, args):
        global specific_var
        # print(specific_var)
        assert len(args) >= 2, "IfCmd: input args has %s elements" % len(args)
        self.args = args

        self.if_branches = []
        self.else_branch = None
        for i in range(len(self.args) // 2):
            self.if_branches.append((self.args[2*i], self.args[2*i+1]))

        if len(self.args) % 2 == 1:
            self.else_branch = self.args[-1]

    def __str__(self):
        if check_ivy(ivySelect):
            res = "if (%s) {\n" % self.if_branches[0][0]
            for cmd in self.if_branches[0][1]:
                res += indent(str(cmd), 2)
            res += "}"
            for i in range(1, len(self.if_branches)):
                res += "\n"
                res += "else if (%s) {\n" % self.if_branches[i][0]
                for cmd in self.if_branches[i][1]:
                    res += indent(str(cmd), 2)
                res += "}"
            if self.else_branch:
                res += "\n"
                res += "else {\n"
                for cmd in self.else_branch:
                    res += indent(str(cmd), 2)
                res += "}"
            res += ";\n"
            return res
        else:
            res = "if (%s) then\n" % self.if_branches[0][0]
            for cmd in self.if_branches[0][1]:
                res += indent(str(cmd), 2) + "\n"
            for i in range(1, len(self.if_branches)):
                res += "elsif (%s) then\n" % self.if_branches[i][0]
                for cmd in self.if_branches[i][1]:
                    res += indent(str(cmd), 2) + "\n"
            if self.else_branch:
                res += "else\n"
                for cmd in self.else_branch:
                    res += indent(str(cmd), 2) + "\n"
            res += "end;"
            return res

    def __repr__(self):
        return "IfCmd(%s)" % repr(self.args)

    def __eq__(self, other):
        return isinstance(other, IfCmd) and self.args == other.args

    def elaborate(self, prot, bound_vars):
        new_args = []
        for arg in self.args:
            if isinstance(arg, BaseExpr):
                new_args.append(arg.elaborate(prot, bound_vars))
            else:
                new_args.append([cmd.elaborate(prot, bound_vars) for cmd in arg])
        return IfCmd(new_args)

class StartState:
    def __init__(self, name, cmds):
        self.name = name
        self.cmds = cmds

    def __str__(self):
        res = "startstate \"%s\"\n" % self.name
        for cmd in self.cmds:
            res += indent(str(cmd), 2) + "\n"
        res += "endstartstate;"
        return res

    def __repr__(self):
        return "StartState(%s, %s)" % (repr(self.name), repr(self.cmds))

    def elaborate(self, prot, bound_vars):
        return StartState(self.name, [cmd.elaborate(prot, bound_vars) for cmd in self.cmds])



class RulesetStartState:
    def __init__(self, var_decls, startstate):
        self.var_decls = var_decls
        self.var_map = dict()
        for var_decl in self.var_decls:
            self.var_map[var_decl.name] = var_decl.typ
        self.startstate = startstate

    def __str__(self):
        res = "ruleset %s do\n" % ("; ".join(str(var_decl) for var_decl in self.var_decls))
        res += str(self.startstate) + "\n"
        res += "endruleset;"
        return res
    
    def __repr__(self):
        return "RulesetStartState(%s, %s)" % (repr(self.var_decls), repr(self.startstate))

    def elaborate(self, prot, bound_vars):
        for var, typ in self.var_map.items():
            bound_vars[var] = typ
        res = RulesetStartState(self.var_decls, self.startstate.elaborate(prot, bound_vars))
        for var in self.var_map:
            del bound_vars[var]
        return res

class MurphiRuleSet:
    def __init__(self, var_decls, rule):
        self.var_decls = var_decls
        self.var_map = dict()
        for var_decl in self.var_decls:
            self.var_map[var_decl.name] = var_decl.typ
        self.rule = rule


    def __str__(self):
        res = "ruleset %s do\n" % ("; ".join(str(var_decl) for var_decl in self.var_decls))
        res += str(self.rule) + "\n"
        res += "endruleset;"
        return res

    def __repr__(self):
        return "MurphiRuleSet(%s, %s)" % (repr(self.var_decls), repr(self.rule))

    def elaborate(self, prot, bound_vars):
        for var, typ in self.var_map.items():
            bound_vars[var] = typ
        res = MurphiRuleSet(self.var_decls, self.rule.elaborate(prot, bound_vars))
        for var in self.var_map:
            del bound_vars[var]
        return res

class MurphiRule:
    # def __init__(self, name, cond, cmds, rule_vars):
    def __init__(self, args):
        self.rule_var_map = dict()
        self.args = args
        assert len(args) >= 3
        if len(args) == 3:
            self.name,self.cond,self.cmds = args
        else:
            self.name,self.cond,self.rule_vars,self.cmds = args
            
            for rule_var in self.rule_vars:
                self.rule_var_map[rule_var.name] = rule_var.typ
        self.name = self.name.replace('"','')

    def __str__(self):
        res = "rule \"%s\"\n" % self.name
        res += indent(str(self.cond), 2) + "\n"
        res += "==>\n"
        res += "begin\n"
        for cmd in self.cmds:
            res += indent(str(cmd), 2) + "\n"
        res += "endrule;"
        return res

    def __repr__(self):
        return "MurphiRule(%s, %s, %s)" % (repr(self.name), repr(self.cond), repr(self.cmds))

    def __eq__(self, other):
        return isinstance(other, MurphiRule) and self.name == other.name and \
            self.cond == other.cond and self.cmds == other.cmds

    def elaborate(self, prot, bound_vars):
        new_args = []
        if len(self.args)>3:
            for var, typ in self.rule_var_map.items():
                bound_vars[var] = typ
            new_args.append(self.name)
            new_args.append(self.cond.elaborate(prot, bound_vars))
            new_args.append(self.rule_vars)
            new_args.append([cmd.elaborate(prot, bound_vars) for cmd in self.cmds])
            
            for var in self.rule_var_map:
                del bound_vars[var]
        elif len(self.args)==3:
            new_args.append(self.name)
            new_args.append(self.cond.elaborate(prot, bound_vars))
            new_args.append([cmd.elaborate(prot, bound_vars) for cmd in self.cmds])
        
        
        return MurphiRule(new_args)

    def addSpecialGuard(self,f):
        self.cond = OpExpr("&",f,self.cond)

class MurphiInvariant:
    def __init__(self, name, inv):
        self.name = name
        self.inv = inv

    def __str__(self):
        # if check_ivy(ivySelect):
        #     res = "conjecture " + str(self.inv)
        #     res = re.sub(r"\[([^]]+)\]", r"(\1)", res)
        #     return res
        # else:
        res = "invariant \"%s\"\n" % self.name
        res += indent(str(self.inv), 2)
        res +=";\n"
        return res

    def __repr__(self):
        return "Invariant(%s, %s)" % (repr(self.name), repr(self.inv))

    def __eq__(self, other):
        return isinstance(other, MurphiInvariant) and self.name == other.name and \
            self.inv == other.inv

    def elaborate(self, prot, bound_vars):
        return MurphiInvariant(self.name, self.inv.elaborate(prot, bound_vars))

class MurphiProtocol:
    def __init__(self, consts, types, vars, start_state, decls):
        self.consts = consts
        self.types = types
        self.vars = vars
        self.start_state = start_state
        self.decls = decls
        global ivySelect
        self.invSelect = ivySelect

        global smvSelect
        self.smvSelect = smvSelect

        self.typ_map = dict()
        self.enum_typ_map = dict()
        self.enum_map = dict()
        self.ori_enum_map = list()
        self.scalarset = list()
        # Process types
        if check_ivy(ivySelect):

            # global record_map
            # self.record_map = dict()
            for typ_decl in self.types:
                typ_decl.name = typ_decl.name.lower() + "_t"
                self.typ_map[typ_decl.name] = typ_decl.typ
                # if isinstance(typ_decl.typ, RecordType):
                #     subrecordlist = list()
                #     for subRecordTyp in typ_decl.typ.typ_decls:
                #
                #         if isinstance(subRecordTyp, BooleanType):
                #             print("subRecordTyp-if")
                #             print(subRecordTyp)
                #         else:
                #             print("subRecordTyp-else")
                #             print(subRecordTyp)
                #             subrecordlist.append([subRecordTyp.name, subRecordTyp.typ.name])
                #         record_map[typ_decl.name] = subrecordlist
                #     print(subrecordlist)
                #     print("record_map:",record_map)
                if isinstance(typ_decl.typ, ScalarSetType):
                    self.scalarset.append(typ_decl.name)
                if isinstance(typ_decl.typ, EnumType):
                    for subname in typ_decl.typ.names:
                        self.ori_enum_map.append(subname)
                    typ_decl.typ.names = [item.lower() + "_em" for item in typ_decl.typ.names]
                    self.enum_typ_map[typ_decl.name] = typ_decl.typ
                    for enum_val in typ_decl.typ.names:
                        self.enum_map[enum_val] = typ_decl.typ
                        # Process variables
            self.var_map = dict()
            for var_decl in self.vars:
                self.var_map[var_decl.name] = var_decl.typ
            self.var_map = {key.lower() + "_v": value for key, value in self.var_map.items()}


            # Elaboration
            self.start_state = self.start_state.elaborate(self, dict())
            self.decls = [decl.elaborate(self, dict()) for decl in self.decls]

        else:
            for typ_decl in self.types:
                self.typ_map[typ_decl.name] = typ_decl.typ
                if isinstance(typ_decl.typ, EnumType):
                    self.enum_typ_map[typ_decl.name] = typ_decl.typ
                    for enum_val in typ_decl.typ.names:
                        self.enum_map[enum_val] = typ_decl.typ

                    if smvSelect:
                        for subname in typ_decl.typ.names:
                            self.ori_enum_map.append(subname)
                        typ_decl.typ.names = [item.lower() for item in typ_decl.typ.names]
                        self.enum_typ_map[typ_decl.name] = typ_decl.typ
                        for enum_val in typ_decl.typ.names:
                            self.enum_map[enum_val] = typ_decl.typ

                if isinstance(typ_decl.typ, ScalarSetType):
                    self.scalarset.append(typ_decl.name)

            # Process variables
            self.var_map = dict()
            for var_decl in self.vars:
                self.var_map[var_decl.name] = var_decl.typ

            # Elaboration
            self.start_state = self.start_state.elaborate(self, dict())
            self.decls = [decl.elaborate(self, dict()) for decl in self.decls]

        # Divide into categories
        self.rule_map = dict()
        self.ori_rule_map = dict()
        self.abs_rule_map = dict()
        self.inv_map = dict()
        self.ori_inv_map = dict()
        self.lemma_map = dict()
        self.axiom_map = dict()


        for decl in self.decls:
            if isinstance(decl, MurphiRule):
                self.rule_map[decl.name] = decl
                if decl.name.startswith("ABS_"):
                    self.abs_rule_map[decl.name] = decl
                else:
                    self.ori_rule_map[decl.name] = decl
            elif isinstance(decl, MurphiRuleSet):
                self.rule_map[decl.rule.name] = decl
                if decl.rule.name.startswith("ABS_"):
                    self.abs_rule_map[decl.rule.name] = decl
                else:
                    self.ori_rule_map[decl.rule.name] = decl
            elif isinstance(decl, MurphiInvariant):
                self.inv_map[decl.name] = decl
                if decl.name.startswith("Lemma_"):
                    self.lemma_map[decl.name] = decl
                else:
                    self.ori_inv_map[decl.name] = decl
            elif isinstance(decl, AxiomExpr):
                self.axiom_map[decl.name] = decl
            else:
                print("else:",decl,type(decl))
                raise NotImplementedError
        #refine abs_r_src etc
        self.export_name = list(self.rule_map.keys())
    def addition(self):
        for k in self.ori_rule_map.keys():
            r=self.ori_rule_map[k]
            if isinstance(r, MurphiRuleSet):
                if len(r.var_decls)==2:
                    for ak in self.abs_rule_map.keys():
                        if ak==("ABS_"+ k+ "_"+ r.var_decls[0].name ):
                            ar=self.abs_rule_map[ak]
                            addf=NegExpr(OpExpr("=",EnumValExpr(None,"Other"),VarExpr(name=r.var_decls[1].name,typ=r.var_decls[1].typ)))
                            ar.rule.addSpecialGuard(addf)
                        elif  ak==("ABS_"+k+"_"+r.var_decls[1].name):
                            ar=self.abs_rule_map[ak]
                            addf=NegExpr(OpExpr("=",VarExpr(name=r.var_decls[0].name,typ=r.var_decls[0].typ),EnumValExpr(None,"Other")))
                            ar.rule.addSpecialGuard(addf)
                        else:
                            pass



    def __str__(self):
        if check_ivy(self.invSelect):
            global IVYObj
            IVYObj = toIVY(self.typ_map, self.var_map, self.start_state, self.rule_map, self.inv_map)

            res = self.invSelect + "\n\n"

            res += IVYObj.type_define()

            res += IVYObj.var_define()

            res += "\n\n"

            res += IVYObj.init_act()

            res += "\n\n"

            res += IVYObj.rule_act()

            res += "\n\n"

            res += IVYObj.inv_act()

            # print("self.inv_map:",self.inv_map)
            # for typ in self.types:
            #     if isinstance(typ.typ,RecordType):
            #         pass
            #     else:
            #         res += "type " + str(typ) + "\n\n"
            # print("var-map:")
            # print(self.vars)
            # print(self.var_map)
            # print("self.typ_map:", self.typ_map)
            # print(self.types)
            return res

        elif smvSelect:
            global SMVObj
            SMVObj = toSMV(self.typ_map, self.var_map, self.rule_map, self.start_state)
            # global scalarset
            # scalarset = self.scalarset
            # global typ_map
            # typ_map = self.typ_map

            res = "MODULE main\n"

            res += "VAR\n"
            # print("const_map:",const_map)
            # print("self.typ_map:",self.typ_map)
            # print("self.var_map:",self.var_map)
            # print("self.rule_map:",self.rule_map)
            # for const in self.consts:
            #     res += indent(str(const), 2) + ";\n\n"
            # res += "type\n\n"
            # for typ in self.types:
            #     res += indent(str(typ), 2) + ";\n\n"
            # res += "var\n\n"
            for var in self.vars:
                res += str(var)
            res += "\n"
            res += "--------------------\n\n"

            global specific_var
            # print("specific_var:",specific_var)


            process, rules = SMVObj.new_rule_act()
            res += process
            res += "--------------------\n\n"
            #
            res += "ASSIGN\n"
            res += SMVObj.init_act()
            res += "\n--------------------\n\n"
            #
            res += "\n\n--------------------\n\n"

            res += rules

            return res

        else:
            res = "const\n\n"
            for const in self.consts:
                res += indent(str(const), 2) + ";\n\n"
            res += "type\n\n"
            for typ in self.types:
                res += indent(str(typ), 2) + ";\n\n"
            res += "var\n\n"
            for var in self.vars:
                res += indent(str(var), 2) + ";\n\n"
            res += str(self.start_state) + "\n\n"
            for decl in self.decls:
                res += str(decl) + "\n\n"
            return res

    # def getrule(self):
    #     return self.rule_map
        # return self.__str__()

    def __repr__(self):
        return "MurphiProtocol(%s, %s, %s, %s, %s)" % (repr(self.consts), repr(self.types), repr(self.vars), repr(self.start_state), repr(self.decls))
