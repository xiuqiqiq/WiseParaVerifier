
1. 运行murphiparser.py文件生成对应协议的ivy代码，可修改协议及ivy版本：
```
if __name__ == "__main__":
    parse_path = "protocols/"
    parse_name = "mutualEx.m"		# 协议名称
```
```
class MurphiTransformer(Transformer):
    def __init__(self):
        murphi.ivySelect = "#lang ivy1.7"		# ivy版本选择
```

2. 运行SMT/newSMT.py文件将自动调用SMT/constructSMT.py构造给定协议的F(guard, assignment', assumption, !inv', ori_inv)，其中ori_inv代表所有目前已找到的辅助不变式，协议生成的F可在SMT/formula.txt中查看。最终使用的F并非所有生成的F，而是根据paraverifier中的‘invHoldForRule2 ：α 不改变 f 中的任何变量即 f ↔ preCond(f, α) ’剔除了部分F，即!inv'中涉及到的变量都未在assignment'中出现的F。
3. 而后newSMT.py将自动用Z3语法建模有效的F，调用z3-solver求解，若有解即找到反例，使用带反例的协议调用localSearch算法，求出辅助不变式。
4. 直至不再有新的辅助不变式被发现，执行结束，求得的归纳不变式被记录在protocols/protocol_name/protocol_name_invs.txt文件中，并在protocol_nameEfficiencyAna.txt文件中记录了本次执行共调用smtSolver和LocalSearch算法的次数。mutualEx/callingRecord.txt中记录了2节点、3节点使用/不使用invHoldForRule2剔除F各需要调用smtSolver和LocalSearch算法的次数。
```
WithoutRule2_node2
times of calling SMT:64
times of calling LocalSearch:36.


WithRule2_node2
times of calling SMT:56
times of calling LocalSearch:36

------------------------------------------

WithoutRule2_node3
times of calling SMT: 216
times of calling LocalSearch: 77

WithRule2_node3
times of calling SMT: 144
times of calling LocalSearch: 77
```

5. 目前已成功找到2节点的mutualEx归纳不变式：

tips：invariant的命名标识了其反例路径。
```
invariant 'mutualEx_Crit1'
  !(n[2] = C & x = true)
invariant 'mutualEx_Crit2'
  !(n[1] = C & x = true)
invariant 'mutualEx_Crit1_Idle1'
  !(n[2] = C & n[1] = E)
invariant 'mutualEx_Crit2_Idle2'
  !(n[1] = C & n[2] = E)
invariant 'mutualEx_Crit1_Idle1_Crit2'
  !(n[1] = E & x = true)
invariant 'mutualEx_Crit2_Idle2_Crit1'
  !(n[2] = E & x = true)
invariant 'mutualEx_Crit1_Idle1_Crit2_Idle2'
  !(n[1] = E & n[2] = E)
```
3节点的归纳不变式也已找到，但分析结果，比如invariant 'mutualEx_Crit1_Idle3_Exit3'：!(n[2] = C & n[3] = C)，其实就是原始的不变式的另一种实例化方式（目前原始不变式，不论2节点还是3节点，node都只用了(1,2)做实例化）。预计下一步需要加入对称规约技术。
```
invariant 'mutualEx_Crit1'
  !(n[2] = C & x = true)
invariant 'mutualEx_Crit2'
  !(n[1] = C & x = true)
  
  
invariant 'mutualEx_Crit1_Idle1'
  !(n[2] = C & n[1] = E)
invariant 'mutualEx_Crit1_Idle3'
  !(n[2] = C & n[3] = E)
invariant 'mutualEx_Crit2_Idle2'
  !(n[1] = C & n[2] = E)
invariant 'mutualEx_Crit2_Idle3'
  !(n[1] = C & n[3] = E)
  
  
invariant 'mutualEx_Crit1_Idle1_Crit2'
  !(n[1] = E & x = true)
invariant 'mutualEx_Crit1_Idle3_Crit2'
  !(n[3] = E & x = true)
invariant 'mutualEx_Crit1_Idle3_Exit3'
  !(n[2] = C & n[3] = C)
invariant 'mutualEx_Crit2_Idle2_Crit1'
  !(n[2] = E & x = true)
invariant 'mutualEx_Crit2_Idle3_Exit3'
  !(n[1] = C & n[3] = C)
  
  
invariant 'mutualEx_Crit1_Idle1_Crit2_Idle2'
  !(n[1] = E & n[2] = E)
invariant 'mutualEx_Crit1_Idle1_Crit2_Idle3'
  !(n[1] = E & n[3] = E)
invariant 'mutualEx_Crit1_Idle3_Crit2_Exit3'
  !(x = true & n[3] = C)
invariant 'mutualEx_Crit1_Idle3_Crit2_Idle2'
  !(n[3] = E & n[2] = E)
  
  
invariant 'mutualEx_Crit1_Idle1_Crit2_Idle3_Exit3'
  !(n[1] = E & n[3] = C)
invariant 'mutualEx_Crit1_Idle3_Crit2_Exit3_Idle2'
  !(n[3] = C & n[2] = E)
```
