

const 
    NODE_NUM  : 2;
    Cache_NUM : 2;
    Addr_NUM  : 4;
    Data_NUM  : 2;
    addrNum : 4;
    cacheNum : 2;

type 
    nodeType  : scalarset(NODE_NUM);
    dataType  : scalarset(Data_NUM);
    addrType  : scalarset(addrNum);
    stateType : enum{i_em, t_em, c_em, e_em};
    cacheType : scalarset(cacheNum);

    cacheState: record
      state : stateType;
      mark  : addrType;
      data  : dataType;
    end;

var
  n: array[nodeType] of array[cacheType] of cacheState;
  x: array[addrType] of boolean;
  memData: array[addrType] of dataType;
  auxData: array[addrType] of dataType;


ruleset c: cacheType do
startstate "Init"
begin
  for i: nodeType do
      n[i][c].state := i_em; 
  endfor;
  for a: addrType do
    x[a] := true;
  endfor;
endstartstate;
endruleset;

ruleset i : nodeType; c: cacheType; d: dataType; a : addrType do
rule "Store"
  n[i][c].state = c_em &
  n[i][c].mark = a
==>
begin
  n[i][c].data := d;
  auxData[a] := d;
endrule;
endruleset;

ruleset i : nodeType; c: cacheType do 
rule "Try"
  n[i][c].state = i_em
==> 
begin
  n[i][c].state := t_em;
endrule;
endruleset;


ruleset i : nodeType; c : cacheType; a : addrType do 
rule "Crit"
  n[i][c].state = t_em & 
  x[a] = true 
==>
begin
  n[i][c].state := c_em;
  n[i][c].mark  := a; 
  n[i][c].data  := memData[a]; 
  x[a] := false;
endrule;endruleset;



ruleset i : nodeType; c: cacheType do 
rule "Exit"
  n[i][c].state = c_em
==>
begin
  n[i][c].state := e_em;
endrule;endruleset;



ruleset i : nodeType; c : cacheType; a : addrType do 
rule "Idle"
  n[i][c].state = e_em &
  n[i][c].mark = a
==>
begin
  n[i][c].state := i_em;
  x[a] := true;
  memData[a] := n[i][c].data;
endrule;endruleset;



invariant "mutualEx"
forall i : nodeType do 
  forall j : nodeType do 
  i != j ->
    forall c1 : cacheType do
    n[i][c1].state = c_em ->
      forall c2 : cacheType do
          !(n[j][c2].state = c_em &
          n[j][c2].mark = n[i][c1].mark) 
        endforall
    endforall
  end  
end;


invariant "coherence"
forall i : nodeType do
  forall c : cacheType do
    forall a : addrType do
    (n[i][c].state = c_em -> 
    n[i][c].data = auxData[a] & n[i][c].mark = a)
  end
  end
end;



