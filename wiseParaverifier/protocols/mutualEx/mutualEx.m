const
    NODENUMS : 2;

type
    state : enum{i_em, t_em, c_em, e_em};
    NODE: scalarset(NODENUMS);

var
    n : array [NODE] of state;
    x : boolean;

startstate "Init"
for i: NODE do
    n[i] :=i_em;
endfor;
x := true;
endstartstate;

ruleset i : NODE
do rule "Try"
  n[i] = i_em
==>
begin
  n[i] :=t_em;
endrule;endruleset;

ruleset i : NODE
do rule "Crit"
  n[i] = t_em & x = true
==>
begin
  n[i] := c_em;
  x := false;
endrule;endruleset;

ruleset i : NODE
do rule "Exit"
  n[i] =c_em
==>
begin
  n[i] := e_em;
endrule;endruleset;

ruleset i : NODE
do rule "Idle"
  n[i] = e_em
==>
begin
  n[i] := i_em;
  x := true;
endrule;endruleset;

invariant "mutualEx"
forall i : NODE do forall j : NODE do
i != j ->
    !(n[i] = c_em & n[j] = c_em)
end  end;

