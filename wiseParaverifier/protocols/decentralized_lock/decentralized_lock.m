const
    NODENUMS : 4;

type
    NODE: scalarset(NODENUMS);
    message_idx : array [NODE] of boolean;

var
    message : array [NODE] of array [NODE] of boolean;
    has_lock : array [NODE] of boolean;

    start_node : NODE;


ruleset h : NODE do
startstate "Init"
  for i : NODE do
    start_node := i; 
    message[i][h] := false;
    has_lock[h] := (h = start_node);
  end;
endstartstate;
endruleset;


ruleset src : NODE; dst : NODE do
rule "send"
  has_lock[src] = true
==>
begin
  message[src][dst] := true;
  has_lock[src] := false;
endrule;endruleset;

ruleset src : NODE; dst : NODE do
rule "recv"
  message[src][dst] = true
==>
begin
  message[src][dst] := false;
  has_lock[dst] := true;
endrule;endruleset;

invariant "Onelock"
forall i : NODE do forall j : NODE do
  i != j ->
    !(has_lock[i] = true & has_lock[j] = true)
end  end;
