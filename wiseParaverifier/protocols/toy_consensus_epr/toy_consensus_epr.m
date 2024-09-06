const
    QUORUMNUMS : 2;
    VALUENUMS : 2;
    NODENUMS : 2;

type
    quorum: scalarset(QUORUMNUMS);
    node: scalarset(NODENUMS);
    value: scalarset(VALUENUMS);

var
    member: array [node] of array[quorum] of boolean;
    voted: array [node] of boolean;
    vote: array [node] of array[value] of boolean;
    decided: array [value] of boolean;


ruleset n : node do
startstate "Init"
  voted[n] := false;
  for v: value do
    vote[n][v] := false;
    decided[v] := false;
  end;
endstartstate;
endruleset;


ruleset n : node;v : value do
rule "cast_vote"
    voted[n] = false
==>
begin
    vote[n][v] := true;
    voted[n] := true;
endrule;endruleset;


ruleset v : value;q: quorum do
rule "decide"
    forall N:node do member[N][q] = true -> vote[N][v] = true end
==>
begin
    decided[v] := true;
endrule;endruleset;


invariant "toyConsensusEpr"
forall V1:value do
  forall V2:value do
    V1 != V2 ->
    !(decided[V1] = true & decided[V2] = true)
end end;