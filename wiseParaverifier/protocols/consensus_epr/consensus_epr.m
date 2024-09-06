const
    NODENUMS : 3;
    QUORUMNUMS : 2;
    VALUENUMS : 2;


type
    quorum: scalarset(QUORUMNUMS);
    node: scalarset(NODENUMS);
    value: scalarset(VALUENUMS);

var
    member: array [node] of array[quorum] of boolean;
    vote_request_msg: array [node] of array [node] of boolean;
    voted: array [node] of boolean;
    vote_msg: array [node] of array [node] of boolean;
    votes: array [node] of array [node] of boolean;
    leader: array [node] of boolean;
    decided: array [node] of array[value] of boolean;


ruleset n: node; m: node do
startstate "Init"
  voted[n] := false;
  leader[n] := false;
  vote_request_msg[n][m] := false;
  vote_msg[n][m] := false;
  votes[n][m] := false;
  for v: value do
      decided[n][v] := false;
  end;
endstartstate;
endruleset;


ruleset src: node; dst: node do
rule "send_request_vote"
    true
==>
begin
    vote_request_msg[src][dst] := true;
endrule;endruleset;


ruleset src: node; dst: node do
rule "send_vote"
    voted[src] = false & vote_request_msg[dst][src] = true
==>
begin
    vote_msg[src][dst] := true;
    voted[src] := true;
endrule;endruleset;


ruleset n: node; sender: node do
rule "recv_vote"
    vote_msg[sender][n] = true
==>
begin
    votes[n][sender] := true;
endrule;endruleset;


ruleset n: node; q: quorum do
rule "become_leader"
    forall N:node do member[N][q] = true -> votes[n][N] = true end
==>
begin
    leader[n] := true;
endrule;endruleset;


ruleset n: node; v: value do
rule "decide"
    leader[n] = true & forall V:value do decided[n][V] = false end
==>
begin
    decided[n][v] := true;
endrule;endruleset;


invariant "consensusepr1"
forall N1:node do forall N2: node do forall V1:value do forall V2:value do
    !(decided[N1][V1] = true & decided[N2][V2] = true)
end end end end;
