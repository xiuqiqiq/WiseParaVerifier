const
  NODENUMS: 2;
  RESPONSENUM: 2;
  REQUESTNUM: 2;

type
  node: scalarset(NODENUMS);
  response: scalarset(RESPONSENUM);
  request: scalarset(REQUESTNUM);


var
  match: array [request] of array[response] of boolean;
  request_sent: array [node] of array[request] of boolean;
  response_sent: array [node] of array[response] of boolean;
  response_received: array [node] of array[response] of boolean;


ruleset R: request; P:response do
startstate "Init"
  for N: node do
    request_sent[N][R] := false;
    response_sent[N][P] := false;
    response_received[N][P] := false;
  end;
endstartstate;
endruleset;


ruleset n: node; r: request do
rule "new_request"
    true
==>
begin
    request_sent[n][r] := true;
endrule;endruleset;


ruleset n:node; r:request; p:response do
rule "respond"
    request_sent[n][r] = true & match[r][p] = true
==>
begin
    response_sent[n][p] := true;
endrule;endruleset;


ruleset n:node; p:response do
rule "receive_response"
    response_sent[n][p] = true
==>
begin
    response_received[n][p] := true;
endrule;endruleset;



invariant "clientServerAE"
forall N:node do forall P:response do
  response_received[N][P] = true ->
  exists R:request do (request_sent[N][R] = true & match[R][P] = true)
end end end;

