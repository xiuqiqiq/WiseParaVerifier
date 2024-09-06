const
  NODENUMS: 2;
  RESPONSENUM: 2;
  REQUESTNUM: 2;
  IDNUMS: 2;

type
  node: scalarset(NODENUMS);
  response: scalarset(RESPONSENUM);
  request: scalarset(REQUESTNUM);
  db_request_id:scalarset(IDNUMS);


var
  match: array [request] of array[response] of boolean;
  request_sent: array [node] of array[request] of boolean;
  response_sent: array [node] of array[response] of boolean;
  response_received: array [node] of array[response] of boolean;
  db_request_sent: array [db_request_id] of array[request] of boolean;
  db_response_sent: array [db_request_id] of array[response] of boolean;
  t: array [db_request_id] of array[node] of boolean;


ruleset R: request; P:response; I:db_request_id do
startstate "Init"
  for N: node do
    request_sent[N][R] := false;
    response_sent[N][P] := false;
    response_received[N][P] := false;
      t[I][N] := false;
  end;
  db_request_sent[I][R] := false;
  db_response_sent[I][P] := false;
endstartstate;
endruleset;

ruleset n: node; r: request do
rule "new_request"
    true
==>
begin
    request_sent[n][r] := true;
endrule;endruleset;


ruleset n:node; r:request; i:db_request_id do
rule "server_process_request"
    request_sent[n][r] = true & forall N:node do t[i][N] = false end
==>
begin
    t[i][n] := true;
    db_request_sent[i][r] := true;
endrule;endruleset;


ruleset i:db_request_id; r:request; p:response do
rule "db_process_request"
    db_request_sent[i][r] = true & match[r][p] = true
==>
begin
    db_response_sent[i][p] := true;
endrule;endruleset;


ruleset n:node; i:db_request_id; p:response do
rule "server_process_db_response"
    db_response_sent[i][p] = true & t[i][n] = true
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

