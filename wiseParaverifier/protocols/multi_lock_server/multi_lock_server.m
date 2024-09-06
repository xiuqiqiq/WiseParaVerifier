const
    NODENUMS : 2;
    LOCKNUMS : 1;

type
    node: scalarset(NODENUMS);
    lock: scalarset(LOCKNUMS);


var
    lock_msg : array [node] of array [lock] of boolean;
    grant_msg : array [node] of array [lock] of boolean;
    unlock_msg : array [node] of array [lock] of boolean;
    holds_lock : array [node] of array [lock] of boolean;

    server_holds_lock : array [lock] of boolean;


ruleset l : lock do
startstate "Init"
  for n: node do
    lock_msg[n][l] := false;
    grant_msg[n][l] := false;
    unlock_msg[n][l] := false;
    holds_lock[n][l] := false;
    server_holds_lock[l] := true;
  end;
endstartstate;
endruleset;


ruleset n : node; l : lock do
rule "send_lock"
  true
==>
begin
  lock_msg[n][l] := true;
endrule;endruleset;

ruleset n : node; l : lock do
rule "recv_lock"
  lock_msg[n][l] = true &
  server_holds_lock[l] = true
==>
begin
  server_holds_lock[l] := false;
  lock_msg[n][l] := false;
  grant_msg[n][l] := true;
endrule;endruleset;

ruleset n : node; l : lock do
rule "recv_grant"
  grant_msg[n][l] = true
==>
begin
  grant_msg[n][l] := false;
  holds_lock[n][l] := true;
endrule;endruleset;

ruleset n : node; l : lock do
rule "unlock"
  holds_lock[n][l] = true
==>
begin
  holds_lock[n][l] := false;
  unlock_msg[n][l] := true;
endrule;endruleset;

ruleset n : node; l : lock do
rule "recv_unlock"
  unlock_msg[n][l] = true
==>
begin
  unlock_msg[n][l] := false;
  server_holds_lock[l] := true;
endrule;endruleset;

invariant "Onelink"
forall n1 : node do forall n2 : node do forall l : lock do
  n1 != n2 ->
    !(holds_lock[n1][l] = true & holds_lock[n2][l] = true)
end  end end;




