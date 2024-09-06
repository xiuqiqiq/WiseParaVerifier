const
    SERNUMS : 1;
    CLINUMS : 2;

type
    client: scalarset(CLINUMS);
    server: scalarset(SERNUMS);
    link_idx : array [server] of boolean;

var
    link : array [client] of link_idx;
    semaphore : array [server] of boolean;



ruleset i : client do
startstate "Init"
  for h : server do
    semaphore[h] := true;
    link[i][h] := false;
  end;
endstartstate;
endruleset;


ruleset x : client; y : server do
rule "connect"
  semaphore[y] = true
==>
begin
  link[x][y] := true;
  semaphore[y] := false;
endrule;endruleset;

ruleset x : client; y : server do
rule "disconnect"
  link[x][y] = true
==>
begin
  link[x][y] := false;
  semaphore[y] := true;
endrule;endruleset;

invariant "Onelink"
forall i : client do forall j : client do forall k : server do
  i != j ->
    !(link[i][k] = true & link[j][k] = true)
end  end end;
