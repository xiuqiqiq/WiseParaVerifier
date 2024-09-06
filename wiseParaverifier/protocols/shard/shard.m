const
    KEYNUMS : 1;
    VALUENUMS : 2;
    NODENUMS : 2;

type
    key: scalarset(KEYNUMS);
    value: scalarset(VALUENUMS);
    node: scalarset(NODENUMS);
    table_idx : array [value] of boolean;
    table_idx_idx : array [key] of table_idx;
    owner_idx : array [key] of boolean;
    transfer_msg_idx : array [value] of boolean;
    transfer_msg_idx_idx : array [key] of transfer_msg_idx;

var
    table : array [node] of table_idx_idx;
    owner : array [node] of owner_idx;
    transfer_msg : array [node] of transfer_msg_idx_idx;


ruleset k : key; n1: node do
startstate "Init"
  for v : value do
  table[n1][k][v] := false;
  transfer_msg[n1][k][v] := false;
  endfor;
  owner[n1][k] := false;
endstartstate;
endruleset;

ruleset k : key; v : value; n_old : node; n_new : node do
rule "reshard"
  table[n_old][k][v] = true
==>
begin
  table[n_old][k][v] := false;
  owner[n_old][k] := false;
  transfer_msg[n_new][k][v] := true;
endrule;endruleset;

ruleset n : node;k : key; v : value do
rule "recv_transfer_msg"
  transfer_msg[n][k][v] = true
==>
begin
  transfer_msg[n][k][v] := false;
  table[n][k][v] := true;
  owner[n][k] := true;
endrule;endruleset;

ruleset n : node;k : key; v : value do
rule "put"
  owner[n][k] = true
==>
begin
  for p : value do
    if p=v then
      table[n][k][p] := true;
    else
      table[n][k][p] := false;
    end;
  end;
endrule;endruleset;

invariant "OnenodeValue"
forall n1 : node do forall n2 : node do forall v1 : value do forall v2 : value do forall k : key do
  n1 != n2 & v1 != v2 ->
    !(table[n1][k][v1] = true & table[n2][k][v2] = true)
end  end end end end;
