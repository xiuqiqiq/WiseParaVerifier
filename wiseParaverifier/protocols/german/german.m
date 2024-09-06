	
const


  NODE_NUM : 2;
  DATA_NUM : 2;

type

  NODE : scalarset(NODE_NUM);
  DATA : scalarset(DATA_NUM);

  CACHE_STATE : enum{i_em,s_em,e_em};
  CACHE : record
    State : CACHE_STATE;
    Data : DATA;
  end;


  MSG_CMD1: enum {empty1_em, reqs_em, reqe_em};

  MSG_CMD2: enum {empty2_em, inv_em, gnts_em, gnte_em};

  MSG_CMD3: enum {empty3_em, invack_em};

  MSG1 : record
    Cmd : MSG_CMD1;
    Data : DATA;
  end;

  MSG2 : record
    Cmd : MSG_CMD2;
    Data : DATA;
  end;

  MSG3 : record
    Cmd : MSG_CMD3;
    Data : DATA;
  end;


var

  cache : array [NODE] of CACHE;
  chan1 : array [NODE] of MSG1;
  chan2 : array [NODE] of MSG2;
  chan3 : array [NODE] of MSG3;
  invSet : array [NODE] of boolean;
  shrSet : array [NODE] of boolean;
  exGntd : boolean;
  curCmd : MSG_CMD1;
  curPtr : NODE;
  memData : DATA;
  auxData : DATA;

ruleset d : DATA do 
startstate "Init"
  for i : NODE do
    chan1[i].Cmd := empty1_em;
    chan2[i].Cmd := empty2_em;
    chan3[i].Cmd := empty3_em;
    chan1[i].Data := d;
    chan2[i].Data := d;
    chan3[i].Data := d;
    cache[i].State := i_em;
    cache[i].Data := d;
    invSet[i] := false;
    shrSet[i] := false;
  end;
  memData := d;
  auxData := d;
  exGntd := false;
  curCmd := empty1_em;
endstartstate;
endruleset;

ruleset  i : NODE do
rule "RecvGntE"
  chan2[i].Cmd = gnte_em
==>
begin
  cache[i].State := e_em;
  cache[i].Data := chan2[i].Data;
  chan2[i].Cmd := empty2_em;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvGntS"
  chan2[i].Cmd = gnts_em
==>
begin
  cache[i].State := s_em;
  cache[i].Data := chan2[i].Data;
  chan2[i].Cmd := empty2_em;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendGntE"
  curCmd = reqe_em &
  curPtr = i &
  chan2[i].Cmd = empty2_em &
  exGntd = false &
  forall j : NODE do
    shrSet[j] = false
  end
==>
begin
  chan2[i].Cmd := gnte_em;
  chan2[i].Data := memData;
  shrSet[i] := true;
  exGntd := true;
  curCmd := empty1_em;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendGntS"
  curCmd = reqs_em &
  curPtr = i &
  chan2[i].Cmd = empty2_em &
  exGntd = false
==>
begin
  chan2[i].Cmd := gnts_em;
  chan2[i].Data := memData;
  shrSet[i] := true;
  curCmd := empty1_em;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvInvAck1"
  chan3[i].Cmd = invack_em &
  curCmd != empty1_em &
  exGntd = true
==>
begin
  chan3[i].Cmd := empty3_em;
  shrSet[i] := false;
  exGntd := false;
  memData := chan3[i].Data;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvInvAck2"
  chan3[i].Cmd = invack_em &
  curCmd != empty1_em &
  exGntd != true
==>
begin
  chan3[i].Cmd := empty3_em;
  shrSet[i] := false;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendInvAck1"
  chan2[i].Cmd = inv_em &
  chan3[i].Cmd = empty3_em &
  cache[i].State = e_em
==>
begin
  chan2[i].Cmd := empty2_em;
  chan3[i].Cmd := invack_em;
  chan3[i].Data := cache[i].Data;
  cache[i].State := i_em;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendInvAck2"
  chan2[i].Cmd = inv_em &
  chan3[i].Cmd = empty3_em &
  cache[i].State != e_em
==>
begin
  chan2[i].Cmd := empty2_em;
  chan3[i].Cmd := invack_em;
  cache[i].State := i_em;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendInv1"
  chan2[i].Cmd = empty2_em &
  invSet[i] = true &
  curCmd = reqe_em
==>
begin
  chan2[i].Cmd := inv_em;
  invSet[i] := false;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendInv2"
  chan2[i].Cmd = empty2_em &
  invSet[i] = true &
  curCmd = reqs_em &
  exGntd = true
==>
begin
  chan2[i].Cmd := inv_em;
  invSet[i] := false;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvReqE"
  curCmd = empty1_em &
  chan1[i].Cmd = reqe_em
==>
begin
  curCmd := reqe_em;
  curPtr := i;
  chan1[i].Cmd := empty1_em;
  for j : NODE do
    invSet[j] := shrSet[j];
  endfor;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvReqS"
  curCmd = empty1_em &
  chan1[i].Cmd = reqs_em
==>
begin
  curCmd := reqs_em;
  curPtr := i;
  chan1[i].Cmd := empty1_em;
  for j : NODE do
    invSet[j] := shrSet[j];
  endfor;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendReqE1"
  chan1[i].Cmd = empty1_em &
  cache[i].State = i_em
==>
begin
  chan1[i].Cmd := reqe_em;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendReqE2"
  chan1[i].Cmd = empty1_em &
  cache[i].State = s_em
==>
begin
  chan1[i].Cmd := reqe_em;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendReqS"
  chan1[i].Cmd = empty1_em &
  cache[i].State = i_em
==>
begin
  chan1[i].Cmd := reqs_em;
endrule;
endruleset;

ruleset  d : DATA; i : NODE do
rule "Store"
  cache[i].State = e_em
==>
begin
  cache[i].Data := d;
  auxData := d;
endrule;
endruleset;


invariant "CntrlProp"
  forall i : NODE do
    forall j : NODE do
    i != j ->
      ((cache[i].State = e_em ->
      cache[j].State = i_em) &
      (cache[i].State = s_em ->
      (cache[j].State = i_em |
      cache[j].State = s_em)))
    end
  end;


invariant "DataProp"
  ((exGntd = false ->
  memData = auxData) &
  forall i : NODE do
    (cache[i].State != i_em ->
    cache[i].Data = auxData)  
 end);