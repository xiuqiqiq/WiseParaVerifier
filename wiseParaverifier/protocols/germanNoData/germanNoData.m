const

  NODE_NUM : 2;

type

  NODE : scalarset(NODE_NUM);

  OTHER : enum {other_em};

  CACHE_STATE : enum {i_em, s_em, e_em};

  CACHE : record
    State : CACHE_STATE;
  end;

  MSG_CMD: enum {empty_em, reqs_em, reqe_em, inv_em, invack_em, gnts_em, gnte_em};

  MSG: record
    Cmd : MSG_CMD;
  end;


var

  cache : array [NODE] of CACHE;
  chan1 : array [NODE] of MSG;
  chan2 : array [NODE] of MSG;
  chan3 : array [NODE] of MSG;
  invSet : array [NODE] of boolean;
  shrSet : array [NODE] of boolean;
  exGntd : boolean;
  curCmd : MSG_CMD;

startstate "Init"
begin
  for i : NODE do
    chan1[i].Cmd := empty_em;
    chan2[i].Cmd := empty_em;
    chan3[i].Cmd := empty_em;
    cache[i].State := i_em;
    invSet[i] := false;
    shrSet[i] := false;
  end;
  exGntd := false;
  curCmd := empty_em;
endstartstate;

ruleset i : NODE do
rule "RecvGntE"
  chan2[i].Cmd = gnte_em
==>
begin
  cache[i].State := e_em;
  chan2[i].Cmd := empty_em;
endrule;
endruleset;

ruleset i : NODE do
rule "RecvGntS"
  chan2[i].Cmd = gnts_em
==>
begin
  cache[i].State := s_em;
  chan2[i].Cmd := empty_em;
endrule;
endruleset;

ruleset i : NODE do
rule "SendGntE"
  curCmd = reqe_em &
  chan2[i].Cmd = empty_em &
  exGntd = false &
  forall j : NODE do
    shrSet[j] = false
  end
==>
begin
  chan2[i].Cmd := gnte_em;
  shrSet[i] := true;
  exGntd := true;
  curCmd := empty_em;
endrule;
endruleset;

ruleset i : NODE do
rule "SendGntS"
  curCmd = reqs_em &
  chan2[i].Cmd = empty_em &
  exGntd = false
==>
begin
  chan2[i].Cmd := gnts_em;
  shrSet[i] := true;
  curCmd := empty_em;
endrule;
endruleset;

ruleset i : NODE do
rule "RecvInvAck1"
  chan3[i].Cmd = invack_em &
  curCmd != empty_em &
  exGntd = true
==>
begin
  chan3[i].Cmd := empty_em;
  shrSet[i] := false;
  exGntd := false;
endrule;
endruleset;

ruleset i : NODE do
rule "RecvInvAck2"
  chan3[i].Cmd = invack_em &
  curCmd != empty_em &
  exGntd = false
==>
begin
  chan3[i].Cmd := empty_em;
  shrSet[i] := false;
endrule;
endruleset;

ruleset i : NODE do
rule "SendInvAck"
  chan2[i].Cmd = inv_em &
  chan3[i].Cmd = empty_em
==>
begin
  chan2[i].Cmd := empty_em;
  chan3[i].Cmd := invack_em;
  cache[i].State := i_em;
endrule;
endruleset;

ruleset i : NODE do
rule "SendInv"
  chan2[i].Cmd = empty_em &
  invSet[i] = true &
  ( curCmd = reqe_em | curCmd = reqs_em & exGntd = true )
==>
begin
  chan2[i].Cmd := inv_em;
  invSet[i] := false;
endrule;
endruleset;

ruleset i : NODE do
rule "RecvReqE"
  curCmd = empty_em &
  chan1[i].Cmd = reqe_em
==>
begin
  curCmd := reqe_em;
  chan1[i].Cmd := empty_em;
  for j : NODE do
    invSet[j] := shrSet[j];
  end;
endrule;
endruleset;

ruleset i : NODE do
rule "RecvReqS"
  curCmd = empty_em &
  chan1[i].Cmd = reqs_em
==>
begin
  curCmd := reqs_em;
  chan1[i].Cmd := empty_em;
  for j : NODE do
    invSet[j] := shrSet[j];
  end;
endrule;
endruleset;

ruleset i : NODE do
rule "SendReqE"
  chan1[i].Cmd = empty_em &
  (cache[i].State = i_em | cache[i].State = s_em)
==>
begin
  chan1[i].Cmd := reqe_em;
endrule;
endruleset;

ruleset i : NODE do
rule "SendReqS"
  chan1[i].Cmd = empty_em &
  cache[i].State = i_em
==>
begin
  chan1[i].Cmd := reqs_em;
endrule;
endruleset;




invariant "CntrlProp"
  forall i : NODE do forall j : NODE do
    i != j ->
         (cache[i].State = e_em -> cache[j].State = i_em) &
              (cache[i].State = s_em -> cache[j].State = i_em | cache[j].State = s_em)
  end end;

