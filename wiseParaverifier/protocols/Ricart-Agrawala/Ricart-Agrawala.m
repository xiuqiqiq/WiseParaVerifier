const
    NODENUMS : 2;

type
    NODE: scalarset(NODENUMS);

var
    requested : array [NODE] of array [NODE] of boolean;
    replied : array [NODE] of array [NODE] of boolean;

    holds : array [NODE] of boolean;

ruleset i: NODE do
startstate "Init"
  holds[i] := false;
  for h : NODE do
  requested[i][h] := false;
  replied[i][h] := false;
  end;
endstartstate;
endruleset;

ruleset requester : NODE; responder : NODE do
rule "request"
  requester != responder &
  requested[requester][responder] = false
==>
begin
  requested[requester][responder] := true;
endrule;endruleset;

ruleset requester : NODE; responder : NODE do
rule "reply"
  requester != responder &
  replied[requester][responder] = false &
  holds[responder] = false &
  replied[responder][requester] = false &
  requested[requester][responder] = true
==>
begin
  requested[requester][responder] := false;
  replied[requester][responder] := true;
endrule;endruleset;

ruleset requester : NODE do
rule "enter"
  forall n : NODE do requester != n -> replied[requester][n] = true end
==>
begin
  holds[requester] := true;
endrule;endruleset;

ruleset requester : NODE do
rule "leave"
  holds[requester] = true
==>
begin
  holds[requester] := false;
  for n : NODE do
    replied[requester][n] := false;
  end;
endrule;endruleset;

invariant "Oneholds"
forall i : NODE do forall j : NODE do
i != j ->
    !(holds[i] = true & holds[j] = true)
end  end;
