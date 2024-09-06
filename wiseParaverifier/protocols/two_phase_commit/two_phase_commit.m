const
    NODENUMS : 2;

type
    NODE: scalarset(NODENUMS);

var
    vote_yes : array [NODE] of boolean;
    vote_no : array [NODE] of boolean;
    alive : array [NODE] of boolean;
    go_commit : array [NODE] of boolean;
    go_abort : array [NODE] of boolean;
    decide_commit : array [NODE] of boolean;
    decide_abort : array [NODE] of boolean;

    abort_flag : boolean;


startstate "Init"
for i: NODE do
  vote_yes[i] := false;
  vote_no[i] := false;
  alive[i] := true;
  go_commit[i] := false;
  go_abort[i] := false;
  decide_commit[i] := false;
  decide_abort[i] := false;
  abort_flag := false;
end;
endstartstate;


ruleset i : NODE
do rule "vote1"
  alive[i] = true & vote_no[i] = false & decide_commit[i] = false & decide_abort[i] = false
==>
begin
  vote_yes[i] := true;
endrule;endruleset;

ruleset i : NODE
do rule "vote2"
  alive[i] = true & vote_yes[i] = false & decide_commit[i] = false & decide_abort[i] = false
==>
begin
  vote_no[i] := true;
  abort_flag := true;
  decide_abort[i] := true;
endrule;endruleset;

ruleset i : NODE
do rule "fail"
  alive[i] = true
==>
begin
  alive[i] := false;
  abort_flag := true;
endrule;endruleset;

rule "go1"
  forall p : NODE do go_commit[p] = false & go_abort[p] = false & vote_yes[p] = true end
==>
begin
  for p : NODE do
    go_commit[p] := true;
  end;
endrule;

rule "go2"
  forall i : NODE do go_commit[i] = false & go_abort[i] = false end & !forall p : NODE do vote_no[p] = false & alive[p] = true end
==>
begin
  for p : NODE do
    go_abort[p] := true;
  end;
endrule;

ruleset i : NODE
do rule "commit"
  alive[i] = true & go_commit[i] = true
==>
begin
  decide_commit[i] := true;
endrule;endruleset;

ruleset i : NODE
do rule "abort"
  alive[i] = true & go_abort[i] = true
==>
begin
  decide_abort[i] := true;
endrule;endruleset;


invariant "commit_abort"
forall i : NODE do forall j : NODE do
    !(decide_commit[i] = true & decide_abort[j] = true)
end  end;

invariant "commit_vote_yes"
forall i : NODE do forall j : NODE do
    !(decide_commit[i] = true & vote_yes[j] != true)
end  end;

invariant "abort"
forall i : NODE do forall j : NODE do
    !(decide_abort[i] = true & abort_flag != true)
end  end;