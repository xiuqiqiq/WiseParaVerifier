const 
    NODENUMS : 2;
    DATANUMS: 2;
			
type 
     state : enum{i_em, t_em, c_em, e_em};

     DATA: scalarset(DATANUMS);
     NODE: scalarset(NODENUMS);

     status : record 
       st:state; 
       data: DATA; 
      end;

var 
    n : array [NODE] of status;

    x : boolean; 
    
    auxDATA : DATA;
    
    memDATA: DATA;


ruleset d : DATA do
startstate "Init"
 for i: NODE do
    n[i].st := i_em; 
    n[i].data:=d;
  endfor;
  x := true;
  auxDATA := d;
  memDATA:=d;
endstartstate;
endruleset;


ruleset i : NODE do
rule "Try" 
      n[i].st = i_em 
==>
begin
      n[i].st := t_em;
endrule;endruleset;


ruleset i : NODE do
rule "Crit"
      n[i].st = t_em & 
      x = true 
==>
begin
      n[i].st := c_em;
      x := false;
      n[i].data := memDATA; 
endrule;endruleset;


ruleset i : NODE do
rule "Exit"
      n[i].st = c_em 
==>
begin
      n[i].st := e_em;
endrule;endruleset;
      
 
ruleset i : NODE do
rule "Idle"
      n[i].st = e_em 
==>
begin 
      n[i].st := i_em;
      x := true; 
      memDATA := n[i].data; 
endrule;endruleset;

ruleset i : NODE; d : DATA do rule "Store"
	n[i].st = c_em
==>
begin
      auxDATA := d;
      n[i].data := d; 
endrule;endruleset;    


invariant "coherence"
  forall i : NODE do
    forall j : NODE do
    i != j ->
      !(n[i].st = c_em & n[j].st = c_em)
end   end;


invariant "c51"
forall i : NODE do
  !(n[i].st= c_em & n[i].data != auxDATA)
end;