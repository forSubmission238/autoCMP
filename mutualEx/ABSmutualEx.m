const

  NODENUMS : 2;

type

  state : enum {I, T, C, E};

  NODE : scalarset(NODENUMS);

var

  n : array [NODE] of state;

  x : boolean;

startstate "Init"
  for i : NODE do
    n[i] := I;
  end;
  x := true;
endstartstate;

ruleset i : NODE do
rule "Try"
  n[i] = I
==>
begin
  n[i] := T;
endrule;
endruleset;

ruleset i : NODE do
rule "Crit"
  n[i] = T &
  x = true
==>
begin
  n[i] := C;
  x := false;
endrule;
endruleset;

ruleset i : NODE do
rule "Exit"
  n[i] = C
==>
begin
  n[i] := E;
endrule;
endruleset;

ruleset i : NODE do
rule "Idle"
  n[i] = E
==>
begin
  n[i] := I;
  x := true;
endrule;
endruleset;

invariant "mutualEx"
  forall i : NODE do
    forall j : NODE do
      i != j ->
      (  n[i] = C ->
          n[j] != C)
    end
  end;


rule "ABS_Crit"
  x = true
==>
begin
  x := false;
endrule;

rule "ABS_Idle"
  forall j : NODE do
    n[j] != C &
    n[j] != E
  end
==>
begin
  x := true;
endrule;

invariant "Lemma_1"
  forall p : NODE do
    forall i : NODE do
      n[i] = E ->
        forall j : NODE do
          j != i ->
            n[j] != C &
            n[j] != E
        end
    end
  end;


