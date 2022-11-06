
const

  NODE_NUM : 2;

type

  NODE : scalarset(NODE_NUM);

  OTHER : enum {Other};

  ABS_NODE : union {NODE, OTHER};

  LOCATION: enum {MM, E, S, I};

var

  state : array [NODE] of LOCATION;

startstate "Init"
begin
  for i : NODE do
    state[i] := I;
  end;
endstartstate;

ruleset i : NODE do
rule "t1"
  state[i] = E
==>
begin
  state[i] := MM;
endrule;
endruleset;

ruleset i : NODE do
rule "t2"
  state[i] = I
==>
begin
  state[i] := S;
  for j : NODE do
    if (j != i) then
      if (state[j] = I) then
        state[j] := I;
      else
        state[j] := S;
      end;
    end;
  end;
endrule;
endruleset;

ruleset i : NODE do
rule "t3"
  state[i] = S
==>
begin
  state[i] := E;
  for j : NODE do
    if (j != i) then
      state[j] := I;
    end;
  end;
endrule;
endruleset;

ruleset i : NODE do
rule "t4"
  state[i] = MM
==>
begin
  state[i] := E;
  for j : NODE do
    if (j != i) then
      state[j] := I;
    end;
  end;
endrule;
endruleset;

---- Invariant properties ----

invariant "Mesi"
  forall i : NODE do forall j : NODE do
    i != j -> (state[i] = MM -> state[j] != MM)
  end end;
