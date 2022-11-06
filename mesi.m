
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

rule "ABS_t2"
  true
==>
begin
  for j : NODE do
    if (state[j] = I) then
      state[j] := I;
    else
      state[j] := S;
    end;
  end;
endrule;

rule "ABS_t3"
  forall j : NODE do
    state[j] != E            -- Lemma_5
  end &
  forall j : NODE do
    state[j] != MM           -- Lemma_4
  end
==>
begin
  for j : NODE do
    state[j] := I;
  end;
endrule;

rule "ABS_t4"
  forall j : NODE do
	state[j] != S            -- Lemma_9
  end &
  forall j : NODE do
	state[j] != E            -- Lemma_3
  end &
  forall j : NODE do
	state[j] = I             -- Lemma_6
  end &
  forall j : NODE do
	state[j] != MM           -- Lemma_0
  end
==>
begin
  for j : NODE do
    state[j] := I;
  end;
endrule;

invariant "Lemma_0"
  forall p : NODE do forall i : NODE do
    state[i] = MM ->
    forall j : NODE do j != i -> state[j] != MM end
  end end;

invariant "Lemma_3"
  forall p : NODE do forall i : NODE do
    state[i] = MM ->
    forall j : NODE do j != i -> state[j] != E end
  end end;

invariant "Lemma_4"
  forall p : NODE do forall i : NODE do
    state[i] = S ->
    forall j : NODE do j != i -> state[j] != MM end
  end end;

invariant "Lemma_5"
  forall p : NODE do forall i : NODE do
    state[i] = S ->
    forall j : NODE do j != i -> state[j] != E end
  end end;

invariant "Lemma_6"
  forall p : NODE do forall i : NODE do
    state[i] = MM ->
    forall j : NODE do j != i -> state[j] = I end
  end end;

invariant "Lemma_9"
  forall p : NODE do forall i : NODE do
    state[i] = MM ->
    forall j : NODE do j != i -> state[j] != S end
  end end;
