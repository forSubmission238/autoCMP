invariant "Lemma_0"
  forall p : NODE do forall i : NODE do
    state[i] = MM ->
    forall j : NODE do j != i -> state[j] != MM 
end
end 
end;

invariant "Lemma_3"
  forall p : NODE do forall i : NODE do
    state[i] = MM ->
    forall j : NODE do j != i -> state[j] != E 
end
end 
end;

invariant "Lemma_4"
  forall p : NODE do forall i : NODE do
    state[i] = S ->
    forall j : NODE do j != i -> state[j] != MM 
end
end 
end;

invariant "Lemma_5"
  forall p : NODE do forall i : NODE do
    state[i] = S ->
    forall j : NODE do j != i -> state[j] != E 
end
end 
end;

invariant "Lemma_6"
  forall p : NODE do forall i : NODE do
    state[i] = MM ->
    forall j : NODE do j != i -> state[j] = I 
end
end 
end;

invariant "Lemma_9"
  forall p : NODE do forall i : NODE do
    state[i] = MM ->
    forall j : NODE do j != i -> state[j] != S
end
end 
end;
