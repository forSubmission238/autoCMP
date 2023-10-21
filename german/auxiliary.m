invariant "Lemma_1"
  forall p : NODE do forall i : NODE do
    Chan3[i].Cmd = InvAck & CurCmd != Empty & ExGntd = true ->
    forall j : NODE do
      j != i -> Cache[j].State != E &
                Chan2[j].Cmd != GntE &
                Chan3[j].Cmd != InvAck
end
end 
end;
