invariant "Lemma_1"
    forall p : NODE do
        forall i : NODE do
            n[i] = E ->
            forall j : NODE do j != i -> n[j] != C & n[j] != E 
        end
    end
end;
