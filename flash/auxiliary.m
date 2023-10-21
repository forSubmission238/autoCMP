invariant "Lemma_1"
forall src : NODE do   forall dst : NODE do
    Sta.Proc[dst].CacheState = CACHE_E ->
    forall p : NODE do p != dst ->
    Sta.Dir.Dirty & Sta.WbMsg.Cmd != WB_Wb & Sta.ShWbMsg.Cmd != SHWB_ShWb &
    Sta.Proc[p].CacheState != CACHE_E &
    Sta.HomeProc.CacheState != CACHE_E &
    Sta.HomeUniMsg.Cmd != UNI_Put &
    Sta.UniMsg[p].Cmd != UNI_PutX &
    Sta.HomeUniMsg.Cmd != UNI_PutX  
end  
end 
end;

invariant "Lemma_2a"
  forall src : NODE do forall dst : NODE do
    src != dst &
    Sta.UniMsg[src].Cmd = UNI_Get &
    !Sta.UniMsg[src].HomeProc & Sta.UniMsg[src].Proc = dst ->
    Sta.Dir.Pending & !Sta.Dir.Local &
    !Sta.HomePendReqSrc & Sta.PendReqSrc = src & Sta.FwdCmd = UNI_Get
end 
end;

invariant "Lemma_2b"
  forall src : NODE do forall dst : NODE do
    Sta.HomeUniMsg.Cmd = UNI_Get &
    !Sta.HomeUniMsg.HomeProc & Sta.HomeUniMsg.Proc = dst ->
    Sta.Dir.Pending & !Sta.Dir.Local &
    Sta.HomePendReqSrc & Sta.FwdCmd = UNI_Get
end 
end;

invariant "Lemma_3a"
  forall src : NODE do forall dst : NODE do
    src != dst &
    Sta.UniMsg[src].Cmd = UNI_GetX &
    !Sta.UniMsg[src].HomeProc & Sta.UniMsg[src].Proc = dst ->
    Sta.Dir.Pending & !Sta.Dir.Local &
    !Sta.HomePendReqSrc & Sta.PendReqSrc = src & Sta.FwdCmd = UNI_GetX
end 
end;

invariant "Lemma_3b"
  forall src : NODE do forall dst : NODE do
    Sta.HomeUniMsg.Cmd = UNI_GetX &
    !Sta.HomeUniMsg.HomeProc & Sta.HomeUniMsg.Proc = dst ->
    Sta.Dir.Pending & !Sta.Dir.Local &
    Sta.HomePendReqSrc & Sta.FwdCmd = UNI_GetX
end 
end;

invariant "Lemma_4"
  forall dst : NODE do forall src : NODE do 
    Sta.InvMsg[src].Cmd = INV_InvAck ->
    forall q : NODE do q != src ->
    Sta.Collecting &
    Sta.NakcMsg.Cmd = NAKC_None & Sta.ShWbMsg.Cmd = SHWB_None &
    (( Sta.UniMsg[q].Cmd = UNI_Get | Sta.UniMsg[q].Cmd = UNI_GetX ->
      Sta.UniMsg[q].HomeProc ) &
    ( Sta.UniMsg[q].Cmd = UNI_PutX ->
      Sta.UniMsg[q].HomeProc & !Sta.HomePendReqSrc & Sta.PendReqSrc = q ))
end
end 
end;
