
theory Flash
  imports ECMP
begin

definition CACHE_I :: "scalrValueType" where [simp]:
 "CACHE_I \<equiv> enum ''CACHE_STATE'' ''CACHE_I''"

definition CACHE_S :: "scalrValueType" where [simp]:
 "CACHE_S \<equiv> enum ''CACHE_STATE'' ''CACHE_S''"

definition CACHE_E :: "scalrValueType" where [simp]:
 "CACHE_E \<equiv> enum ''CACHE_STATE'' ''CACHE_E''"

definition NODE_None :: "scalrValueType" where [simp]:
 "NODE_None \<equiv> enum ''NODE_CMD'' ''NODE_None''"

definition NODE_Get :: "scalrValueType" where [simp]:
 "NODE_Get \<equiv> enum ''NODE_CMD'' ''NODE_Get''"

definition NODE_GetX :: "scalrValueType" where [simp]:
 "NODE_GetX \<equiv> enum ''NODE_CMD'' ''NODE_GetX''"

definition UNI_None :: "scalrValueType" where [simp]:
 "UNI_None \<equiv> enum ''UNI_CMD'' ''UNI_None''"

definition UNI_Get :: "scalrValueType" where [simp]:
 "UNI_Get \<equiv> enum ''UNI_CMD'' ''UNI_Get''"

definition UNI_GetX :: "scalrValueType" where [simp]:
 "UNI_GetX \<equiv> enum ''UNI_CMD'' ''UNI_GetX''"

definition UNI_Put :: "scalrValueType" where [simp]:
 "UNI_Put \<equiv> enum ''UNI_CMD'' ''UNI_Put''"

definition UNI_PutX :: "scalrValueType" where [simp]:
 "UNI_PutX \<equiv> enum ''UNI_CMD'' ''UNI_PutX''"

definition UNI_Nak :: "scalrValueType" where [simp]:
 "UNI_Nak \<equiv> enum ''UNI_CMD'' ''UNI_Nak''"

definition INV_None :: "scalrValueType" where [simp]:
 "INV_None \<equiv> enum ''INV_CMD'' ''INV_None''"

definition INV_Inv :: "scalrValueType" where [simp]:
 "INV_Inv \<equiv> enum ''INV_CMD'' ''INV_Inv''"

definition INV_InvAck :: "scalrValueType" where [simp]:
 "INV_InvAck \<equiv> enum ''INV_CMD'' ''INV_InvAck''"

definition RP_None :: "scalrValueType" where [simp]:
 "RP_None \<equiv> enum ''RP_CMD'' ''RP_None''"

definition RP_Replace :: "scalrValueType" where [simp]:
 "RP_Replace \<equiv> enum ''RP_CMD'' ''RP_Replace''"

definition WB_None :: "scalrValueType" where [simp]:
 "WB_None \<equiv> enum ''WB_CMD'' ''WB_None''"

definition WB_Wb :: "scalrValueType" where [simp]:
 "WB_Wb \<equiv> enum ''WB_CMD'' ''WB_Wb''"

definition SHWB_None :: "scalrValueType" where [simp]:
 "SHWB_None \<equiv> enum ''SHWB_CMD'' ''SHWB_None''"

definition SHWB_ShWb :: "scalrValueType" where [simp]:
 "SHWB_ShWb \<equiv> enum ''SHWB_CMD'' ''SHWB_ShWb''"

definition SHWB_FAck :: "scalrValueType" where [simp]:
 "SHWB_FAck \<equiv> enum ''SHWB_CMD'' ''SHWB_FAck''"

definition NAKC_None :: "scalrValueType" where [simp]:
 "NAKC_None \<equiv> enum ''NAKC_CMD'' ''NAKC_None''"

definition NAKC_Nakc :: "scalrValueType" where [simp]:
 "NAKC_Nakc \<equiv> enum ''NAKC_CMD'' ''NAKC_Nakc''"

definition true :: "scalrValueType" where [simp]:
 "true \<equiv> boolV True"

definition false :: "scalrValueType" where [simp]:
 "false \<equiv> boolV False"

primrec env :: "nat => envType" where
"env N (Ident n) = (if Ident n = Ident ''Sta.Dir.Pending'' then
  boolType
else
  if Ident n = Ident ''Sta.Dir.Local'' then
    boolType
  else
    if Ident n = Ident ''Sta.Dir.Dirty'' then
      boolType
    else
      if Ident n = Ident ''Sta.Dir.HeadVld'' then
        boolType
      else
        if Ident n = Ident ''Sta.Dir.ShrVld'' then
          boolType
        else
          if Ident n = Ident ''Sta.Dir.HeadPtr'' then
            indexType
          else
            if Ident n = Ident ''Sta.WbMsg.Cmd'' then
              enumType
            else
              if Ident n = Ident ''Sta.WbMsg.Proc'' then
                indexType
              else
                if Ident n = Ident ''Sta.ShWbMsg.Cmd'' then
                  enumType
                else
                  if Ident n = Ident ''Sta.ShWbMsg.Proc'' then
                    indexType
                  else
                    if Ident n = Ident ''Sta.NakcMsg.Cmd'' then
                      enumType
                    else
                      if Ident n = Ident ''Sta.HomeProc.ProcCmd'' then
                        enumType
                      else
                        if Ident n = Ident ''Sta.HomeProc.InvMarked'' then
                          boolType
                        else
                          if Ident n = Ident ''Sta.HomeProc.CacheState'' then
                            enumType
                          else
                            if Ident n = Ident ''Sta.HomeUniMsg.Cmd'' then
                              enumType
                            else
                              if Ident n = Ident ''Sta.HomeUniMsg.HomeProc'' then
                                boolType
                              else
                                if Ident n = Ident ''Sta.HomeUniMsg.Proc'' then
                                  indexType
                                else
                                  if Ident n = Ident ''Sta.HomePendReqSrc'' then
                                    boolType
                                  else
                                    if Ident n = Ident ''Sta.Collecting'' then
                                      boolType
                                    else
                                      if Ident n = Ident ''Sta.FwdCmd'' then
                                        enumType
                                      else
                                        if Ident n = Ident ''Sta.PendReqSrc'' then
                                          indexType
                                        else
                                          anyType
                                        
                                      
                                    
                                  
                                
                              
                            
                          
                        
                      
                    
                  
                
              
            
          
        
      
    
  
)"|
"env N (Para n p) = (if Para n p = Para ''Sta.Proc.ProcCmd'' p \<and> (p \<le> N) then
  enumType
else
  if Para n p = Para ''Sta.Proc.InvMarked'' p \<and> (p \<le> N) then
    boolType
  else
    if Para n p = Para ''Sta.Proc.CacheState'' p \<and> (p \<le> N) then
      enumType
    else
      if Para n p = Para ''Sta.Dir.ShrSet'' p \<and> (p \<le> N) then
        boolType
      else
        if Para n p = Para ''Sta.Dir.InvSet'' p \<and> (p \<le> N) then
          boolType
        else
          if Para n p = Para ''Sta.InvMsg.Cmd'' p \<and> (p \<le> N) then
            enumType
          else
            if Para n p = Para ''Sta.RpMsg.Cmd'' p \<and> (p \<le> N) then
              enumType
            else
              if Para n p = Para ''Sta.UniMsg.Cmd'' p \<and> (p \<le> N) then
                enumType
              else
                if Para n p = Para ''Sta.UniMsg.HomeProc'' p \<and> (p \<le> N) then
                  boolType
                else
                  if Para n p = Para ''Sta.UniMsg.Proc'' p \<and> (p \<le> N) then
                    indexType
                  else
                    anyType
                  
                
              
            
          
        
      
    
  
)"|
"env N dontCareVar = anyType"

lemma env_simp : 
             "[|p <= N|] 
                 ==> env N (Para ''Sta.Proc.ProcCmd'' p) = enumType"
                 

"[|p <= N|] 
                 ==> env N (Para ''Sta.Proc.InvMarked'' p) = boolType"
                 

"[|p <= N|] 
                 ==> env N (Para ''Sta.Proc.CacheState'' p) = enumType"
                 

"[|p <= N|] 
                 ==> env N (Para ''Sta.Dir.ShrSet'' p) = boolType"
                 

"[|p <= N|] 
                 ==> env N (Para ''Sta.Dir.InvSet'' p) = boolType"
                 

"[|p <= N|] 
                 ==> env N (Para ''Sta.InvMsg.Cmd'' p) = enumType"
                 

"[|p <= N|] 
                 ==> env N (Para ''Sta.RpMsg.Cmd'' p) = enumType"
                 

"[|p <= N|] 
                 ==> env N (Para ''Sta.UniMsg.Cmd'' p) = enumType"
                 

"[|p <= N|] 
                 ==> env N (Para ''Sta.UniMsg.HomeProc'' p) = boolType"
                 

"[|p <= N|] 
                 ==> env N (Para ''Sta.UniMsg.Proc'' p) = indexType"
                 

" 
                  env N (Ident ''Sta.Dir.Pending'') = boolType"
                 

" 
                  env N (Ident ''Sta.Dir.Local'') = boolType"
                 

" 
                  env N (Ident ''Sta.Dir.Dirty'') = boolType"
                 

" 
                  env N (Ident ''Sta.Dir.HeadVld'') = boolType"
                 

" 
                  env N (Ident ''Sta.Dir.ShrVld'') = boolType"
                 

" 
                  env N (Ident ''Sta.Dir.HeadPtr'') = indexType"
                 

" 
                  env N (Ident ''Sta.WbMsg.Cmd'') = enumType"
                 

" 
                  env N (Ident ''Sta.WbMsg.Proc'') = indexType"
                 

" 
                  env N (Ident ''Sta.ShWbMsg.Cmd'') = enumType"
                 

" 
                  env N (Ident ''Sta.ShWbMsg.Proc'') = indexType"
                 

" 
                  env N (Ident ''Sta.NakcMsg.Cmd'') = enumType"
                 

" 
                  env N (Ident ''Sta.HomeProc.ProcCmd'') = enumType"
                 

" 
                  env N (Ident ''Sta.HomeProc.InvMarked'') = boolType"
                 

" 
                  env N (Ident ''Sta.HomeProc.CacheState'') = enumType"
                 

" 
                  env N (Ident ''Sta.HomeUniMsg.Cmd'') = enumType"
                 

" 
                  env N (Ident ''Sta.HomeUniMsg.HomeProc'') = boolType"
                 

" 
                  env N (Ident ''Sta.HomeUniMsg.Proc'') = indexType"
                 

" 
                  env N (Ident ''Sta.HomePendReqSrc'') = boolType"
                 

" 
                  env N (Ident ''Sta.Collecting'') = boolType"
                 

" 
                  env N (Ident ''Sta.FwdCmd'') = enumType"
                 

" 
                  env N (Ident ''Sta.PendReqSrc'') = indexType"
                 

"[|p > N|] 
                 ==> env N (Para n p) = anyType"
                 
 
               apply(auto      )    
 
done

definition initSpec0 :: "formula" where [simp]:
 "initSpec0 \<equiv> IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false"

lemma symPreds0 [intro]: 
                  " 
                  symPredSet' N {initSpec0}"
                   apply(auto      )    
 
done

lemma deriveFormInitSpec0 [intro]: 
                  "[|f : {initSpec0}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec1 :: "formula" where [simp]:
 "initSpec1 \<equiv> IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false"

lemma symPreds1 [intro]: 
                  " 
                  symPredSet' N {initSpec1}"
                   apply(auto      )    
 
done

lemma deriveFormInitSpec1 [intro]: 
                  "[|f : {initSpec1}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec2 :: "formula" where [simp]:
 "initSpec2 \<equiv> IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const false"

lemma symPreds2 [intro]: 
                  " 
                  symPredSet' N {initSpec2}"
                   apply(auto      )    
 
done

lemma deriveFormInitSpec2 [intro]: 
                  "[|f : {initSpec2}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec3 :: "formula" where [simp]:
 "initSpec3 \<equiv> IVar (Ident ''Sta.Dir.HeadVld'') =\<^sub>f Const false"

lemma symPreds3 [intro]: 
                  " 
                  symPredSet' N {initSpec3}"
                   apply(auto      )    
 
done

lemma deriveFormInitSpec3 [intro]: 
                  "[|f : {initSpec3}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec4 :: "formula" where [simp]:
 "initSpec4 \<equiv> IVar (Ident ''Sta.Dir.ShrVld'') =\<^sub>f Const false"

lemma symPreds4 [intro]: 
                  " 
                  symPredSet' N {initSpec4}"
                   apply(auto      )    
 
done

lemma deriveFormInitSpec4 [intro]: 
                  "[|f : {initSpec4}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec5 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec5 N \<equiv> (\<exists>\<^sub>fi_0. IVar (Ident ''Sta.Dir.HeadPtr'') =\<^sub>f Const (index i_0)) N"

lemma symPreds5 [intro]: 
                  " 
                  symPredSet' N {initSpec5 N}"
                 unfolding initSpec5_def   apply(rule symPredSetExist)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma deriveFormInitSpec5 [intro]: 
                  "[|f : {initSpec5 N}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec6 :: "formula" where [simp]:
 "initSpec6 \<equiv> IVar (Ident ''Sta.WbMsg.Cmd'') =\<^sub>f Const WB_None"

lemma symPreds6 [intro]: 
                  " 
                  symPredSet' N {initSpec6}"
                   apply(auto      )    
 
done

lemma deriveFormInitSpec6 [intro]: 
                  "[|f : {initSpec6}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec7 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec7 N \<equiv> (\<exists>\<^sub>fi_0. IVar (Ident ''Sta.WbMsg.Proc'') =\<^sub>f Const (index i_0)) N"

lemma symPreds7 [intro]: 
                  " 
                  symPredSet' N {initSpec7 N}"
                 unfolding initSpec7_def   apply(rule symPredSetExist)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma deriveFormInitSpec7 [intro]: 
                  "[|f : {initSpec7 N}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec8 :: "formula" where [simp]:
 "initSpec8 \<equiv> IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_None"

lemma symPreds8 [intro]: 
                  " 
                  symPredSet' N {initSpec8}"
                   apply(auto      )    
 
done

lemma deriveFormInitSpec8 [intro]: 
                  "[|f : {initSpec8}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec9 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec9 N \<equiv> (\<exists>\<^sub>fi_0. IVar (Ident ''Sta.ShWbMsg.Proc'') =\<^sub>f Const (index i_0)) N"

lemma symPreds9 [intro]: 
                  " 
                  symPredSet' N {initSpec9 N}"
                 unfolding initSpec9_def   apply(rule symPredSetExist)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma deriveFormInitSpec9 [intro]: 
                  "[|f : {initSpec9 N}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec10 :: "formula" where [simp]:
 "initSpec10 \<equiv> IVar (Ident ''Sta.NakcMsg.Cmd'') =\<^sub>f Const NAKC_None"

lemma symPreds10 [intro]: 
                  " 
                  symPredSet' N {initSpec10}"
                   apply(auto      )    
 
done

lemma deriveFormInitSpec10 [intro]: 
                  "[|f : {initSpec10}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec11 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec11 N \<equiv> (\<forall>\<^sub>fp. IVar (Para ''Sta.Proc.ProcCmd'' p) =\<^sub>f Const NODE_None) N"

lemma symPreds11 [intro]: 
                  " 
                  symPredSet' N {initSpec11 N}"
                 unfolding initSpec11_def   apply(rule symPredSetForall)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma deriveFormInitSpec11 [intro]: 
                  "[|f : {initSpec11 N}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec12 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec12 N \<equiv> (\<forall>\<^sub>fp. IVar (Para ''Sta.Proc.InvMarked'' p) =\<^sub>f Const false) N"

lemma symPreds12 [intro]: 
                  " 
                  symPredSet' N {initSpec12 N}"
                 unfolding initSpec12_def   apply(rule symPredSetForall)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma deriveFormInitSpec12 [intro]: 
                  "[|f : {initSpec12 N}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec13 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec13 N \<equiv> (\<forall>\<^sub>fp. IVar (Para ''Sta.Proc.CacheState'' p) =\<^sub>f Const CACHE_I) N"

lemma symPreds13 [intro]: 
                  " 
                  symPredSet' N {initSpec13 N}"
                 unfolding initSpec13_def   apply(rule symPredSetForall)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma deriveFormInitSpec13 [intro]: 
                  "[|f : {initSpec13 N}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec14 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec14 N \<equiv> (\<forall>\<^sub>fp. IVar (Para ''Sta.Dir.ShrSet'' p) =\<^sub>f Const false) N"

lemma symPreds14 [intro]: 
                  " 
                  symPredSet' N {initSpec14 N}"
                 unfolding initSpec14_def   apply(rule symPredSetForall)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma deriveFormInitSpec14 [intro]: 
                  "[|f : {initSpec14 N}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec15 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec15 N \<equiv> (\<forall>\<^sub>fp. IVar (Para ''Sta.Dir.InvSet'' p) =\<^sub>f Const false) N"

lemma symPreds15 [intro]: 
                  " 
                  symPredSet' N {initSpec15 N}"
                 unfolding initSpec15_def   apply(rule symPredSetForall)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma deriveFormInitSpec15 [intro]: 
                  "[|f : {initSpec15 N}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec16 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec16 N \<equiv> (\<forall>\<^sub>fp. IVar (Para ''Sta.InvMsg.Cmd'' p) =\<^sub>f Const INV_None) N"

lemma symPreds16 [intro]: 
                  " 
                  symPredSet' N {initSpec16 N}"
                 unfolding initSpec16_def   apply(rule symPredSetForall)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma deriveFormInitSpec16 [intro]: 
                  "[|f : {initSpec16 N}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec17 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec17 N \<equiv> (\<forall>\<^sub>fp. IVar (Para ''Sta.RpMsg.Cmd'' p) =\<^sub>f Const RP_None) N"

lemma symPreds17 [intro]: 
                  " 
                  symPredSet' N {initSpec17 N}"
                 unfolding initSpec17_def   apply(rule symPredSetForall)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma deriveFormInitSpec17 [intro]: 
                  "[|f : {initSpec17 N}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec18 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec18 N \<equiv> (\<forall>\<^sub>fp. IVar (Para ''Sta.UniMsg.Cmd'' p) =\<^sub>f Const UNI_None) N"

lemma symPreds18 [intro]: 
                  " 
                  symPredSet' N {initSpec18 N}"
                 unfolding initSpec18_def   apply(rule symPredSetForall)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma deriveFormInitSpec18 [intro]: 
                  "[|f : {initSpec18 N}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec19 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec19 N \<equiv> (\<forall>\<^sub>fp. IVar (Para ''Sta.UniMsg.HomeProc'' p) =\<^sub>f Const false) N"

lemma symPreds19 [intro]: 
                  " 
                  symPredSet' N {initSpec19 N}"
                 unfolding initSpec19_def   apply(rule symPredSetForall)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma deriveFormInitSpec19 [intro]: 
                  "[|f : {initSpec19 N}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec20 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec20 N \<equiv> (\<exists>\<^sub>fi_0. (\<forall>\<^sub>fp. IVar (Para ''Sta.UniMsg.Proc'' p) =\<^sub>f Const (index i_0)) N) N"

lemma symPreds20 [intro]: 
                  " 
                  symPredSet' N {initSpec20 N}"
                 unfolding initSpec20_def   apply(rule symPredSetExistForall)
unfolding symParamForm2_def  apply(auto      )    
 
done

lemma deriveFormInitSpec20 [intro]: 
                  "[|f : {initSpec20 N}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec21 :: "formula" where [simp]:
 "initSpec21 \<equiv> IVar (Ident ''Sta.HomeProc.ProcCmd'') =\<^sub>f Const NODE_None"

lemma symPreds21 [intro]: 
                  " 
                  symPredSet' N {initSpec21}"
                   apply(auto      )    
 
done

lemma deriveFormInitSpec21 [intro]: 
                  "[|f : {initSpec21}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec22 :: "formula" where [simp]:
 "initSpec22 \<equiv> IVar (Ident ''Sta.HomeProc.InvMarked'') =\<^sub>f Const false"

lemma symPreds22 [intro]: 
                  " 
                  symPredSet' N {initSpec22}"
                   apply(auto      )    
 
done

lemma deriveFormInitSpec22 [intro]: 
                  "[|f : {initSpec22}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec23 :: "formula" where [simp]:
 "initSpec23 \<equiv> IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_I"

lemma symPreds23 [intro]: 
                  " 
                  symPredSet' N {initSpec23}"
                   apply(auto      )    
 
done

lemma deriveFormInitSpec23 [intro]: 
                  "[|f : {initSpec23}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec24 :: "formula" where [simp]:
 "initSpec24 \<equiv> IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_None"

lemma symPreds24 [intro]: 
                  " 
                  symPredSet' N {initSpec24}"
                   apply(auto      )    
 
done

lemma deriveFormInitSpec24 [intro]: 
                  "[|f : {initSpec24}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec25 :: "formula" where [simp]:
 "initSpec25 \<equiv> IVar (Ident ''Sta.HomeUniMsg.HomeProc'') =\<^sub>f Const false"

lemma symPreds25 [intro]: 
                  " 
                  symPredSet' N {initSpec25}"
                   apply(auto      )    
 
done

lemma deriveFormInitSpec25 [intro]: 
                  "[|f : {initSpec25}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec26 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec26 N \<equiv> (\<exists>\<^sub>fi_0. IVar (Ident ''Sta.HomeUniMsg.Proc'') =\<^sub>f Const (index i_0)) N"

lemma symPreds26 [intro]: 
                  " 
                  symPredSet' N {initSpec26 N}"
                 unfolding initSpec26_def   apply(rule symPredSetExist)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma deriveFormInitSpec26 [intro]: 
                  "[|f : {initSpec26 N}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec27 :: "formula" where [simp]:
 "initSpec27 \<equiv> IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false"

lemma symPreds27 [intro]: 
                  " 
                  symPredSet' N {initSpec27}"
                   apply(auto      )    
 
done

lemma deriveFormInitSpec27 [intro]: 
                  "[|f : {initSpec27}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec28 :: "formula" where [simp]:
 "initSpec28 \<equiv> IVar (Ident ''Sta.Collecting'') =\<^sub>f Const false"

lemma symPreds28 [intro]: 
                  " 
                  symPredSet' N {initSpec28}"
                   apply(auto      )    
 
done

lemma deriveFormInitSpec28 [intro]: 
                  "[|f : {initSpec28}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec29 :: "formula" where [simp]:
 "initSpec29 \<equiv> IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_None"

lemma symPreds29 [intro]: 
                  " 
                  symPredSet' N {initSpec29}"
                   apply(auto      )    
 
done

lemma deriveFormInitSpec29 [intro]: 
                  "[|f : {initSpec29}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec30 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec30 N \<equiv> (\<exists>\<^sub>fi_0. IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index i_0)) N"

lemma symPreds30 [intro]: 
                  " 
                  symPredSet' N {initSpec30 N}"
                 unfolding initSpec30_def   apply(rule symPredSetExist)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma deriveFormInitSpec30 [intro]: 
                  "[|f : {initSpec30 N}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition allInitSpecs :: "nat \<Rightarrow> formula set" where [simp]:
 "allInitSpecs N \<equiv> {initSpec0} \<union> ({initSpec1} \<union> ({initSpec2} \<union> ({initSpec3} \<union> ({initSpec4} \<union> ({initSpec5 N} \<union> ({initSpec6} \<union> ({initSpec7 N} \<union> ({initSpec8} \<union> ({initSpec9 N} \<union> ({initSpec10} \<union> ({initSpec11 N} \<union> ({initSpec12 N} \<union> ({initSpec13 N} \<union> ({initSpec14 N} \<union> ({initSpec15 N} \<union> ({initSpec16 N} \<union> ({initSpec17 N} \<union> ({initSpec18 N} \<union> ({initSpec19 N} \<union> ({initSpec20 N} \<union> ({initSpec21} \<union> ({initSpec22} \<union> ({initSpec23} \<union> ({initSpec24} \<union> ({initSpec25} \<union> ({initSpec26 N} \<union> ({initSpec27} \<union> ({initSpec28} \<union> ({initSpec29} \<union> {initSpec30 N})))))))))))))))))))))))))))))"

lemma symPreds [intro]: 
                  " 
                  symPredSet' N (allInitSpecs N)"
                 unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

  apply(blast      )

done

lemma deriveFormAllInitSpec : 
                  "[|f : allInitSpecs N|] 
                 ==> deriveForm (env N) f"
                  using deriveFormInitSpec0 deriveFormInitSpec1 deriveFormInitSpec2 deriveFormInitSpec3 deriveFormInitSpec4 deriveFormInitSpec5 deriveFormInitSpec6 deriveFormInitSpec7 deriveFormInitSpec8 deriveFormInitSpec9 deriveFormInitSpec10 deriveFormInitSpec11 deriveFormInitSpec12 deriveFormInitSpec13 deriveFormInitSpec14 deriveFormInitSpec15 deriveFormInitSpec16 deriveFormInitSpec17 deriveFormInitSpec18 deriveFormInitSpec19 deriveFormInitSpec20 deriveFormInitSpec21 deriveFormInitSpec22 deriveFormInitSpec23 deriveFormInitSpec24 deriveFormInitSpec25 deriveFormInitSpec26 deriveFormInitSpec27 deriveFormInitSpec28 deriveFormInitSpec29 deriveFormInitSpec30 apply(auto      simp del: initSpec0_def initSpec1_def initSpec2_def initSpec3_def initSpec4_def initSpec5_def initSpec6_def initSpec7_def initSpec8_def initSpec9_def initSpec10_def initSpec11_def initSpec12_def initSpec13_def initSpec14_def initSpec15_def initSpec16_def initSpec17_def initSpec18_def initSpec19_def initSpec20_def initSpec21_def initSpec22_def initSpec23_def initSpec24_def initSpec25_def initSpec26_def initSpec27_def initSpec28_def initSpec29_def initSpec30_def)    
 
done

definition PI_Remote_Get :: "nat \<Rightarrow> rule" where
 "PI_Remote_Get src \<equiv> 
   IVar (Para ''Sta.Proc.ProcCmd'' src) =\<^sub>f Const NODE_None \<and>\<^sub>f
   IVar (Para ''Sta.Proc.CacheState'' src) =\<^sub>f Const CACHE_I
  \<triangleright>
   assign (Para ''Sta.Proc.ProcCmd'' src, Const NODE_Get) ||
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_Get) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const true)"

lemma symPI_Remote_Get : 
             " 
                  symParamRule N PI_Remote_Get"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (PI_Remote_Get src)"
                 
 
             unfolding PI_Remote_Get_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition PI_Remote_Gets :: "nat \<Rightarrow> rule set" where
 "PI_Remote_Gets N \<equiv> oneParamCons N PI_Remote_Get"

definition PI_Local_Get_Get :: "rule" where
 "PI_Local_Get_Get \<equiv> 
   IVar (Ident ''Sta.HomeProc.ProcCmd'') =\<^sub>f Const NODE_None \<and>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_I \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true
  \<triangleright>
   assign (Ident ''Sta.HomeProc.ProcCmd'', Const NODE_Get) ||
   assign (Ident ''Sta.Dir.Pending'', Const true) ||
   assign (Ident ''Sta.HomeUniMsg.Cmd'', Const UNI_Get) ||
   assign (Ident ''Sta.HomeUniMsg.HomeProc'', Const false) ||
   assign (Ident ''Sta.HomeUniMsg.Proc'', IVar (Ident ''Sta.Dir.HeadPtr'')) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_Get) ||
   assign (Ident ''Sta.HomePendReqSrc'', Const true) ||
   assign (Ident ''Sta.Collecting'', Const false)"

lemma symPI_Local_Get_Get : 
             " 
                  symProtRules' N {PI_Local_Get_Get}"
                 

" 
                  wellFormedRule (env N) N (PI_Local_Get_Get)"
                 
 
             unfolding PI_Local_Get_Get_def  apply(auto      )    
 
done

definition PI_Local_Get_Gets :: "rule set" where
 "PI_Local_Get_Gets \<equiv> {PI_Local_Get_Get}"

definition PI_Local_Get_Put :: "rule" where
 "PI_Local_Get_Put \<equiv> 
   IVar (Ident ''Sta.HomeProc.ProcCmd'') =\<^sub>f Const NODE_None \<and>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_I \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const false
  \<triangleright>
   assign (Ident ''Sta.Dir.Local'', Const true) ||
   assign (Ident ''Sta.HomeProc.ProcCmd'', Const NODE_None) ||
   (IF IVar (Ident ''Sta.HomeProc.InvMarked'') =\<^sub>f Const true DO
     assign (Ident ''Sta.HomeProc.InvMarked'', Const false) ||
     assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_I)
   ELSE
     assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_S)
   FI)"

lemma symPI_Local_Get_Put : 
             " 
                  symProtRules' N {PI_Local_Get_Put}"
                 

" 
                  wellFormedRule (env N) N (PI_Local_Get_Put)"
                 
 
             unfolding PI_Local_Get_Put_def  apply(auto      )    
 
done

definition PI_Local_Get_Puts :: "rule set" where
 "PI_Local_Get_Puts \<equiv> {PI_Local_Get_Put}"

definition PI_Remote_GetX :: "nat \<Rightarrow> rule" where
 "PI_Remote_GetX src \<equiv> 
   IVar (Para ''Sta.Proc.ProcCmd'' src) =\<^sub>f Const NODE_None \<and>\<^sub>f
   IVar (Para ''Sta.Proc.CacheState'' src) =\<^sub>f Const CACHE_I
  \<triangleright>
   assign (Para ''Sta.Proc.ProcCmd'' src, Const NODE_GetX) ||
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_GetX) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const true)"

lemma symPI_Remote_GetX : 
             " 
                  symParamRule N PI_Remote_GetX"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (PI_Remote_GetX src)"
                 
 
             unfolding PI_Remote_GetX_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition PI_Remote_GetXs :: "nat \<Rightarrow> rule set" where
 "PI_Remote_GetXs N \<equiv> oneParamCons N PI_Remote_GetX"

definition PI_Local_GetX_GetX :: "rule" where
 "PI_Local_GetX_GetX \<equiv> 
   IVar (Ident ''Sta.HomeProc.ProcCmd'') =\<^sub>f Const NODE_None \<and>\<^sub>f
   (IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_I \<or>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_S) \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true
  \<triangleright>
   assign (Ident ''Sta.HomeProc.ProcCmd'', Const NODE_GetX) ||
   assign (Ident ''Sta.Dir.Pending'', Const true) ||
   assign (Ident ''Sta.HomeUniMsg.Cmd'', Const UNI_GetX) ||
   assign (Ident ''Sta.HomeUniMsg.HomeProc'', Const false) ||
   assign (Ident ''Sta.HomeUniMsg.Proc'', IVar (Ident ''Sta.Dir.HeadPtr'')) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_GetX) ||
   assign (Ident ''Sta.HomePendReqSrc'', Const true) ||
   assign (Ident ''Sta.Collecting'', Const false)"

lemma symPI_Local_GetX_GetX : 
             " 
                  symProtRules' N {PI_Local_GetX_GetX}"
                 

" 
                  wellFormedRule (env N) N (PI_Local_GetX_GetX)"
                 
 
             unfolding PI_Local_GetX_GetX_def  apply(auto      )    
 
done

definition PI_Local_GetX_GetXs :: "rule set" where
 "PI_Local_GetX_GetXs \<equiv> {PI_Local_GetX_GetX}"

definition PI_Local_GetX_PutX :: "nat \<Rightarrow> rule" where
 "PI_Local_GetX_PutX N \<equiv> 
   IVar (Ident ''Sta.HomeProc.ProcCmd'') =\<^sub>f Const NODE_None \<and>\<^sub>f
   (IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_I \<or>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_S) \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const false
  \<triangleright>
   assign (Ident ''Sta.Dir.Local'', Const true) ||
   assign (Ident ''Sta.Dir.Dirty'', Const true) ||
   (IF IVar (Ident ''Sta.Dir.HeadVld'') =\<^sub>f Const true DO
     assign (Ident ''Sta.Dir.Pending'', Const true) ||
     forallStm (\<lambda>p. assign (Para ''Sta.Dir.InvSet'' p, iteForm (IVar (Ident ''Sta.Dir.ShrVld'') =\<^sub>f Const true \<and>\<^sub>f
     IVar (Para ''Sta.Dir.ShrSet'' p) =\<^sub>f Const true \<or>\<^sub>f
     IVar (Ident ''Sta.Dir.HeadVld'') =\<^sub>f Const true \<and>\<^sub>f
     IVar (Ident ''Sta.Dir.HeadPtr'') =\<^sub>f Const (index p)) (Const true) (Const false)) ||
     assign (Para ''Sta.InvMsg.Cmd'' p, iteForm (IVar (Ident ''Sta.Dir.ShrVld'') =\<^sub>f Const true \<and>\<^sub>f
     IVar (Para ''Sta.Dir.ShrSet'' p) =\<^sub>f Const true \<or>\<^sub>f
     IVar (Ident ''Sta.Dir.HeadVld'') =\<^sub>f Const true \<and>\<^sub>f
     IVar (Ident ''Sta.Dir.HeadPtr'') =\<^sub>f Const (index p)) (Const INV_Inv) (Const INV_None)) ||
     assign (Para ''Sta.Dir.ShrSet'' p, Const false)) N ||
     assign (Ident ''Sta.Dir.HeadVld'', Const false) ||
     assign (Ident ''Sta.Dir.ShrVld'', Const false) ||
     assign (Ident ''Sta.Collecting'', Const true)
   ELSE
     skip
   FI) ||
   assign (Ident ''Sta.HomeProc.ProcCmd'', Const NODE_None) ||
   assign (Ident ''Sta.HomeProc.InvMarked'', Const false) ||
   assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_E)"

lemma symPI_Local_GetX_PutX : 
             " 
                  symProtRules' N {PI_Local_GetX_PutX N}"
                 

" 
                  wellFormedRule (env N) N (PI_Local_GetX_PutX N)"
                 
 
             unfolding PI_Local_GetX_PutX_def  apply(auto intro!: equivStatementParallel equivStatementIteStm equivStatementPermute     )    
 
   apply(rule equivStatementSym)
   apply(rule equivStatementPermute)
  apply(auto     simp add: mutualDiffVars_def )    
 
done

definition PI_Local_GetX_PutXs :: "nat \<Rightarrow> rule set" where
 "PI_Local_GetX_PutXs N \<equiv> {PI_Local_GetX_PutX N}"

definition PI_Remote_PutX :: "nat \<Rightarrow> rule" where
 "PI_Remote_PutX dst \<equiv> 
   IVar (Para ''Sta.Proc.ProcCmd'' dst) =\<^sub>f Const NODE_None \<and>\<^sub>f
   IVar (Para ''Sta.Proc.CacheState'' dst) =\<^sub>f Const CACHE_E
  \<triangleright>
   assign (Para ''Sta.Proc.CacheState'' dst, Const CACHE_I) ||
   assign (Ident ''Sta.WbMsg.Cmd'', Const WB_Wb) ||
   assign (Ident ''Sta.WbMsg.Proc'', Const (index dst))"

lemma symPI_Remote_PutX : 
             " 
                  symParamRule N PI_Remote_PutX"
                 

"[|dst <= N|] 
                 ==> wellFormedRule (env N) N (PI_Remote_PutX dst)"
                 
 
             unfolding PI_Remote_PutX_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition PI_Remote_PutXs :: "nat \<Rightarrow> rule set" where
 "PI_Remote_PutXs N \<equiv> oneParamCons N PI_Remote_PutX"

definition PI_Local_PutX :: "rule" where
 "PI_Local_PutX \<equiv> 
   IVar (Ident ''Sta.HomeProc.ProcCmd'') =\<^sub>f Const NODE_None \<and>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E
  \<triangleright>
   (IF IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true DO
     assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_I) ||
     assign (Ident ''Sta.Dir.Dirty'', Const false)
   ELSE
     assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_I) ||
     assign (Ident ''Sta.Dir.Local'', Const false) ||
     assign (Ident ''Sta.Dir.Dirty'', Const false)
   FI)"

lemma symPI_Local_PutX : 
             " 
                  symProtRules' N {PI_Local_PutX}"
                 

" 
                  wellFormedRule (env N) N (PI_Local_PutX)"
                 
 
             unfolding PI_Local_PutX_def  apply(auto      )    
 
done

definition PI_Local_PutXs :: "rule set" where
 "PI_Local_PutXs \<equiv> {PI_Local_PutX}"

definition PI_Remote_Replace :: "nat \<Rightarrow> rule" where
 "PI_Remote_Replace src \<equiv> 
   IVar (Para ''Sta.Proc.ProcCmd'' src) =\<^sub>f Const NODE_None \<and>\<^sub>f
   IVar (Para ''Sta.Proc.CacheState'' src) =\<^sub>f Const CACHE_S
  \<triangleright>
   assign (Para ''Sta.Proc.CacheState'' src, Const CACHE_I) ||
   assign (Para ''Sta.RpMsg.Cmd'' src, Const RP_Replace)"

lemma symPI_Remote_Replace : 
             " 
                  symParamRule N PI_Remote_Replace"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (PI_Remote_Replace src)"
                 
 
             unfolding PI_Remote_Replace_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition PI_Remote_Replaces :: "nat \<Rightarrow> rule set" where
 "PI_Remote_Replaces N \<equiv> oneParamCons N PI_Remote_Replace"

definition PI_Local_Replace :: "rule" where
 "PI_Local_Replace \<equiv> 
   IVar (Ident ''Sta.HomeProc.ProcCmd'') =\<^sub>f Const NODE_None \<and>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_S
  \<triangleright>
   assign (Ident ''Sta.Dir.Local'', Const false) ||
   assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_I)"

lemma symPI_Local_Replace : 
             " 
                  symProtRules' N {PI_Local_Replace}"
                 

" 
                  wellFormedRule (env N) N (PI_Local_Replace)"
                 
 
             unfolding PI_Local_Replace_def  apply(auto      )    
 
done

definition PI_Local_Replaces :: "rule set" where
 "PI_Local_Replaces \<equiv> {PI_Local_Replace}"

definition NI_Nak :: "nat \<Rightarrow> rule" where
 "NI_Nak dst \<equiv> 
   IVar (Para ''Sta.UniMsg.Cmd'' dst) =\<^sub>f Const UNI_Nak
  \<triangleright>
   assign (Para ''Sta.UniMsg.Cmd'' dst, Const UNI_None) ||
   assign (Para ''Sta.UniMsg.HomeProc'' dst, Const false) ||
   assign (Para ''Sta.Proc.ProcCmd'' dst, Const NODE_None) ||
   assign (Para ''Sta.Proc.InvMarked'' dst, Const false)"

lemma symNI_Nak : 
             " 
                  symParamRule N NI_Nak"
                 

"[|dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Nak dst)"
                 
 
             unfolding NI_Nak_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Naks :: "nat \<Rightarrow> rule set" where
 "NI_Naks N \<equiv> oneParamCons N NI_Nak"

definition NI_Nak_Home :: "rule" where
 "NI_Nak_Home \<equiv> 
   IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Nak
  \<triangleright>
   assign (Ident ''Sta.HomeUniMsg.Cmd'', Const UNI_None) ||
   assign (Ident ''Sta.HomeUniMsg.HomeProc'', Const false) ||
   assign (Ident ''Sta.HomeProc.ProcCmd'', Const NODE_None) ||
   assign (Ident ''Sta.HomeProc.InvMarked'', Const false)"

lemma symNI_Nak_Home : 
             " 
                  symProtRules' N {NI_Nak_Home}"
                 

" 
                  wellFormedRule (env N) N (NI_Nak_Home)"
                 
 
             unfolding NI_Nak_Home_def  apply(auto      )    
 
done

definition NI_Nak_Homes :: "rule set" where
 "NI_Nak_Homes \<equiv> {NI_Nak_Home}"

definition NI_Nak_Clear :: "rule" where
 "NI_Nak_Clear \<equiv> 
   IVar (Ident ''Sta.NakcMsg.Cmd'') =\<^sub>f Const NAKC_Nakc
  \<triangleright>
   assign (Ident ''Sta.NakcMsg.Cmd'', Const NAKC_None) ||
   assign (Ident ''Sta.Dir.Pending'', Const false)"

lemma symNI_Nak_Clear : 
             " 
                  symProtRules' N {NI_Nak_Clear}"
                 

" 
                  wellFormedRule (env N) N (NI_Nak_Clear)"
                 
 
             unfolding NI_Nak_Clear_def  apply(auto      )    
 
done

definition NI_Nak_Clears :: "rule set" where
 "NI_Nak_Clears \<equiv> {NI_Nak_Clear}"

definition NI_Local_Get_Nak :: "nat \<Rightarrow> rule" where
 "NI_Local_Get_Nak src \<equiv> 
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_Get \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.RpMsg.Cmd'' src) =\<^sub>f Const RP_Replace \<and>\<^sub>f
   (IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<or>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E \<or>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.HeadPtr'') =\<^sub>f Const (index src))
  \<triangleright>
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_Nak) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const true)"

lemma symNI_Local_Get_Nak : 
             " 
                  symParamRule N NI_Local_Get_Nak"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_Local_Get_Nak src)"
                 
 
             unfolding NI_Local_Get_Nak_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Local_Get_Naks :: "nat \<Rightarrow> rule set" where
 "NI_Local_Get_Naks N \<equiv> oneParamCons N NI_Local_Get_Nak"

definition NI_Local_Get_Get :: "nat \<Rightarrow> rule" where
 "NI_Local_Get_Get src \<equiv> 
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_Get \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.RpMsg.Cmd'' src) =\<^sub>f Const RP_Replace \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.Dir.HeadPtr'') =\<^sub>f Const (index src)
  \<triangleright>
   assign (Ident ''Sta.Dir.Pending'', Const true) ||
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_Get) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const false) ||
   assign (Para ''Sta.UniMsg.Proc'' src, IVar (Ident ''Sta.Dir.HeadPtr'')) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_Get) ||
   assign (Ident ''Sta.HomePendReqSrc'', Const false) ||
   assign (Ident ''Sta.PendReqSrc'', Const (index src)) ||
   assign (Ident ''Sta.Collecting'', Const false)"

lemma symNI_Local_Get_Get : 
             " 
                  symParamRule N NI_Local_Get_Get"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_Local_Get_Get src)"
                 
 
             unfolding NI_Local_Get_Get_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Local_Get_Gets :: "nat \<Rightarrow> rule set" where
 "NI_Local_Get_Gets N \<equiv> oneParamCons N NI_Local_Get_Get"

definition NI_Local_Get_Put :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "NI_Local_Get_Put N src \<equiv> 
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_Get \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.RpMsg.Cmd'' src) =\<^sub>f Const RP_Replace \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   (IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<longrightarrow>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E)
  \<triangleright>
   (IF IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true DO
     assign (Ident ''Sta.Dir.Dirty'', Const false) ||
     assign (Ident ''Sta.Dir.HeadVld'', Const true) ||
     assign (Ident ''Sta.Dir.HeadPtr'', Const (index src)) ||
     assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_S) ||
     assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_Put) ||
     assign (Para ''Sta.UniMsg.HomeProc'' src, Const true)
   ELSE
     (IF IVar (Ident ''Sta.Dir.HeadVld'') =\<^sub>f Const true DO
       assign (Ident ''Sta.Dir.ShrVld'', Const true) ||
       assign (Para ''Sta.Dir.ShrSet'' src, Const true) ||
       assign (Para ''Sta.Dir.InvSet'' src, Const true) ||
       forallStmExcl (\<lambda>p. assign (Para ''Sta.Dir.InvSet'' p, IVar (Para ''Sta.Dir.ShrSet'' p))) src N
     ELSE
       assign (Ident ''Sta.Dir.HeadVld'', Const true) ||
       assign (Ident ''Sta.Dir.HeadPtr'', Const (index src))
     FI) ||
     assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_Put) ||
     assign (Para ''Sta.UniMsg.HomeProc'' src, Const true)
   FI)"

lemma symNI_Local_Get_Put : 
             " 
                  symParamRule N (NI_Local_Get_Put N)"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_Local_Get_Put N src)"
                 
 
             unfolding NI_Local_Get_Put_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Local_Get_Puts :: "nat \<Rightarrow> rule set" where
 "NI_Local_Get_Puts N \<equiv> oneParamCons N (NI_Local_Get_Put N)"

definition NI_Remote_Get_Nak :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "NI_Remote_Get_Nak src dst \<equiv> 
   \<not>\<^sub>f Const (index src) =\<^sub>f Const (index dst) \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_Get \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const false \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Proc'' src) =\<^sub>f Const (index dst) \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' dst) =\<^sub>f Const CACHE_E
  \<triangleright>
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_Nak) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const false) ||
   assign (Para ''Sta.UniMsg.Proc'' src, Const (index dst)) ||
   assign (Ident ''Sta.NakcMsg.Cmd'', Const NAKC_Nakc) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

lemma symNI_Remote_Get_Nak : 
             " 
                  symParamRule2' N NI_Remote_Get_Nak"
                 

"[|src <= N;dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Remote_Get_Nak src dst)"
                 
 
             unfolding NI_Remote_Get_Nak_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamForm2And symParamForm2Forall1 symParamForm2Forall2 symParamFormForallExcl2 symParamForm2Imply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Remote_Get_Naks :: "nat \<Rightarrow> rule set" where
 "NI_Remote_Get_Naks N \<equiv> twoParamsCons N NI_Remote_Get_Nak"

definition NI_Remote_Get_Nak_Home :: "nat \<Rightarrow> rule" where
 "NI_Remote_Get_Nak_Home dst \<equiv> 
   IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Get \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.HomeProc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.Proc'') =\<^sub>f Const (index dst) \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E
  \<triangleright>
   assign (Ident ''Sta.HomeUniMsg.Cmd'', Const UNI_Nak) ||
   assign (Ident ''Sta.HomeUniMsg.HomeProc'', Const false) ||
   assign (Ident ''Sta.HomeUniMsg.Proc'', Const (index dst)) ||
   assign (Ident ''Sta.NakcMsg.Cmd'', Const NAKC_Nakc) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

lemma symNI_Remote_Get_Nak_Home : 
             " 
                  symParamRule N NI_Remote_Get_Nak_Home"
                 

"[|dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Remote_Get_Nak_Home dst)"
                 
 
             unfolding NI_Remote_Get_Nak_Home_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Remote_Get_Nak_Homes :: "nat \<Rightarrow> rule set" where
 "NI_Remote_Get_Nak_Homes N \<equiv> oneParamCons N NI_Remote_Get_Nak_Home"

definition NI_Remote_Get_Put :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "NI_Remote_Get_Put src dst \<equiv> 
   \<not>\<^sub>f Const (index src) =\<^sub>f Const (index dst) \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_Get \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const false \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Proc'' src) =\<^sub>f Const (index dst) \<and>\<^sub>f
   IVar (Para ''Sta.Proc.CacheState'' dst) =\<^sub>f Const CACHE_E
  \<triangleright>
   assign (Para ''Sta.Proc.CacheState'' dst, Const CACHE_S) ||
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_Put) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const false) ||
   assign (Para ''Sta.UniMsg.Proc'' src, Const (index dst)) ||
   assign (Ident ''Sta.ShWbMsg.Cmd'', Const SHWB_ShWb) ||
   assign (Ident ''Sta.ShWbMsg.Proc'', Const (index src)) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

lemma symNI_Remote_Get_Put : 
             " 
                  symParamRule2' N NI_Remote_Get_Put"
                 

"[|src <= N;dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Remote_Get_Put src dst)"
                 
 
             unfolding NI_Remote_Get_Put_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamForm2And symParamForm2Forall1 symParamForm2Forall2 symParamFormForallExcl2 symParamForm2Imply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Remote_Get_Puts :: "nat \<Rightarrow> rule set" where
 "NI_Remote_Get_Puts N \<equiv> twoParamsCons N NI_Remote_Get_Put"

definition NI_Remote_Get_Put_Home :: "nat \<Rightarrow> rule" where
 "NI_Remote_Get_Put_Home dst \<equiv> 
   IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Get \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.HomeProc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.Proc'') =\<^sub>f Const (index dst) \<and>\<^sub>f
   IVar (Para ''Sta.Proc.CacheState'' dst) =\<^sub>f Const CACHE_E
  \<triangleright>
   assign (Para ''Sta.Proc.CacheState'' dst, Const CACHE_S) ||
   assign (Ident ''Sta.HomeUniMsg.Cmd'', Const UNI_Put) ||
   assign (Ident ''Sta.HomeUniMsg.HomeProc'', Const false) ||
   assign (Ident ''Sta.HomeUniMsg.Proc'', Const (index dst)) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

lemma symNI_Remote_Get_Put_Home : 
             " 
                  symParamRule N NI_Remote_Get_Put_Home"
                 

"[|dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Remote_Get_Put_Home dst)"
                 
 
             unfolding NI_Remote_Get_Put_Home_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Remote_Get_Put_Homes :: "nat \<Rightarrow> rule set" where
 "NI_Remote_Get_Put_Homes N \<equiv> oneParamCons N NI_Remote_Get_Put_Home"

definition NI_Local_GetX_Nak :: "nat \<Rightarrow> rule" where
 "NI_Local_GetX_Nak src \<equiv> 
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_GetX \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const true \<and>\<^sub>f
   (IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<or>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E \<or>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.HeadPtr'') =\<^sub>f Const (index src))
  \<triangleright>
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_Nak) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const true)"

lemma symNI_Local_GetX_Nak : 
             " 
                  symParamRule N NI_Local_GetX_Nak"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_Local_GetX_Nak src)"
                 
 
             unfolding NI_Local_GetX_Nak_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Local_GetX_Naks :: "nat \<Rightarrow> rule set" where
 "NI_Local_GetX_Naks N \<equiv> oneParamCons N NI_Local_GetX_Nak"

definition NI_Local_GetX_GetX :: "nat \<Rightarrow> rule" where
 "NI_Local_GetX_GetX src \<equiv> 
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_GetX \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.Dir.HeadPtr'') =\<^sub>f Const (index src)
  \<triangleright>
   assign (Ident ''Sta.Dir.Pending'', Const true) ||
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_GetX) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const false) ||
   assign (Para ''Sta.UniMsg.Proc'' src, IVar (Ident ''Sta.Dir.HeadPtr'')) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_GetX) ||
   assign (Ident ''Sta.HomePendReqSrc'', Const false) ||
   assign (Ident ''Sta.PendReqSrc'', Const (index src)) ||
   assign (Ident ''Sta.Collecting'', Const false)"

lemma symNI_Local_GetX_GetX : 
             " 
                  symParamRule N NI_Local_GetX_GetX"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_Local_GetX_GetX src)"
                 
 
             unfolding NI_Local_GetX_GetX_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Local_GetX_GetXs :: "nat \<Rightarrow> rule set" where
 "NI_Local_GetX_GetXs N \<equiv> oneParamCons N NI_Local_GetX_GetX"

definition NI_Local_GetX_PutX1 :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "NI_Local_GetX_PutX1 N src \<equiv> 
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_GetX \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   (IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<longrightarrow>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E) \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true
  \<triangleright>
   assign (Ident ''Sta.Dir.Local'', Const false) ||
   assign (Ident ''Sta.Dir.Dirty'', Const true) ||
   assign (Ident ''Sta.Dir.HeadVld'', Const true) ||
   assign (Ident ''Sta.Dir.HeadPtr'', Const (index src)) ||
   assign (Ident ''Sta.Dir.ShrVld'', Const false) ||
   forallStm (\<lambda>p. assign (Para ''Sta.Dir.ShrSet'' p, Const false) ||
   assign (Para ''Sta.Dir.InvSet'' p, Const false)) N ||
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_PutX) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const true) ||
   assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_I)"

lemma symNI_Local_GetX_PutX1 : 
             " 
                  symParamRule N (NI_Local_GetX_PutX1 N)"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_Local_GetX_PutX1 N src)"
                 
 
             unfolding NI_Local_GetX_PutX1_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Local_GetX_PutX1s :: "nat \<Rightarrow> rule set" where
 "NI_Local_GetX_PutX1s N \<equiv> oneParamCons N (NI_Local_GetX_PutX1 N)"

definition NI_Local_GetX_PutX2 :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "NI_Local_GetX_PutX2 N src \<equiv> 
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_GetX \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   (IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<longrightarrow>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E) \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const false \<and>\<^sub>f
   (IVar (Ident ''Sta.Dir.HeadVld'') =\<^sub>f Const true \<longrightarrow>\<^sub>f
   IVar (Ident ''Sta.Dir.HeadPtr'') =\<^sub>f Const (index src) \<and>\<^sub>f
   forallFormExcl (\<lambda>p. IVar (Para ''Sta.Dir.ShrSet'' p) =\<^sub>f Const false) src N)
  \<triangleright>
   assign (Ident ''Sta.Dir.Dirty'', Const true) ||
   assign (Ident ''Sta.Dir.HeadVld'', Const true) ||
   assign (Ident ''Sta.Dir.HeadPtr'', Const (index src)) ||
   assign (Ident ''Sta.Dir.ShrVld'', Const false) ||
   forallStm (\<lambda>p. assign (Para ''Sta.Dir.ShrSet'' p, Const false) ||
   assign (Para ''Sta.Dir.InvSet'' p, Const false)) N ||
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_PutX) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const true) ||
   assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_I) ||
   (IF IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true DO
     assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_I) ||
     (IF IVar (Ident ''Sta.HomeProc.ProcCmd'') =\<^sub>f Const NODE_Get DO
       assign (Ident ''Sta.HomeProc.InvMarked'', Const true)
     ELSE
       skip
     FI)
   ELSE
     skip
   FI) ||
   assign (Ident ''Sta.Dir.Local'', Const false)"

lemma symNI_Local_GetX_PutX2 : 
             " 
                  symParamRule N (NI_Local_GetX_PutX2 N)"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_Local_GetX_PutX2 N src)"
                 
 
             unfolding NI_Local_GetX_PutX2_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Local_GetX_PutX2s :: "nat \<Rightarrow> rule set" where
 "NI_Local_GetX_PutX2s N \<equiv> oneParamCons N (NI_Local_GetX_PutX2 N)"

definition NI_Local_GetX_PutX3 :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "NI_Local_GetX_PutX3 N src \<equiv> 
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_GetX \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   (IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<longrightarrow>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E) \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const false
  \<triangleright>
   assign (Ident ''Sta.Dir.Pending'', Const true) ||
   assign (Ident ''Sta.Dir.Dirty'', Const true) ||
   assign (Para ''Sta.Dir.InvSet'' src, Const false) ||
   assign (Para ''Sta.InvMsg.Cmd'' src, Const INV_None) ||
   assign (Para ''Sta.Dir.ShrSet'' src, Const false) ||
   forallStmExcl (\<lambda>p. assign (Para ''Sta.Dir.InvSet'' p, iteForm (IVar (Ident ''Sta.Dir.ShrVld'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Para ''Sta.Dir.ShrSet'' p) =\<^sub>f Const true \<or>\<^sub>f
   IVar (Ident ''Sta.Dir.HeadVld'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.HeadPtr'') =\<^sub>f Const (index p)) (Const true) (Const false)) ||
   assign (Para ''Sta.InvMsg.Cmd'' p, iteForm (IVar (Ident ''Sta.Dir.ShrVld'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Para ''Sta.Dir.ShrSet'' p) =\<^sub>f Const true \<or>\<^sub>f
   IVar (Ident ''Sta.Dir.HeadVld'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.HeadPtr'') =\<^sub>f Const (index p)) (Const INV_Inv) (Const INV_None)) ||
   assign (Para ''Sta.Dir.ShrSet'' p, Const false)) src N ||
   assign (Ident ''Sta.Dir.HeadVld'', Const true) ||
   assign (Ident ''Sta.Dir.HeadPtr'', Const (index src)) ||
   assign (Ident ''Sta.Dir.ShrVld'', Const false) ||
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_PutX) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const true) ||
   (IF IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true DO
     assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_I) ||
     (IF IVar (Ident ''Sta.HomeProc.ProcCmd'') =\<^sub>f Const NODE_Get DO
       assign (Ident ''Sta.HomeProc.InvMarked'', Const true)
     ELSE
       skip
     FI)
   ELSE
     skip
   FI) ||
   assign (Ident ''Sta.Dir.Local'', Const false) ||
   assign (Ident ''Sta.HomePendReqSrc'', Const false) ||
   assign (Ident ''Sta.PendReqSrc'', Const (index src)) ||
   assign (Ident ''Sta.Collecting'', Const true)"

lemma symNI_Local_GetX_PutX3 : 
             " 
                  symParamRule N (NI_Local_GetX_PutX3 N)"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_Local_GetX_PutX3 N src)"
                 
 
             unfolding NI_Local_GetX_PutX3_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Local_GetX_PutX3s :: "nat \<Rightarrow> rule set" where
 "NI_Local_GetX_PutX3s N \<equiv> oneParamCons N (NI_Local_GetX_PutX3 N)"

definition NI_Remote_GetX_Nak :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "NI_Remote_GetX_Nak src dst \<equiv> 
   \<not>\<^sub>f Const (index src) =\<^sub>f Const (index dst) \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_GetX \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const false \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Proc'' src) =\<^sub>f Const (index dst) \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' dst) =\<^sub>f Const CACHE_E
  \<triangleright>
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_Nak) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const false) ||
   assign (Para ''Sta.UniMsg.Proc'' src, Const (index dst)) ||
   assign (Ident ''Sta.NakcMsg.Cmd'', Const NAKC_Nakc) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

lemma symNI_Remote_GetX_Nak : 
             " 
                  symParamRule2' N NI_Remote_GetX_Nak"
                 

"[|src <= N;dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Remote_GetX_Nak src dst)"
                 
 
             unfolding NI_Remote_GetX_Nak_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamForm2And symParamForm2Forall1 symParamForm2Forall2 symParamFormForallExcl2 symParamForm2Imply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Remote_GetX_Naks :: "nat \<Rightarrow> rule set" where
 "NI_Remote_GetX_Naks N \<equiv> twoParamsCons N NI_Remote_GetX_Nak"

definition NI_Remote_GetX_Nak_Home :: "nat \<Rightarrow> rule" where
 "NI_Remote_GetX_Nak_Home dst \<equiv> 
   IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_GetX \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.HomeProc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.Proc'') =\<^sub>f Const (index dst) \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' dst) =\<^sub>f Const CACHE_E
  \<triangleright>
   assign (Ident ''Sta.HomeUniMsg.Cmd'', Const UNI_Nak) ||
   assign (Ident ''Sta.HomeUniMsg.HomeProc'', Const false) ||
   assign (Ident ''Sta.HomeUniMsg.Proc'', Const (index dst)) ||
   assign (Ident ''Sta.NakcMsg.Cmd'', Const NAKC_Nakc) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

lemma symNI_Remote_GetX_Nak_Home : 
             " 
                  symParamRule N NI_Remote_GetX_Nak_Home"
                 

"[|dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Remote_GetX_Nak_Home dst)"
                 
 
             unfolding NI_Remote_GetX_Nak_Home_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Remote_GetX_Nak_Homes :: "nat \<Rightarrow> rule set" where
 "NI_Remote_GetX_Nak_Homes N \<equiv> oneParamCons N NI_Remote_GetX_Nak_Home"

definition NI_Remote_GetX_PutX :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "NI_Remote_GetX_PutX src dst \<equiv> 
   \<not>\<^sub>f Const (index src) =\<^sub>f Const (index dst) \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_GetX \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const false \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Proc'' src) =\<^sub>f Const (index dst) \<and>\<^sub>f
   IVar (Para ''Sta.Proc.CacheState'' dst) =\<^sub>f Const CACHE_E
  \<triangleright>
   assign (Para ''Sta.Proc.CacheState'' dst, Const CACHE_I) ||
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_PutX) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const false) ||
   assign (Para ''Sta.UniMsg.Proc'' src, Const (index dst)) ||
   assign (Ident ''Sta.ShWbMsg.Cmd'', Const SHWB_FAck) ||
   assign (Ident ''Sta.ShWbMsg.Proc'', Const (index src)) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

lemma symNI_Remote_GetX_PutX : 
             " 
                  symParamRule2' N NI_Remote_GetX_PutX"
                 

"[|src <= N;dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Remote_GetX_PutX src dst)"
                 
 
             unfolding NI_Remote_GetX_PutX_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamForm2And symParamForm2Forall1 symParamForm2Forall2 symParamFormForallExcl2 symParamForm2Imply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Remote_GetX_PutXs :: "nat \<Rightarrow> rule set" where
 "NI_Remote_GetX_PutXs N \<equiv> twoParamsCons N NI_Remote_GetX_PutX"

definition NI_Remote_GetX_PutX_Home :: "nat \<Rightarrow> rule" where
 "NI_Remote_GetX_PutX_Home dst \<equiv> 
   IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_GetX \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.HomeProc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.Proc'') =\<^sub>f Const (index dst) \<and>\<^sub>f
   IVar (Para ''Sta.Proc.CacheState'' dst) =\<^sub>f Const CACHE_E
  \<triangleright>
   assign (Para ''Sta.Proc.CacheState'' dst, Const CACHE_I) ||
   assign (Ident ''Sta.HomeUniMsg.Cmd'', Const UNI_PutX) ||
   assign (Ident ''Sta.HomeUniMsg.HomeProc'', Const false) ||
   assign (Ident ''Sta.HomeUniMsg.Proc'', Const (index dst)) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

lemma symNI_Remote_GetX_PutX_Home : 
             " 
                  symParamRule N NI_Remote_GetX_PutX_Home"
                 

"[|dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Remote_GetX_PutX_Home dst)"
                 
 
             unfolding NI_Remote_GetX_PutX_Home_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Remote_GetX_PutX_Homes :: "nat \<Rightarrow> rule set" where
 "NI_Remote_GetX_PutX_Homes N \<equiv> oneParamCons N NI_Remote_GetX_PutX_Home"

definition NI_Local_Put :: "rule" where
 "NI_Local_Put \<equiv> 
   IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Put
  \<triangleright>
   assign (Ident ''Sta.HomeUniMsg.Cmd'', Const UNI_None) ||
   assign (Ident ''Sta.Dir.Pending'', Const false) ||
   assign (Ident ''Sta.Dir.Dirty'', Const false) ||
   assign (Ident ''Sta.Dir.Local'', Const true) ||
   assign (Ident ''Sta.HomeProc.ProcCmd'', Const NODE_None) ||
   (IF IVar (Ident ''Sta.HomeProc.InvMarked'') =\<^sub>f Const true DO
     assign (Ident ''Sta.HomeProc.InvMarked'', Const false) ||
     assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_I)
   ELSE
     assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_S)
   FI)"

lemma symNI_Local_Put : 
             " 
                  symProtRules' N {NI_Local_Put}"
                 

" 
                  wellFormedRule (env N) N (NI_Local_Put)"
                 
 
             unfolding NI_Local_Put_def  apply(auto      )    
 
done

definition NI_Local_Puts :: "rule set" where
 "NI_Local_Puts \<equiv> {NI_Local_Put}"

definition NI_Remote_Put :: "nat \<Rightarrow> rule" where
 "NI_Remote_Put dst \<equiv> 
   IVar (Para ''Sta.UniMsg.Cmd'' dst) =\<^sub>f Const UNI_Put
  \<triangleright>
   assign (Para ''Sta.UniMsg.Cmd'' dst, Const UNI_None) ||
   assign (Para ''Sta.UniMsg.HomeProc'' dst, Const false) ||
   assign (Para ''Sta.Proc.ProcCmd'' dst, Const NODE_None) ||
   assign (Para ''Sta.Proc.CacheState'' dst, iteForm (IVar (Para ''Sta.Proc.InvMarked'' dst) =\<^sub>f Const true) (Const CACHE_I) (Const CACHE_S)) ||
   assign (Para ''Sta.Proc.InvMarked'' dst, Const false)"

lemma symNI_Remote_Put : 
             " 
                  symParamRule N NI_Remote_Put"
                 

"[|dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Remote_Put dst)"
                 
 
             unfolding NI_Remote_Put_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Remote_Puts :: "nat \<Rightarrow> rule set" where
 "NI_Remote_Puts N \<equiv> oneParamCons N NI_Remote_Put"

definition NI_Local_PutXAcksDone :: "rule" where
 "NI_Local_PutXAcksDone \<equiv> 
   IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_PutX
  \<triangleright>
   assign (Ident ''Sta.HomeUniMsg.Cmd'', Const UNI_None) ||
   assign (Ident ''Sta.Dir.Pending'', Const false) ||
   assign (Ident ''Sta.Dir.Local'', Const true) ||
   assign (Ident ''Sta.Dir.HeadVld'', Const false) ||
   assign (Ident ''Sta.HomeProc.ProcCmd'', Const NODE_None) ||
   assign (Ident ''Sta.HomeProc.InvMarked'', Const false) ||
   assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_E)"

lemma symNI_Local_PutXAcksDone : 
             " 
                  symProtRules' N {NI_Local_PutXAcksDone}"
                 

" 
                  wellFormedRule (env N) N (NI_Local_PutXAcksDone)"
                 
 
             unfolding NI_Local_PutXAcksDone_def  apply(auto      )    
 
done

definition NI_Local_PutXAcksDones :: "rule set" where
 "NI_Local_PutXAcksDones \<equiv> {NI_Local_PutXAcksDone}"

definition NI_Remote_PutX :: "nat \<Rightarrow> rule" where
 "NI_Remote_PutX dst \<equiv> 
   IVar (Para ''Sta.UniMsg.Cmd'' dst) =\<^sub>f Const UNI_PutX \<and>\<^sub>f
   IVar (Para ''Sta.Proc.ProcCmd'' dst) =\<^sub>f Const NODE_GetX
  \<triangleright>
   assign (Para ''Sta.UniMsg.Cmd'' dst, Const UNI_None) ||
   assign (Para ''Sta.UniMsg.HomeProc'' dst, Const false) ||
   assign (Para ''Sta.Proc.ProcCmd'' dst, Const NODE_None) ||
   assign (Para ''Sta.Proc.InvMarked'' dst, Const false) ||
   assign (Para ''Sta.Proc.CacheState'' dst, Const CACHE_E)"

lemma symNI_Remote_PutX : 
             " 
                  symParamRule N NI_Remote_PutX"
                 

"[|dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Remote_PutX dst)"
                 
 
             unfolding NI_Remote_PutX_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Remote_PutXs :: "nat \<Rightarrow> rule set" where
 "NI_Remote_PutXs N \<equiv> oneParamCons N NI_Remote_PutX"

definition NI_Inv :: "nat \<Rightarrow> rule" where
 "NI_Inv dst \<equiv> 
   IVar (Para ''Sta.InvMsg.Cmd'' dst) =\<^sub>f Const INV_Inv
  \<triangleright>
   assign (Para ''Sta.InvMsg.Cmd'' dst, Const INV_InvAck) ||
   assign (Para ''Sta.Proc.CacheState'' dst, Const CACHE_I) ||
   assign (Para ''Sta.Proc.InvMarked'' dst, iteForm (IVar (Para ''Sta.Proc.ProcCmd'' dst) =\<^sub>f Const NODE_Get) (Const true) (IVar (Para ''Sta.Proc.InvMarked'' dst)))"

lemma symNI_Inv : 
             " 
                  symParamRule N NI_Inv"
                 

"[|dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Inv dst)"
                 
 
             unfolding NI_Inv_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Invs :: "nat \<Rightarrow> rule set" where
 "NI_Invs N \<equiv> oneParamCons N NI_Inv"

definition NI_InvAck1 :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "NI_InvAck1 N src \<equiv> 
   IVar (Para ''Sta.InvMsg.Cmd'' src) =\<^sub>f Const INV_InvAck \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Para ''Sta.Dir.InvSet'' src) =\<^sub>f Const true \<and>\<^sub>f
   forallFormExcl (\<lambda>p. IVar (Para ''Sta.Dir.InvSet'' p) =\<^sub>f Const false) src N
  \<triangleright>
   assign (Para ''Sta.InvMsg.Cmd'' src, Const INV_None) ||
   assign (Para ''Sta.Dir.InvSet'' src, Const false) ||
   assign (Ident ''Sta.Dir.Pending'', Const false) ||
   (IF IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const false DO
     assign (Ident ''Sta.Dir.Local'', Const false)
   ELSE
     skip
   FI) ||
   assign (Ident ''Sta.Collecting'', Const false)"

lemma symNI_InvAck1 : 
             " 
                  symParamRule N (NI_InvAck1 N)"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_InvAck1 N src)"
                 
 
             unfolding NI_InvAck1_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_InvAck1s :: "nat \<Rightarrow> rule set" where
 "NI_InvAck1s N \<equiv> oneParamCons N (NI_InvAck1 N)"

definition NI_InvAck2 :: "nat \<Rightarrow> rule" where
 "NI_InvAck2 src \<equiv> 
   IVar (Para ''Sta.InvMsg.Cmd'' src) =\<^sub>f Const INV_InvAck \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Para ''Sta.Dir.InvSet'' src) =\<^sub>f Const true
  \<triangleright>
   assign (Para ''Sta.InvMsg.Cmd'' src, Const INV_None) ||
   assign (Para ''Sta.Dir.InvSet'' src, Const false)"

lemma symNI_InvAck2 : 
             " 
                  symParamRule N NI_InvAck2"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_InvAck2 src)"
                 
 
             unfolding NI_InvAck2_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_InvAck2s :: "nat \<Rightarrow> rule set" where
 "NI_InvAck2s N \<equiv> oneParamCons N NI_InvAck2"

definition NI_Wb :: "rule" where
 "NI_Wb \<equiv> 
   IVar (Ident ''Sta.WbMsg.Cmd'') =\<^sub>f Const WB_Wb
  \<triangleright>
   assign (Ident ''Sta.WbMsg.Cmd'', Const WB_None) ||
   assign (Ident ''Sta.Dir.Dirty'', Const false) ||
   assign (Ident ''Sta.Dir.HeadVld'', Const false)"

lemma symNI_Wb : 
             " 
                  symProtRules' N {NI_Wb}"
                 

" 
                  wellFormedRule (env N) N (NI_Wb)"
                 
 
             unfolding NI_Wb_def  apply(auto      )    
 
done

definition NI_Wbs :: "rule set" where
 "NI_Wbs \<equiv> {NI_Wb}"

definition NI_FAck :: "rule" where
 "NI_FAck \<equiv> 
   IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_FAck
  \<triangleright>
   assign (Ident ''Sta.ShWbMsg.Cmd'', Const SHWB_None) ||
   assign (Ident ''Sta.Dir.Pending'', Const false) ||
   (IF IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true DO
     assign (Ident ''Sta.Dir.HeadPtr'', IVar (Ident ''Sta.ShWbMsg.Proc''))
   ELSE
     skip
   FI)"

lemma symNI_FAck : 
             " 
                  symProtRules' N {NI_FAck}"
                 

" 
                  wellFormedRule (env N) N (NI_FAck)"
                 
 
             unfolding NI_FAck_def  apply(auto      )    
 
done

definition NI_FAcks :: "rule set" where
 "NI_FAcks \<equiv> {NI_FAck}"

definition NI_ShWb :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "NI_ShWb N src \<equiv> 
   IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_ShWb \<and>\<^sub>f
   IVar (Ident ''Sta.ShWbMsg.Proc'') =\<^sub>f Const (index src)
  \<triangleright>
   assign (Ident ''Sta.ShWbMsg.Cmd'', Const SHWB_None) ||
   assign (Ident ''Sta.Dir.Pending'', Const false) ||
   assign (Ident ''Sta.Dir.Dirty'', Const false) ||
   assign (Ident ''Sta.Dir.ShrVld'', Const true) ||
   assign (Para ''Sta.Dir.ShrSet'' src, Const true) ||
   assign (Para ''Sta.Dir.InvSet'' src, Const true) ||
   forallStmExcl (\<lambda>p. assign (Para ''Sta.Dir.InvSet'' p, IVar (Para ''Sta.Dir.ShrSet'' p))) src N"

lemma symNI_ShWb : 
             " 
                  symParamRule N (NI_ShWb N)"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_ShWb N src)"
                 
 
             unfolding NI_ShWb_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_ShWbs :: "nat \<Rightarrow> rule set" where
 "NI_ShWbs N \<equiv> oneParamCons N (NI_ShWb N)"

definition NI_Replace :: "nat \<Rightarrow> rule" where
 "NI_Replace src \<equiv> 
   IVar (Para ''Sta.RpMsg.Cmd'' src) =\<^sub>f Const RP_Replace
  \<triangleright>
   assign (Para ''Sta.RpMsg.Cmd'' src, Const RP_None) ||
   (IF IVar (Ident ''Sta.Dir.ShrVld'') =\<^sub>f Const true DO
     assign (Para ''Sta.Dir.ShrSet'' src, Const false) ||
     assign (Para ''Sta.Dir.InvSet'' src, Const false)
   ELSE
     skip
   FI)"

lemma symNI_Replace : 
             " 
                  symParamRule N NI_Replace"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_Replace src)"
                 
 
             unfolding NI_Replace_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Replaces :: "nat \<Rightarrow> rule set" where
 "NI_Replaces N \<equiv> oneParamCons N NI_Replace"

definition CacheStateProp :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "CacheStateProp N p q \<equiv> \<not>\<^sub>f Const (index p) =\<^sub>f Const (index q) \<longrightarrow>\<^sub>f
  \<not>\<^sub>f (IVar (Para ''Sta.Proc.CacheState'' p) =\<^sub>f Const CACHE_E \<and>\<^sub>f
  IVar (Para ''Sta.Proc.CacheState'' q) =\<^sub>f Const CACHE_E)"

definition CacheStateProp_Home :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "CacheStateProp_Home N p q \<equiv> IVar (Para ''Sta.Proc.CacheState'' p) =\<^sub>f Const CACHE_E \<longrightarrow>\<^sub>f
  \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E"

definition ABS_PI_Remote_PutX :: "nat \<Rightarrow> rule" where
 "ABS_PI_Remote_PutX N \<equiv> 
   (\<forall>\<^sub>fp. IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.WbMsg.Cmd'') =\<^sub>f Const WB_Wb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_ShWb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' p) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Put \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.UniMsg.Cmd'' p) =\<^sub>f Const UNI_PutX \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_PutX) N
  \<triangleright>
   assign (Ident ''Sta.WbMsg.Cmd'', Const WB_Wb) ||
   assign (Ident ''Sta.WbMsg.Proc'', Const (index (N + 1)))"

definition ABS_PI_Remote_PutXs :: "nat \<Rightarrow> rule set" where
 "ABS_PI_Remote_PutXs N \<equiv> {ABS_PI_Remote_PutX N}"

definition ABS_NI_Local_Get_Get :: "nat \<Rightarrow> rule" where
 "ABS_NI_Local_Get_Get N \<equiv> 
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false
  \<triangleright>
   assign (Ident ''Sta.Dir.Pending'', Const true) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_Get) ||
   assign (Ident ''Sta.HomePendReqSrc'', Const false) ||
   assign (Ident ''Sta.PendReqSrc'', Const (index (N + 1))) ||
   assign (Ident ''Sta.Collecting'', Const false)"

definition ABS_NI_Local_Get_Gets :: "nat \<Rightarrow> rule set" where
 "ABS_NI_Local_Get_Gets N \<equiv> {ABS_NI_Local_Get_Get N}"

definition ABS_NI_Local_Get_Put :: "nat \<Rightarrow> rule" where
 "ABS_NI_Local_Get_Put N \<equiv> 
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   (IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<longrightarrow>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E)
  \<triangleright>
   (IF IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true DO
     assign (Ident ''Sta.Dir.Dirty'', Const false) ||
     assign (Ident ''Sta.Dir.HeadVld'', Const true) ||
     assign (Ident ''Sta.Dir.HeadPtr'', Const (index (N + 1))) ||
     assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_S)
   ELSE
     IF IVar (Ident ''Sta.Dir.HeadVld'') =\<^sub>f Const true DO
       assign (Ident ''Sta.Dir.ShrVld'', Const true) ||
       forallStm (\<lambda>p. assign (Para ''Sta.Dir.InvSet'' p, IVar (Para ''Sta.Dir.ShrSet'' p))) N
     ELSE
       assign (Ident ''Sta.Dir.HeadVld'', Const true) ||
       assign (Ident ''Sta.Dir.HeadPtr'', Const (index (N + 1)))
     FI
   FI)"

definition ABS_NI_Local_Get_Puts :: "nat \<Rightarrow> rule set" where
 "ABS_NI_Local_Get_Puts N \<equiv> {ABS_NI_Local_Get_Put N}"

definition ABS_NI_Remote_Get_Nak_src :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "ABS_NI_Remote_Get_Nak_src N dst \<equiv> 
   \<not>\<^sub>f Const (index (N + 1)) =\<^sub>f Const (index dst) \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' dst) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_Get
  \<triangleright>
   assign (Ident ''Sta.NakcMsg.Cmd'', Const NAKC_Nakc) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

definition ABS_NI_Remote_Get_Nak_srcs :: "nat \<Rightarrow> rule set" where
 "ABS_NI_Remote_Get_Nak_srcs N \<equiv> oneParamCons N (ABS_NI_Remote_Get_Nak_src N)"

definition ABS_NI_Remote_Get_Nak_dst :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "ABS_NI_Remote_Get_Nak_dst N src \<equiv> 
   \<not>\<^sub>f Const (index src) =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_Get \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const false \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Proc'' src) =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index src) \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_Get
  \<triangleright>
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_Nak) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const false) ||
   assign (Para ''Sta.UniMsg.Proc'' src, Const (index (N + 1))) ||
   assign (Ident ''Sta.NakcMsg.Cmd'', Const NAKC_Nakc) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

definition ABS_NI_Remote_Get_Nak_dsts :: "nat \<Rightarrow> rule set" where
 "ABS_NI_Remote_Get_Nak_dsts N \<equiv> oneParamCons N (ABS_NI_Remote_Get_Nak_dst N)"

definition ABS_NI_Remote_Get_Nak_Home :: "nat \<Rightarrow> rule" where
 "ABS_NI_Remote_Get_Nak_Home N \<equiv> 
   IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Get \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.HomeProc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.Proc'') =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_Get
  \<triangleright>
   assign (Ident ''Sta.HomeUniMsg.Cmd'', Const UNI_Nak) ||
   assign (Ident ''Sta.HomeUniMsg.HomeProc'', Const false) ||
   assign (Ident ''Sta.HomeUniMsg.Proc'', Const (index (N + 1))) ||
   assign (Ident ''Sta.NakcMsg.Cmd'', Const NAKC_Nakc) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

definition ABS_NI_Remote_Get_Nak_Homes :: "nat \<Rightarrow> rule set" where
 "ABS_NI_Remote_Get_Nak_Homes N \<equiv> {ABS_NI_Remote_Get_Nak_Home N}"

definition ABS_NI_Remote_Get_Nak_src_dst :: "nat \<Rightarrow> rule" where
 "ABS_NI_Remote_Get_Nak_src_dst N \<equiv> 
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_Get
  \<triangleright>
   assign (Ident ''Sta.NakcMsg.Cmd'', Const NAKC_Nakc) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

definition ABS_NI_Remote_Get_Nak_src_dsts :: "nat \<Rightarrow> rule set" where
 "ABS_NI_Remote_Get_Nak_src_dsts N \<equiv> {ABS_NI_Remote_Get_Nak_src_dst N}"

definition ABS_NI_Remote_Get_Put_src :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "ABS_NI_Remote_Get_Put_src N dst \<equiv> 
   \<not>\<^sub>f Const (index (N + 1)) =\<^sub>f Const (index dst) \<and>\<^sub>f
   IVar (Para ''Sta.Proc.CacheState'' dst) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   forallFormExcl (\<lambda>p. IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.WbMsg.Cmd'') =\<^sub>f Const WB_Wb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_ShWb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' p) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Put \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.UniMsg.Cmd'' p) =\<^sub>f Const UNI_PutX \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_PutX) dst N \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_Get
  \<triangleright>
   assign (Para ''Sta.Proc.CacheState'' dst, Const CACHE_S) ||
   assign (Ident ''Sta.ShWbMsg.Cmd'', Const SHWB_ShWb) ||
   assign (Ident ''Sta.ShWbMsg.Proc'', Const (index (N + 1))) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

definition ABS_NI_Remote_Get_Put_srcs :: "nat \<Rightarrow> rule set" where
 "ABS_NI_Remote_Get_Put_srcs N \<equiv> oneParamCons N (ABS_NI_Remote_Get_Put_src N)"

definition ABS_NI_Remote_Get_Put_dst :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "ABS_NI_Remote_Get_Put_dst N src \<equiv> 
   \<not>\<^sub>f Const (index src) =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_Get \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const false \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Proc'' src) =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   (\<forall>\<^sub>fp. IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.WbMsg.Cmd'') =\<^sub>f Const WB_Wb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_ShWb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' p) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Put \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.UniMsg.Cmd'' p) =\<^sub>f Const UNI_PutX \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_PutX) N \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index src) \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_Get
  \<triangleright>
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_Put) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const false) ||
   assign (Para ''Sta.UniMsg.Proc'' src, Const (index (N + 1))) ||
   assign (Ident ''Sta.ShWbMsg.Cmd'', Const SHWB_ShWb) ||
   assign (Ident ''Sta.ShWbMsg.Proc'', Const (index src)) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

definition ABS_NI_Remote_Get_Put_dsts :: "nat \<Rightarrow> rule set" where
 "ABS_NI_Remote_Get_Put_dsts N \<equiv> oneParamCons N (ABS_NI_Remote_Get_Put_dst N)"

definition ABS_NI_Remote_Get_Put_Home :: "nat \<Rightarrow> rule" where
 "ABS_NI_Remote_Get_Put_Home N \<equiv> 
   IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Get \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.HomeProc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.Proc'') =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   (\<forall>\<^sub>fp. IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.WbMsg.Cmd'') =\<^sub>f Const WB_Wb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_ShWb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' p) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Put \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.UniMsg.Cmd'' p) =\<^sub>f Const UNI_PutX \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_PutX) N \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_Get
  \<triangleright>
   assign (Ident ''Sta.HomeUniMsg.Cmd'', Const UNI_Put) ||
   assign (Ident ''Sta.HomeUniMsg.HomeProc'', Const false) ||
   assign (Ident ''Sta.HomeUniMsg.Proc'', Const (index (N + 1))) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

definition ABS_NI_Remote_Get_Put_Homes :: "nat \<Rightarrow> rule set" where
 "ABS_NI_Remote_Get_Put_Homes N \<equiv> {ABS_NI_Remote_Get_Put_Home N}"

definition ABS_NI_Remote_Get_Put_src_dst :: "nat \<Rightarrow> rule" where
 "ABS_NI_Remote_Get_Put_src_dst N \<equiv> 
   (\<forall>\<^sub>fp. IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.WbMsg.Cmd'') =\<^sub>f Const WB_Wb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_ShWb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' p) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Put \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.UniMsg.Cmd'' p) =\<^sub>f Const UNI_PutX \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_PutX) N \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_Get
  \<triangleright>
   assign (Ident ''Sta.ShWbMsg.Cmd'', Const SHWB_ShWb) ||
   assign (Ident ''Sta.ShWbMsg.Proc'', Const (index (N + 1))) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

definition ABS_NI_Remote_Get_Put_src_dsts :: "nat \<Rightarrow> rule set" where
 "ABS_NI_Remote_Get_Put_src_dsts N \<equiv> {ABS_NI_Remote_Get_Put_src_dst N}"

definition ABS_NI_Local_GetX_GetX :: "nat \<Rightarrow> rule" where
 "ABS_NI_Local_GetX_GetX N \<equiv> 
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false
  \<triangleright>
   assign (Ident ''Sta.Dir.Pending'', Const true) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_GetX) ||
   assign (Ident ''Sta.HomePendReqSrc'', Const false) ||
   assign (Ident ''Sta.PendReqSrc'', Const (index (N + 1))) ||
   assign (Ident ''Sta.Collecting'', Const false)"

definition ABS_NI_Local_GetX_GetXs :: "nat \<Rightarrow> rule set" where
 "ABS_NI_Local_GetX_GetXs N \<equiv> {ABS_NI_Local_GetX_GetX N}"

definition ABS_NI_Local_GetX_PutX1 :: "nat \<Rightarrow> rule" where
 "ABS_NI_Local_GetX_PutX1 N \<equiv> 
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   (IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<longrightarrow>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E) \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true
  \<triangleright>
   assign (Ident ''Sta.Dir.Local'', Const false) ||
   assign (Ident ''Sta.Dir.Dirty'', Const true) ||
   assign (Ident ''Sta.Dir.HeadVld'', Const true) ||
   assign (Ident ''Sta.Dir.HeadPtr'', Const (index (N + 1))) ||
   assign (Ident ''Sta.Dir.ShrVld'', Const false) ||
   forallStm (\<lambda>p. assign (Para ''Sta.Dir.ShrSet'' p, Const false) ||
   assign (Para ''Sta.Dir.InvSet'' p, Const false)) N ||
   assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_I)"

definition ABS_NI_Local_GetX_PutX1s :: "nat \<Rightarrow> rule set" where
 "ABS_NI_Local_GetX_PutX1s N \<equiv> {ABS_NI_Local_GetX_PutX1 N}"

definition ABS_NI_Local_GetX_PutX2 :: "nat \<Rightarrow> rule" where
 "ABS_NI_Local_GetX_PutX2 N \<equiv> 
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   (IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<longrightarrow>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E) \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const false \<and>\<^sub>f
   (IVar (Ident ''Sta.Dir.HeadVld'') =\<^sub>f Const true \<longrightarrow>\<^sub>f
   IVar (Ident ''Sta.Dir.HeadPtr'') =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   (\<forall>\<^sub>fp. IVar (Para ''Sta.Dir.ShrSet'' p) =\<^sub>f Const false) N)
  \<triangleright>
   assign (Ident ''Sta.Dir.Dirty'', Const true) ||
   assign (Ident ''Sta.Dir.HeadVld'', Const true) ||
   assign (Ident ''Sta.Dir.HeadPtr'', Const (index (N + 1))) ||
   assign (Ident ''Sta.Dir.ShrVld'', Const false) ||
   forallStm (\<lambda>p. assign (Para ''Sta.Dir.ShrSet'' p, Const false) ||
   assign (Para ''Sta.Dir.InvSet'' p, Const false)) N ||
   assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_I) ||
   (IF IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true DO
     assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_I) ||
     (IF IVar (Ident ''Sta.HomeProc.ProcCmd'') =\<^sub>f Const NODE_Get DO
       assign (Ident ''Sta.HomeProc.InvMarked'', Const true)
     ELSE
       skip
     FI)
   ELSE
     skip
   FI) ||
   assign (Ident ''Sta.Dir.Local'', Const false)"

definition ABS_NI_Local_GetX_PutX2s :: "nat \<Rightarrow> rule set" where
 "ABS_NI_Local_GetX_PutX2s N \<equiv> {ABS_NI_Local_GetX_PutX2 N}"

definition ABS_NI_Local_GetX_PutX3 :: "nat \<Rightarrow> rule" where
 "ABS_NI_Local_GetX_PutX3 N \<equiv> 
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   (IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<longrightarrow>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E) \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const false
  \<triangleright>
   assign (Ident ''Sta.Dir.Pending'', Const true) ||
   assign (Ident ''Sta.Dir.Dirty'', Const true) ||
   forallStm (\<lambda>p. assign (Para ''Sta.Dir.InvSet'' p, iteForm (IVar (Ident ''Sta.Dir.ShrVld'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Para ''Sta.Dir.ShrSet'' p) =\<^sub>f Const true \<or>\<^sub>f
   IVar (Ident ''Sta.Dir.HeadVld'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.HeadPtr'') =\<^sub>f Const (index p)) (Const true) (Const false)) ||
   assign (Para ''Sta.InvMsg.Cmd'' p, iteForm (IVar (Ident ''Sta.Dir.ShrVld'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Para ''Sta.Dir.ShrSet'' p) =\<^sub>f Const true \<or>\<^sub>f
   IVar (Ident ''Sta.Dir.HeadVld'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.HeadPtr'') =\<^sub>f Const (index p)) (Const INV_Inv) (Const INV_None)) ||
   assign (Para ''Sta.Dir.ShrSet'' p, Const false)) N ||
   assign (Ident ''Sta.Dir.HeadVld'', Const true) ||
   assign (Ident ''Sta.Dir.HeadPtr'', Const (index (N + 1))) ||
   assign (Ident ''Sta.Dir.ShrVld'', Const false) ||
   (IF IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true DO
     assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_I) ||
     (IF IVar (Ident ''Sta.HomeProc.ProcCmd'') =\<^sub>f Const NODE_Get DO
       assign (Ident ''Sta.HomeProc.InvMarked'', Const true)
     ELSE
       skip
     FI)
   ELSE
     skip
   FI) ||
   assign (Ident ''Sta.Dir.Local'', Const false) ||
   assign (Ident ''Sta.HomePendReqSrc'', Const false) ||
   assign (Ident ''Sta.PendReqSrc'', Const (index (N + 1))) ||
   assign (Ident ''Sta.Collecting'', Const true)"

definition ABS_NI_Local_GetX_PutX3s :: "nat \<Rightarrow> rule set" where
 "ABS_NI_Local_GetX_PutX3s N \<equiv> {ABS_NI_Local_GetX_PutX3 N}"

definition ABS_NI_Remote_GetX_Nak_src :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "ABS_NI_Remote_GetX_Nak_src N dst \<equiv> 
   \<not>\<^sub>f Const (index (N + 1)) =\<^sub>f Const (index dst) \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' dst) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_GetX
  \<triangleright>
   assign (Ident ''Sta.NakcMsg.Cmd'', Const NAKC_Nakc) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

definition ABS_NI_Remote_GetX_Nak_srcs :: "nat \<Rightarrow> rule set" where
 "ABS_NI_Remote_GetX_Nak_srcs N \<equiv> oneParamCons N (ABS_NI_Remote_GetX_Nak_src N)"

definition ABS_NI_Remote_GetX_Nak_dst :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "ABS_NI_Remote_GetX_Nak_dst N src \<equiv> 
   \<not>\<^sub>f Const (index src) =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_GetX \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const false \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Proc'' src) =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index src) \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_GetX
  \<triangleright>
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_Nak) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const false) ||
   assign (Para ''Sta.UniMsg.Proc'' src, Const (index (N + 1))) ||
   assign (Ident ''Sta.NakcMsg.Cmd'', Const NAKC_Nakc) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

definition ABS_NI_Remote_GetX_Nak_dsts :: "nat \<Rightarrow> rule set" where
 "ABS_NI_Remote_GetX_Nak_dsts N \<equiv> oneParamCons N (ABS_NI_Remote_GetX_Nak_dst N)"

definition ABS_NI_Remote_GetX_Nak_Home :: "nat \<Rightarrow> rule" where
 "ABS_NI_Remote_GetX_Nak_Home N \<equiv> 
   IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_GetX \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.HomeProc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.Proc'') =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_GetX
  \<triangleright>
   assign (Ident ''Sta.HomeUniMsg.Cmd'', Const UNI_Nak) ||
   assign (Ident ''Sta.HomeUniMsg.HomeProc'', Const false) ||
   assign (Ident ''Sta.HomeUniMsg.Proc'', Const (index (N + 1))) ||
   assign (Ident ''Sta.NakcMsg.Cmd'', Const NAKC_Nakc) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

definition ABS_NI_Remote_GetX_Nak_Homes :: "nat \<Rightarrow> rule set" where
 "ABS_NI_Remote_GetX_Nak_Homes N \<equiv> {ABS_NI_Remote_GetX_Nak_Home N}"

definition ABS_NI_Remote_GetX_Nak_src_dst :: "nat \<Rightarrow> rule" where
 "ABS_NI_Remote_GetX_Nak_src_dst N \<equiv> 
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_GetX
  \<triangleright>
   assign (Ident ''Sta.NakcMsg.Cmd'', Const NAKC_Nakc) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

definition ABS_NI_Remote_GetX_Nak_src_dsts :: "nat \<Rightarrow> rule set" where
 "ABS_NI_Remote_GetX_Nak_src_dsts N \<equiv> {ABS_NI_Remote_GetX_Nak_src_dst N}"

definition ABS_NI_Remote_GetX_PutX_src :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "ABS_NI_Remote_GetX_PutX_src N dst \<equiv> 
   \<not>\<^sub>f Const (index (N + 1)) =\<^sub>f Const (index dst) \<and>\<^sub>f
   IVar (Para ''Sta.Proc.CacheState'' dst) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   forallFormExcl (\<lambda>p. IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.WbMsg.Cmd'') =\<^sub>f Const WB_Wb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_ShWb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' p) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Put \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.UniMsg.Cmd'' p) =\<^sub>f Const UNI_PutX \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_PutX) dst N \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_GetX
  \<triangleright>
   assign (Para ''Sta.Proc.CacheState'' dst, Const CACHE_I) ||
   assign (Ident ''Sta.ShWbMsg.Cmd'', Const SHWB_FAck) ||
   assign (Ident ''Sta.ShWbMsg.Proc'', Const (index (N + 1))) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

definition ABS_NI_Remote_GetX_PutX_srcs :: "nat \<Rightarrow> rule set" where
 "ABS_NI_Remote_GetX_PutX_srcs N \<equiv> oneParamCons N (ABS_NI_Remote_GetX_PutX_src N)"

definition ABS_NI_Remote_GetX_PutX_dst :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "ABS_NI_Remote_GetX_PutX_dst N src \<equiv> 
   \<not>\<^sub>f Const (index src) =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_GetX \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const false \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Proc'' src) =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   (\<forall>\<^sub>fp. IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.WbMsg.Cmd'') =\<^sub>f Const WB_Wb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_ShWb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' p) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Put \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.UniMsg.Cmd'' p) =\<^sub>f Const UNI_PutX \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_PutX) N \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index src) \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_GetX
  \<triangleright>
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_PutX) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const false) ||
   assign (Para ''Sta.UniMsg.Proc'' src, Const (index (N + 1))) ||
   assign (Ident ''Sta.ShWbMsg.Cmd'', Const SHWB_FAck) ||
   assign (Ident ''Sta.ShWbMsg.Proc'', Const (index src)) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

definition ABS_NI_Remote_GetX_PutX_dsts :: "nat \<Rightarrow> rule set" where
 "ABS_NI_Remote_GetX_PutX_dsts N \<equiv> oneParamCons N (ABS_NI_Remote_GetX_PutX_dst N)"

definition ABS_NI_Remote_GetX_PutX_Home :: "nat \<Rightarrow> rule" where
 "ABS_NI_Remote_GetX_PutX_Home N \<equiv> 
   IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_GetX \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.HomeProc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.Proc'') =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   (\<forall>\<^sub>fp. IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.WbMsg.Cmd'') =\<^sub>f Const WB_Wb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_ShWb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' p) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Put \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.UniMsg.Cmd'' p) =\<^sub>f Const UNI_PutX \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_PutX) N \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_GetX
  \<triangleright>
   assign (Ident ''Sta.HomeUniMsg.Cmd'', Const UNI_PutX) ||
   assign (Ident ''Sta.HomeUniMsg.HomeProc'', Const false) ||
   assign (Ident ''Sta.HomeUniMsg.Proc'', Const (index (N + 1))) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

definition ABS_NI_Remote_GetX_PutX_Homes :: "nat \<Rightarrow> rule set" where
 "ABS_NI_Remote_GetX_PutX_Homes N \<equiv> {ABS_NI_Remote_GetX_PutX_Home N}"

definition ABS_NI_Remote_GetX_PutX_src_dst :: "nat \<Rightarrow> rule" where
 "ABS_NI_Remote_GetX_PutX_src_dst N \<equiv> 
   (\<forall>\<^sub>fp. IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.WbMsg.Cmd'') =\<^sub>f Const WB_Wb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_ShWb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' p) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Put \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.UniMsg.Cmd'' p) =\<^sub>f Const UNI_PutX \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_PutX) N \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_GetX
  \<triangleright>
   assign (Ident ''Sta.ShWbMsg.Cmd'', Const SHWB_FAck) ||
   assign (Ident ''Sta.ShWbMsg.Proc'', Const (index (N + 1))) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

definition ABS_NI_Remote_GetX_PutX_src_dsts :: "nat \<Rightarrow> rule set" where
 "ABS_NI_Remote_GetX_PutX_src_dsts N \<equiv> {ABS_NI_Remote_GetX_PutX_src_dst N}"

definition ABS_NI_InvAck1 :: "nat \<Rightarrow> rule" where
 "ABS_NI_InvAck1 N \<equiv> 
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   (\<forall>\<^sub>fp. IVar (Para ''Sta.Dir.InvSet'' p) =\<^sub>f Const false) N \<and>\<^sub>f
   (\<forall>\<^sub>fq. IVar (Ident ''Sta.Collecting'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.NakcMsg.Cmd'') =\<^sub>f Const NAKC_None \<and>\<^sub>f
   IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_None \<and>\<^sub>f
   (IVar (Para ''Sta.UniMsg.Cmd'' q) =\<^sub>f Const UNI_Get \<or>\<^sub>f
   IVar (Para ''Sta.UniMsg.Cmd'' q) =\<^sub>f Const UNI_GetX \<longrightarrow>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' q) =\<^sub>f Const true) \<and>\<^sub>f
   (IVar (Para ''Sta.UniMsg.Cmd'' q) =\<^sub>f Const UNI_PutX \<longrightarrow>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' q) =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index q))) N
  \<triangleright>
   assign (Ident ''Sta.Dir.Pending'', Const false) ||
   (IF IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const false DO
     assign (Ident ''Sta.Dir.Local'', Const false)
   ELSE
     skip
   FI) ||
   assign (Ident ''Sta.Collecting'', Const false)"

definition ABS_NI_InvAck1s :: "nat \<Rightarrow> rule set" where
 "ABS_NI_InvAck1s N \<equiv> {ABS_NI_InvAck1 N}"

definition ABS_NI_ShWb :: "nat \<Rightarrow> rule" where
 "ABS_NI_ShWb N \<equiv> 
   IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_ShWb \<and>\<^sub>f
   IVar (Ident ''Sta.ShWbMsg.Proc'') =\<^sub>f Const (index (N + 1))
  \<triangleright>
   assign (Ident ''Sta.ShWbMsg.Cmd'', Const SHWB_None) ||
   assign (Ident ''Sta.Dir.Pending'', Const false) ||
   assign (Ident ''Sta.Dir.Dirty'', Const false) ||
   assign (Ident ''Sta.Dir.ShrVld'', Const true) ||
   forallStm (\<lambda>p. assign (Para ''Sta.Dir.InvSet'' p, IVar (Para ''Sta.Dir.ShrSet'' p))) N"

definition ABS_NI_ShWbs :: "nat \<Rightarrow> rule set" where
 "ABS_NI_ShWbs N \<equiv> {ABS_NI_ShWb N}"

definition Lemma_1 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_1 N src dst \<equiv> IVar (Para ''Sta.Proc.CacheState'' dst) =\<^sub>f Const CACHE_E \<longrightarrow>\<^sub>f
  forallFormExcl (\<lambda>p. IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
  \<not>\<^sub>f IVar (Ident ''Sta.WbMsg.Cmd'') =\<^sub>f Const WB_Wb \<and>\<^sub>f
  \<not>\<^sub>f IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_ShWb \<and>\<^sub>f
  \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' p) =\<^sub>f Const CACHE_E \<and>\<^sub>f
  \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E \<and>\<^sub>f
  \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Put \<and>\<^sub>f
  \<not>\<^sub>f IVar (Para ''Sta.UniMsg.Cmd'' p) =\<^sub>f Const UNI_PutX \<and>\<^sub>f
  \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_PutX) dst N"

definition Lemma_2a :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_2a N src dst \<equiv> \<not>\<^sub>f Const (index src) =\<^sub>f Const (index dst) \<and>\<^sub>f
  IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_Get \<and>\<^sub>f
  IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const false \<and>\<^sub>f
  IVar (Para ''Sta.UniMsg.Proc'' src) =\<^sub>f Const (index dst) \<longrightarrow>\<^sub>f
  IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
  IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
  IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
  IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index src) \<and>\<^sub>f
  IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_Get"

definition Lemma_2b :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_2b N src dst \<equiv> IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Get \<and>\<^sub>f
  IVar (Ident ''Sta.HomeUniMsg.HomeProc'') =\<^sub>f Const false \<and>\<^sub>f
  IVar (Ident ''Sta.HomeUniMsg.Proc'') =\<^sub>f Const (index dst) \<longrightarrow>\<^sub>f
  IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
  IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
  IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const true \<and>\<^sub>f
  IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_Get"

definition Lemma_3a :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_3a N src dst \<equiv> \<not>\<^sub>f Const (index src) =\<^sub>f Const (index dst) \<and>\<^sub>f
  IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_GetX \<and>\<^sub>f
  IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const false \<and>\<^sub>f
  IVar (Para ''Sta.UniMsg.Proc'' src) =\<^sub>f Const (index dst) \<longrightarrow>\<^sub>f
  IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
  IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
  IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
  IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index src) \<and>\<^sub>f
  IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_GetX"

definition Lemma_3b :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_3b N src dst \<equiv> IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_GetX \<and>\<^sub>f
  IVar (Ident ''Sta.HomeUniMsg.HomeProc'') =\<^sub>f Const false \<and>\<^sub>f
  IVar (Ident ''Sta.HomeUniMsg.Proc'') =\<^sub>f Const (index dst) \<longrightarrow>\<^sub>f
  IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
  IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
  IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const true \<and>\<^sub>f
  IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_GetX"

definition Lemma_4 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_4 N dst src \<equiv> IVar (Para ''Sta.InvMsg.Cmd'' src) =\<^sub>f Const INV_InvAck \<longrightarrow>\<^sub>f
  forallFormExcl (\<lambda>q. IVar (Ident ''Sta.Collecting'') =\<^sub>f Const true \<and>\<^sub>f
  IVar (Ident ''Sta.NakcMsg.Cmd'') =\<^sub>f Const NAKC_None \<and>\<^sub>f
  IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_None \<and>\<^sub>f
  (IVar (Para ''Sta.UniMsg.Cmd'' q) =\<^sub>f Const UNI_Get \<or>\<^sub>f
  IVar (Para ''Sta.UniMsg.Cmd'' q) =\<^sub>f Const UNI_GetX \<longrightarrow>\<^sub>f
  IVar (Para ''Sta.UniMsg.HomeProc'' q) =\<^sub>f Const true) \<and>\<^sub>f
  (IVar (Para ''Sta.UniMsg.Cmd'' q) =\<^sub>f Const UNI_PutX \<longrightarrow>\<^sub>f
  IVar (Para ''Sta.UniMsg.HomeProc'' q) =\<^sub>f Const true \<and>\<^sub>f
  IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
  IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index q))) src N"

definition rules :: "nat \<Rightarrow> rule set" where
 "rules N = (PI_Remote_Gets N \<union> (PI_Local_Get_Gets \<union> (PI_Local_Get_Puts \<union> (PI_Remote_GetXs N \<union> (PI_Local_GetX_GetXs \<union> (PI_Local_GetX_PutXs N \<union> (PI_Remote_PutXs N \<union> (PI_Local_PutXs \<union> (PI_Remote_Replaces N \<union> (PI_Local_Replaces \<union> (NI_Naks N \<union> (NI_Nak_Homes \<union> (NI_Nak_Clears \<union> (NI_Local_Get_Naks N \<union> (NI_Local_Get_Gets N \<union> (NI_Local_Get_Puts N \<union> (NI_Remote_Get_Naks N \<union> (NI_Remote_Get_Nak_Homes N \<union> (NI_Remote_Get_Puts N \<union> (NI_Remote_Get_Put_Homes N \<union> (NI_Local_GetX_Naks N \<union> (NI_Local_GetX_GetXs N \<union> (NI_Local_GetX_PutX1s N \<union> (NI_Local_GetX_PutX2s N \<union> (NI_Local_GetX_PutX3s N \<union> (NI_Remote_GetX_Naks N \<union> (NI_Remote_GetX_Nak_Homes N \<union> (NI_Remote_GetX_PutXs N \<union> (NI_Remote_GetX_PutX_Homes N \<union> (NI_Local_Puts \<union> (NI_Remote_Puts N \<union> (NI_Local_PutXAcksDones \<union> (NI_Remote_PutXs N \<union> (NI_Invs N \<union> (NI_InvAck1s N \<union> (NI_InvAck2s N \<union> (NI_Wbs \<union> (NI_FAcks \<union> (NI_ShWbs N \<union> NI_Replaces N)))))))))))))))))))))))))))))))))))))))"

lemma deriveAll : 
             "[|r : PI_Remote_Gets N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : PI_Local_Get_Gets|] 
                 ==> deriveRule (env N) r"
                 

"[|r : PI_Local_Get_Puts|] 
                 ==> deriveRule (env N) r"
                 

"[|r : PI_Remote_GetXs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : PI_Local_GetX_GetXs|] 
                 ==> deriveRule (env N) r"
                 

"[|r : PI_Local_GetX_PutXs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : PI_Remote_PutXs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : PI_Local_PutXs|] 
                 ==> deriveRule (env N) r"
                 

"[|r : PI_Remote_Replaces N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : PI_Local_Replaces|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Naks N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Nak_Homes|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Nak_Clears|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Local_Get_Naks N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Local_Get_Gets N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Local_Get_Puts N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Remote_Get_Naks N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Remote_Get_Nak_Homes N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Remote_Get_Puts N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Remote_Get_Put_Homes N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Local_GetX_Naks N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Local_GetX_GetXs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Local_GetX_PutX1s N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Local_GetX_PutX2s N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Local_GetX_PutX3s N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Remote_GetX_Naks N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Remote_GetX_Nak_Homes N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Remote_GetX_PutXs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Remote_GetX_PutX_Homes N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Local_Puts|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Remote_Puts N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Local_PutXAcksDones|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Remote_PutXs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Invs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_InvAck1s N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_InvAck2s N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Wbs|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_FAcks|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_ShWbs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Replaces N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_PI_Remote_PutXs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_Local_Get_Gets N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_Local_Get_Puts N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_Remote_Get_Nak_srcs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_Remote_Get_Nak_dsts N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_Remote_Get_Nak_Homes N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_Remote_Get_Nak_src_dsts N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_Remote_Get_Put_srcs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_Remote_Get_Put_dsts N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_Remote_Get_Put_Homes N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_Remote_Get_Put_src_dsts N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_Local_GetX_GetXs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_Local_GetX_PutX1s N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_Local_GetX_PutX2s N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_Local_GetX_PutX3s N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_Remote_GetX_Nak_srcs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_Remote_GetX_Nak_dsts N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_Remote_GetX_Nak_Homes N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_Remote_GetX_Nak_src_dsts N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_Remote_GetX_PutX_srcs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_Remote_GetX_PutX_dsts N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_Remote_GetX_PutX_Homes N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_Remote_GetX_PutX_src_dsts N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_InvAck1s N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_NI_ShWbs N|] 
                 ==> deriveRule (env N) r"
                 
 
             unfolding deriveRule_def deriveForm_def deriveStmt_def PI_Remote_Gets_def PI_Remote_Get_def PI_Local_Get_Gets_def PI_Local_Get_Get_def PI_Local_Get_Puts_def PI_Local_Get_Put_def PI_Remote_GetXs_def PI_Remote_GetX_def PI_Local_GetX_GetXs_def PI_Local_GetX_GetX_def PI_Local_GetX_PutXs_def PI_Local_GetX_PutX_def PI_Remote_PutXs_def PI_Remote_PutX_def PI_Local_PutXs_def PI_Local_PutX_def PI_Remote_Replaces_def PI_Remote_Replace_def PI_Local_Replaces_def PI_Local_Replace_def NI_Naks_def NI_Nak_def NI_Nak_Homes_def NI_Nak_Home_def NI_Nak_Clears_def NI_Nak_Clear_def NI_Local_Get_Naks_def NI_Local_Get_Nak_def NI_Local_Get_Gets_def NI_Local_Get_Get_def NI_Local_Get_Puts_def NI_Local_Get_Put_def NI_Remote_Get_Naks_def NI_Remote_Get_Nak_def NI_Remote_Get_Nak_Homes_def NI_Remote_Get_Nak_Home_def NI_Remote_Get_Puts_def NI_Remote_Get_Put_def NI_Remote_Get_Put_Homes_def NI_Remote_Get_Put_Home_def NI_Local_GetX_Naks_def NI_Local_GetX_Nak_def NI_Local_GetX_GetXs_def NI_Local_GetX_GetX_def NI_Local_GetX_PutX1s_def NI_Local_GetX_PutX1_def NI_Local_GetX_PutX2s_def NI_Local_GetX_PutX2_def NI_Local_GetX_PutX3s_def NI_Local_GetX_PutX3_def NI_Remote_GetX_Naks_def NI_Remote_GetX_Nak_def NI_Remote_GetX_Nak_Homes_def NI_Remote_GetX_Nak_Home_def NI_Remote_GetX_PutXs_def NI_Remote_GetX_PutX_def NI_Remote_GetX_PutX_Homes_def NI_Remote_GetX_PutX_Home_def NI_Local_Puts_def NI_Local_Put_def NI_Remote_Puts_def NI_Remote_Put_def NI_Local_PutXAcksDones_def NI_Local_PutXAcksDone_def NI_Remote_PutXs_def NI_Remote_PutX_def NI_Invs_def NI_Inv_def NI_InvAck1s_def NI_InvAck1_def NI_InvAck2s_def NI_InvAck2_def NI_Wbs_def NI_Wb_def NI_FAcks_def NI_FAck_def NI_ShWbs_def NI_ShWb_def NI_Replaces_def NI_Replace_def ABS_PI_Remote_PutXs_def ABS_PI_Remote_PutX_def ABS_NI_Local_Get_Gets_def ABS_NI_Local_Get_Get_def ABS_NI_Local_Get_Puts_def ABS_NI_Local_Get_Put_def ABS_NI_Remote_Get_Nak_srcs_def ABS_NI_Remote_Get_Nak_src_def ABS_NI_Remote_Get_Nak_dsts_def ABS_NI_Remote_Get_Nak_dst_def ABS_NI_Remote_Get_Nak_Homes_def ABS_NI_Remote_Get_Nak_Home_def ABS_NI_Remote_Get_Nak_src_dsts_def ABS_NI_Remote_Get_Nak_src_dst_def ABS_NI_Remote_Get_Put_srcs_def ABS_NI_Remote_Get_Put_src_def ABS_NI_Remote_Get_Put_dsts_def ABS_NI_Remote_Get_Put_dst_def ABS_NI_Remote_Get_Put_Homes_def ABS_NI_Remote_Get_Put_Home_def ABS_NI_Remote_Get_Put_src_dsts_def ABS_NI_Remote_Get_Put_src_dst_def ABS_NI_Local_GetX_GetXs_def ABS_NI_Local_GetX_GetX_def ABS_NI_Local_GetX_PutX1s_def ABS_NI_Local_GetX_PutX1_def ABS_NI_Local_GetX_PutX2s_def ABS_NI_Local_GetX_PutX2_def ABS_NI_Local_GetX_PutX3s_def ABS_NI_Local_GetX_PutX3_def ABS_NI_Remote_GetX_Nak_srcs_def ABS_NI_Remote_GetX_Nak_src_def ABS_NI_Remote_GetX_Nak_dsts_def ABS_NI_Remote_GetX_Nak_dst_def ABS_NI_Remote_GetX_Nak_Homes_def ABS_NI_Remote_GetX_Nak_Home_def ABS_NI_Remote_GetX_Nak_src_dsts_def ABS_NI_Remote_GetX_Nak_src_dst_def ABS_NI_Remote_GetX_PutX_srcs_def ABS_NI_Remote_GetX_PutX_src_def ABS_NI_Remote_GetX_PutX_dsts_def ABS_NI_Remote_GetX_PutX_dst_def ABS_NI_Remote_GetX_PutX_Homes_def ABS_NI_Remote_GetX_PutX_Home_def ABS_NI_Remote_GetX_PutX_src_dsts_def ABS_NI_Remote_GetX_PutX_src_dst_def ABS_NI_InvAck1s_def ABS_NI_InvAck1_def ABS_NI_ShWbs_def ABS_NI_ShWb_def  apply(auto      )    
 
done

lemma symProtAll : 
             " 
                  symProtRules' N (PI_Remote_Gets N)"
                 

" 
                  symProtRules' N (PI_Local_Get_Gets)"
                 

" 
                  symProtRules' N (PI_Local_Get_Puts)"
                 

" 
                  symProtRules' N (PI_Remote_GetXs N)"
                 

" 
                  symProtRules' N (PI_Local_GetX_GetXs)"
                 

" 
                  symProtRules' N (PI_Local_GetX_PutXs N)"
                 

" 
                  symProtRules' N (PI_Remote_PutXs N)"
                 

" 
                  symProtRules' N (PI_Local_PutXs)"
                 

" 
                  symProtRules' N (PI_Remote_Replaces N)"
                 

" 
                  symProtRules' N (PI_Local_Replaces)"
                 

" 
                  symProtRules' N (NI_Naks N)"
                 

" 
                  symProtRules' N (NI_Nak_Homes)"
                 

" 
                  symProtRules' N (NI_Nak_Clears)"
                 

" 
                  symProtRules' N (NI_Local_Get_Naks N)"
                 

" 
                  symProtRules' N (NI_Local_Get_Gets N)"
                 

" 
                  symProtRules' N (NI_Local_Get_Puts N)"
                 

" 
                  symProtRules' N (NI_Remote_Get_Naks N)"
                 

" 
                  symProtRules' N (NI_Remote_Get_Nak_Homes N)"
                 

" 
                  symProtRules' N (NI_Remote_Get_Puts N)"
                 

" 
                  symProtRules' N (NI_Remote_Get_Put_Homes N)"
                 

" 
                  symProtRules' N (NI_Local_GetX_Naks N)"
                 

" 
                  symProtRules' N (NI_Local_GetX_GetXs N)"
                 

" 
                  symProtRules' N (NI_Local_GetX_PutX1s N)"
                 

" 
                  symProtRules' N (NI_Local_GetX_PutX2s N)"
                 

" 
                  symProtRules' N (NI_Local_GetX_PutX3s N)"
                 

" 
                  symProtRules' N (NI_Remote_GetX_Naks N)"
                 

" 
                  symProtRules' N (NI_Remote_GetX_Nak_Homes N)"
                 

" 
                  symProtRules' N (NI_Remote_GetX_PutXs N)"
                 

" 
                  symProtRules' N (NI_Remote_GetX_PutX_Homes N)"
                 

" 
                  symProtRules' N (NI_Local_Puts)"
                 

" 
                  symProtRules' N (NI_Remote_Puts N)"
                 

" 
                  symProtRules' N (NI_Local_PutXAcksDones)"
                 

" 
                  symProtRules' N (NI_Remote_PutXs N)"
                 

" 
                  symProtRules' N (NI_Invs N)"
                 

" 
                  symProtRules' N (NI_InvAck1s N)"
                 

" 
                  symProtRules' N (NI_InvAck2s N)"
                 

" 
                  symProtRules' N (NI_Wbs)"
                 

" 
                  symProtRules' N (NI_FAcks)"
                 

" 
                  symProtRules' N (NI_ShWbs N)"
                 

" 
                  symProtRules' N (NI_Replaces N)"
                 
 
              using symPI_Remote_Get(1) PI_Remote_Gets_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symPI_Local_Get_Get(1) PI_Local_Get_Gets_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symPI_Local_Get_Put(1) PI_Local_Get_Puts_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symPI_Remote_GetX(1) PI_Remote_GetXs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symPI_Local_GetX_GetX(1) PI_Local_GetX_GetXs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symPI_Local_GetX_PutX(1) PI_Local_GetX_PutXs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symPI_Remote_PutX(1) PI_Remote_PutXs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symPI_Local_PutX(1) PI_Local_PutXs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symPI_Remote_Replace(1) PI_Remote_Replaces_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symPI_Local_Replace(1) PI_Local_Replaces_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Nak(1) NI_Naks_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Nak_Home(1) NI_Nak_Homes_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Nak_Clear(1) NI_Nak_Clears_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Local_Get_Nak(1) NI_Local_Get_Naks_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Local_Get_Get(1) NI_Local_Get_Gets_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Local_Get_Put(1) NI_Local_Get_Puts_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Remote_Get_Nak(1) NI_Remote_Get_Naks_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Remote_Get_Nak_Home(1) NI_Remote_Get_Nak_Homes_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Remote_Get_Put(1) NI_Remote_Get_Puts_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Remote_Get_Put_Home(1) NI_Remote_Get_Put_Homes_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Local_GetX_Nak(1) NI_Local_GetX_Naks_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Local_GetX_GetX(1) NI_Local_GetX_GetXs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Local_GetX_PutX1(1) NI_Local_GetX_PutX1s_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Local_GetX_PutX2(1) NI_Local_GetX_PutX2s_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Local_GetX_PutX3(1) NI_Local_GetX_PutX3s_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Remote_GetX_Nak(1) NI_Remote_GetX_Naks_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Remote_GetX_Nak_Home(1) NI_Remote_GetX_Nak_Homes_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Remote_GetX_PutX(1) NI_Remote_GetX_PutXs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Remote_GetX_PutX_Home(1) NI_Remote_GetX_PutX_Homes_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Local_Put(1) NI_Local_Puts_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Remote_Put(1) NI_Remote_Puts_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Local_PutXAcksDone(1) NI_Local_PutXAcksDones_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Remote_PutX(1) NI_Remote_PutXs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Inv(1) NI_Invs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_InvAck1(1) NI_InvAck1s_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_InvAck2(1) NI_InvAck2s_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Wb(1) NI_Wbs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_FAck(1) NI_FAcks_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_ShWb(1) NI_ShWbs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symNI_Replace(1) NI_Replaces_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
done

lemma symCacheStateProp : 
                  " 
                  symParamForm2 N (CacheStateProp N)"
                 unfolding CacheStateProp_def  apply(auto      )    
 
  apply(intro  symParamForm2Imply symParamFormForallExcl2 )

unfolding symParamForm2_def  apply(auto      )    
 
done

lemma symCacheStateProp_Home : 
                  " 
                  symParamForm2 N (CacheStateProp_Home N)"
                 unfolding CacheStateProp_Home_def  apply(auto      )    
 
  apply(intro  symParamForm2Imply symParamFormForallExcl2 )

unfolding symParamForm2_def  apply(auto      )    
 
done

lemma symLemma_1 : 
                  " 
                  symParamForm2 N (Lemma_1 N)"
                 unfolding Lemma_1_def  apply(auto      )    
 
  apply(intro  symParamForm2Imply symParamFormForallExcl2 )

unfolding symParamForm2_def  apply(auto      )    
 
done

lemma symLemma_2a : 
                  " 
                  symParamForm2 N (Lemma_2a N)"
                 unfolding Lemma_2a_def  apply(auto      )    
 
  apply(intro  symParamForm2Imply symParamFormForallExcl2 )

unfolding symParamForm2_def  apply(auto      )    
 
done

lemma symLemma_2b : 
                  " 
                  symParamForm2 N (Lemma_2b N)"
                 unfolding Lemma_2b_def  apply(auto      )    
 
  apply(intro  symParamForm2Imply symParamFormForallExcl2 )

unfolding symParamForm2_def  apply(auto      )    
 
done

lemma symLemma_3a : 
                  " 
                  symParamForm2 N (Lemma_3a N)"
                 unfolding Lemma_3a_def  apply(auto      )    
 
  apply(intro  symParamForm2Imply symParamFormForallExcl2 )

unfolding symParamForm2_def  apply(auto      )    
 
done

lemma symLemma_3b : 
                  " 
                  symParamForm2 N (Lemma_3b N)"
                 unfolding Lemma_3b_def  apply(auto      )    
 
  apply(intro  symParamForm2Imply symParamFormForallExcl2 )

unfolding symParamForm2_def  apply(auto      )    
 
done

lemma symLemma_4 : 
                  " 
                  symParamForm2 N (Lemma_4 N)"
                 unfolding Lemma_4_def  apply(auto      )    
 
  apply(intro  symParamForm2Imply symParamFormForallExcl2 )

unfolding symParamForm2_def  apply(auto      )    
 
done

definition lemmasFor_PI_Remote_Get :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_PI_Remote_Get N = []"

definition PI_Remote_Get_ref :: "nat \<Rightarrow> rule" where
 "PI_Remote_Get_ref src \<equiv> 
   IVar (Para ''Sta.Proc.ProcCmd'' src) =\<^sub>f Const NODE_None \<and>\<^sub>f
   IVar (Para ''Sta.Proc.CacheState'' src) =\<^sub>f Const CACHE_I
  \<triangleright>
   assign (Para ''Sta.Proc.ProcCmd'' src, Const NODE_Get) ||
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_Get) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const true)"

lemma symPI_Remote_Get_ref : 
             " 
                  symParamRule N PI_Remote_Get_ref"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (PI_Remote_Get_ref src)"
                 
 
             unfolding PI_Remote_Get_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition PI_Remote_Get_refs :: "nat \<Rightarrow> rule set" where
 "PI_Remote_Get_refs N \<equiv> oneParamCons N PI_Remote_Get_ref"

lemma PI_Remote_Get_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_PI_Remote_Get N) j i) (PI_Remote_Get i) = PI_Remote_Get_ref i"
                 unfolding lemmasFor_PI_Remote_Get_def  PI_Remote_Get_def PI_Remote_Get_ref_def  apply(auto      )    
 
done

lemma abs_PI_Remote_Get_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (PI_Remote_Get_ref i) = PI_Remote_Get_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (PI_Remote_Get_ref i) = skipRule"
                 
 
             unfolding PI_Remote_Get_ref_def PI_Remote_Get_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_PI_Local_Get_Get :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_PI_Local_Get_Get N = []"

definition PI_Local_Get_Get_ref :: "rule" where
 "PI_Local_Get_Get_ref \<equiv> 
   IVar (Ident ''Sta.HomeProc.ProcCmd'') =\<^sub>f Const NODE_None \<and>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_I \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true
  \<triangleright>
   assign (Ident ''Sta.HomeProc.ProcCmd'', Const NODE_Get) ||
   assign (Ident ''Sta.Dir.Pending'', Const true) ||
   assign (Ident ''Sta.HomeUniMsg.Cmd'', Const UNI_Get) ||
   assign (Ident ''Sta.HomeUniMsg.HomeProc'', Const false) ||
   assign (Ident ''Sta.HomeUniMsg.Proc'', IVar (Ident ''Sta.Dir.HeadPtr'')) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_Get) ||
   assign (Ident ''Sta.HomePendReqSrc'', Const true) ||
   assign (Ident ''Sta.Collecting'', Const false)"

lemma symPI_Local_Get_Get_ref : 
             " 
                  symProtRules' N {PI_Local_Get_Get_ref}"
                 

" 
                  wellFormedRule (env N) N (PI_Local_Get_Get_ref)"
                 
 
             unfolding PI_Local_Get_Get_ref_def  apply(auto      )    
 
done

definition PI_Local_Get_Get_refs :: "rule set" where
 "PI_Local_Get_Get_refs \<equiv> {PI_Local_Get_Get_ref}"

lemma PI_Local_Get_Get_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_PI_Local_Get_Get N) j i) (PI_Local_Get_Get) = PI_Local_Get_Get_ref"
                 unfolding lemmasFor_PI_Local_Get_Get_def  PI_Local_Get_Get_def PI_Local_Get_Get_ref_def  apply(auto      )    
 
done

lemma abs_PI_Local_Get_Get : 
             "[|M <= N|] 
                 ==> absTransfRule (env N) M (PI_Local_Get_Get_ref) = PI_Local_Get_Get_ref"
                 
 
             unfolding PI_Local_Get_Get_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_PI_Local_Get_Put :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_PI_Local_Get_Put N = []"

definition PI_Local_Get_Put_ref :: "rule" where
 "PI_Local_Get_Put_ref \<equiv> 
   IVar (Ident ''Sta.HomeProc.ProcCmd'') =\<^sub>f Const NODE_None \<and>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_I \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const false
  \<triangleright>
   assign (Ident ''Sta.Dir.Local'', Const true) ||
   assign (Ident ''Sta.HomeProc.ProcCmd'', Const NODE_None) ||
   (IF IVar (Ident ''Sta.HomeProc.InvMarked'') =\<^sub>f Const true DO
     assign (Ident ''Sta.HomeProc.InvMarked'', Const false) ||
     assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_I)
   ELSE
     assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_S)
   FI)"

lemma symPI_Local_Get_Put_ref : 
             " 
                  symProtRules' N {PI_Local_Get_Put_ref}"
                 

" 
                  wellFormedRule (env N) N (PI_Local_Get_Put_ref)"
                 
 
             unfolding PI_Local_Get_Put_ref_def  apply(auto      )    
 
done

definition PI_Local_Get_Put_refs :: "rule set" where
 "PI_Local_Get_Put_refs \<equiv> {PI_Local_Get_Put_ref}"

lemma PI_Local_Get_Put_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_PI_Local_Get_Put N) j i) (PI_Local_Get_Put) = PI_Local_Get_Put_ref"
                 unfolding lemmasFor_PI_Local_Get_Put_def  PI_Local_Get_Put_def PI_Local_Get_Put_ref_def  apply(auto      )    
 
done

lemma abs_PI_Local_Get_Put : 
             "[|M <= N|] 
                 ==> absTransfRule (env N) M (PI_Local_Get_Put_ref) = PI_Local_Get_Put_ref"
                 
 
             unfolding PI_Local_Get_Put_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_PI_Remote_GetX :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_PI_Remote_GetX N = []"

definition PI_Remote_GetX_ref :: "nat \<Rightarrow> rule" where
 "PI_Remote_GetX_ref src \<equiv> 
   IVar (Para ''Sta.Proc.ProcCmd'' src) =\<^sub>f Const NODE_None \<and>\<^sub>f
   IVar (Para ''Sta.Proc.CacheState'' src) =\<^sub>f Const CACHE_I
  \<triangleright>
   assign (Para ''Sta.Proc.ProcCmd'' src, Const NODE_GetX) ||
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_GetX) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const true)"

lemma symPI_Remote_GetX_ref : 
             " 
                  symParamRule N PI_Remote_GetX_ref"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (PI_Remote_GetX_ref src)"
                 
 
             unfolding PI_Remote_GetX_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition PI_Remote_GetX_refs :: "nat \<Rightarrow> rule set" where
 "PI_Remote_GetX_refs N \<equiv> oneParamCons N PI_Remote_GetX_ref"

lemma PI_Remote_GetX_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_PI_Remote_GetX N) j i) (PI_Remote_GetX i) = PI_Remote_GetX_ref i"
                 unfolding lemmasFor_PI_Remote_GetX_def  PI_Remote_GetX_def PI_Remote_GetX_ref_def  apply(auto      )    
 
done

lemma abs_PI_Remote_GetX_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (PI_Remote_GetX_ref i) = PI_Remote_GetX_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (PI_Remote_GetX_ref i) = skipRule"
                 
 
             unfolding PI_Remote_GetX_ref_def PI_Remote_GetX_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_PI_Local_GetX_GetX :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_PI_Local_GetX_GetX N = []"

definition PI_Local_GetX_GetX_ref :: "rule" where
 "PI_Local_GetX_GetX_ref \<equiv> 
   IVar (Ident ''Sta.HomeProc.ProcCmd'') =\<^sub>f Const NODE_None \<and>\<^sub>f
   (IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_I \<or>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_S) \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true
  \<triangleright>
   assign (Ident ''Sta.HomeProc.ProcCmd'', Const NODE_GetX) ||
   assign (Ident ''Sta.Dir.Pending'', Const true) ||
   assign (Ident ''Sta.HomeUniMsg.Cmd'', Const UNI_GetX) ||
   assign (Ident ''Sta.HomeUniMsg.HomeProc'', Const false) ||
   assign (Ident ''Sta.HomeUniMsg.Proc'', IVar (Ident ''Sta.Dir.HeadPtr'')) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_GetX) ||
   assign (Ident ''Sta.HomePendReqSrc'', Const true) ||
   assign (Ident ''Sta.Collecting'', Const false)"

lemma symPI_Local_GetX_GetX_ref : 
             " 
                  symProtRules' N {PI_Local_GetX_GetX_ref}"
                 

" 
                  wellFormedRule (env N) N (PI_Local_GetX_GetX_ref)"
                 
 
             unfolding PI_Local_GetX_GetX_ref_def  apply(auto      )    
 
done

definition PI_Local_GetX_GetX_refs :: "rule set" where
 "PI_Local_GetX_GetX_refs \<equiv> {PI_Local_GetX_GetX_ref}"

lemma PI_Local_GetX_GetX_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_PI_Local_GetX_GetX N) j i) (PI_Local_GetX_GetX) = PI_Local_GetX_GetX_ref"
                 unfolding lemmasFor_PI_Local_GetX_GetX_def  PI_Local_GetX_GetX_def PI_Local_GetX_GetX_ref_def  apply(auto      )    
 
done

lemma abs_PI_Local_GetX_GetX : 
             "[|M <= N|] 
                 ==> absTransfRule (env N) M (PI_Local_GetX_GetX_ref) = PI_Local_GetX_GetX_ref"
                 
 
             unfolding PI_Local_GetX_GetX_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_PI_Local_GetX_PutX :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_PI_Local_GetX_PutX N = []"

definition PI_Local_GetX_PutX_ref :: "nat \<Rightarrow> rule" where
 "PI_Local_GetX_PutX_ref N \<equiv> 
   IVar (Ident ''Sta.HomeProc.ProcCmd'') =\<^sub>f Const NODE_None \<and>\<^sub>f
   (IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_I \<or>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_S) \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const false
  \<triangleright>
   assign (Ident ''Sta.Dir.Local'', Const true) ||
   assign (Ident ''Sta.Dir.Dirty'', Const true) ||
   (IF IVar (Ident ''Sta.Dir.HeadVld'') =\<^sub>f Const true DO
     assign (Ident ''Sta.Dir.Pending'', Const true) ||
     forallStm (\<lambda>p. assign (Para ''Sta.Dir.InvSet'' p, iteForm (IVar (Ident ''Sta.Dir.ShrVld'') =\<^sub>f Const true \<and>\<^sub>f
     IVar (Para ''Sta.Dir.ShrSet'' p) =\<^sub>f Const true \<or>\<^sub>f
     IVar (Ident ''Sta.Dir.HeadVld'') =\<^sub>f Const true \<and>\<^sub>f
     IVar (Ident ''Sta.Dir.HeadPtr'') =\<^sub>f Const (index p)) (Const true) (Const false)) ||
     assign (Para ''Sta.InvMsg.Cmd'' p, iteForm (IVar (Ident ''Sta.Dir.ShrVld'') =\<^sub>f Const true \<and>\<^sub>f
     IVar (Para ''Sta.Dir.ShrSet'' p) =\<^sub>f Const true \<or>\<^sub>f
     IVar (Ident ''Sta.Dir.HeadVld'') =\<^sub>f Const true \<and>\<^sub>f
     IVar (Ident ''Sta.Dir.HeadPtr'') =\<^sub>f Const (index p)) (Const INV_Inv) (Const INV_None)) ||
     assign (Para ''Sta.Dir.ShrSet'' p, Const false)) N ||
     assign (Ident ''Sta.Dir.HeadVld'', Const false) ||
     assign (Ident ''Sta.Dir.ShrVld'', Const false) ||
     assign (Ident ''Sta.Collecting'', Const true)
   ELSE
     skip
   FI) ||
   assign (Ident ''Sta.HomeProc.ProcCmd'', Const NODE_None) ||
   assign (Ident ''Sta.HomeProc.InvMarked'', Const false) ||
   assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_E)"

lemma symPI_Local_GetX_PutX_ref : 
             " 
                  symProtRules' N {PI_Local_GetX_PutX_ref N}"
                 

" 
                  wellFormedRule (env N) N (PI_Local_GetX_PutX_ref N)"
                 
 
             unfolding PI_Local_GetX_PutX_ref_def  apply(auto intro!: equivStatementParallel equivStatementIteStm equivStatementPermute     )    
 
   apply(rule equivStatementSym)
   apply(rule equivStatementPermute)
  apply(auto     simp add: mutualDiffVars_def )    
 
done

definition PI_Local_GetX_PutX_refs :: "nat \<Rightarrow> rule set" where
 "PI_Local_GetX_PutX_refs N \<equiv> {PI_Local_GetX_PutX_ref N}"

lemma PI_Local_GetX_PutX_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_PI_Local_GetX_PutX N) j i) (PI_Local_GetX_PutX N) = PI_Local_GetX_PutX_ref N"
                 unfolding lemmasFor_PI_Local_GetX_PutX_def  PI_Local_GetX_PutX_def PI_Local_GetX_PutX_ref_def  apply(auto      )    
 
done

lemma abs_PI_Local_GetX_PutX : 
             "[|M <= N|] 
                 ==> absTransfRule (env N) M (PI_Local_GetX_PutX_ref M) = PI_Local_GetX_PutX_ref M"
                 
 
             unfolding PI_Local_GetX_PutX_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_PI_Remote_PutX :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_PI_Remote_PutX N = [Lemma_1 N]"

definition PI_Remote_PutX_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "PI_Remote_PutX_ref N dst \<equiv> 
   IVar (Para ''Sta.Proc.ProcCmd'' dst) =\<^sub>f Const NODE_None \<and>\<^sub>f
   IVar (Para ''Sta.Proc.CacheState'' dst) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   forallFormExcl (\<lambda>p. IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.WbMsg.Cmd'') =\<^sub>f Const WB_Wb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_ShWb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' p) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Put \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.UniMsg.Cmd'' p) =\<^sub>f Const UNI_PutX \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_PutX) dst N
  \<triangleright>
   assign (Para ''Sta.Proc.CacheState'' dst, Const CACHE_I) ||
   assign (Ident ''Sta.WbMsg.Cmd'', Const WB_Wb) ||
   assign (Ident ''Sta.WbMsg.Proc'', Const (index dst))"

lemma symPI_Remote_PutX_ref : 
             " 
                  symParamRule N (PI_Remote_PutX_ref N)"
                 

"[|dst <= N|] 
                 ==> wellFormedRule (env N) N (PI_Remote_PutX_ref N dst)"
                 
 
             unfolding PI_Remote_PutX_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition PI_Remote_PutX_refs :: "nat \<Rightarrow> rule set" where
 "PI_Remote_PutX_refs N \<equiv> oneParamCons N (PI_Remote_PutX_ref N)"

lemma PI_Remote_PutX_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_PI_Remote_PutX N) j i) (PI_Remote_PutX i) = PI_Remote_PutX_ref N i"
                 unfolding lemmasFor_PI_Remote_PutX_def Lemma_1_def PI_Remote_PutX_def PI_Remote_PutX_ref_def  apply(auto      )    
 
done

lemma abs_PI_Remote_PutX_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (PI_Remote_PutX_ref N i) = PI_Remote_PutX_ref M i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (PI_Remote_PutX_ref N i) = ABS_PI_Remote_PutX M"
                 
 
             unfolding PI_Remote_PutX_ref_def PI_Remote_PutX_ref_def ABS_PI_Remote_PutX_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_PI_Local_PutX :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_PI_Local_PutX N = []"

definition PI_Local_PutX_ref :: "rule" where
 "PI_Local_PutX_ref \<equiv> 
   IVar (Ident ''Sta.HomeProc.ProcCmd'') =\<^sub>f Const NODE_None \<and>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E
  \<triangleright>
   (IF IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true DO
     assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_I) ||
     assign (Ident ''Sta.Dir.Dirty'', Const false)
   ELSE
     assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_I) ||
     assign (Ident ''Sta.Dir.Local'', Const false) ||
     assign (Ident ''Sta.Dir.Dirty'', Const false)
   FI)"

lemma symPI_Local_PutX_ref : 
             " 
                  symProtRules' N {PI_Local_PutX_ref}"
                 

" 
                  wellFormedRule (env N) N (PI_Local_PutX_ref)"
                 
 
             unfolding PI_Local_PutX_ref_def  apply(auto      )    
 
done

definition PI_Local_PutX_refs :: "rule set" where
 "PI_Local_PutX_refs \<equiv> {PI_Local_PutX_ref}"

lemma PI_Local_PutX_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_PI_Local_PutX N) j i) (PI_Local_PutX) = PI_Local_PutX_ref"
                 unfolding lemmasFor_PI_Local_PutX_def  PI_Local_PutX_def PI_Local_PutX_ref_def  apply(auto      )    
 
done

lemma abs_PI_Local_PutX : 
             "[|M <= N|] 
                 ==> absTransfRule (env N) M (PI_Local_PutX_ref) = PI_Local_PutX_ref"
                 
 
             unfolding PI_Local_PutX_ref_def ABS_PI_Remote_PutX_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_PI_Remote_Replace :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_PI_Remote_Replace N = []"

definition PI_Remote_Replace_ref :: "nat \<Rightarrow> rule" where
 "PI_Remote_Replace_ref src \<equiv> 
   IVar (Para ''Sta.Proc.ProcCmd'' src) =\<^sub>f Const NODE_None \<and>\<^sub>f
   IVar (Para ''Sta.Proc.CacheState'' src) =\<^sub>f Const CACHE_S
  \<triangleright>
   assign (Para ''Sta.Proc.CacheState'' src, Const CACHE_I) ||
   assign (Para ''Sta.RpMsg.Cmd'' src, Const RP_Replace)"

lemma symPI_Remote_Replace_ref : 
             " 
                  symParamRule N PI_Remote_Replace_ref"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (PI_Remote_Replace_ref src)"
                 
 
             unfolding PI_Remote_Replace_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition PI_Remote_Replace_refs :: "nat \<Rightarrow> rule set" where
 "PI_Remote_Replace_refs N \<equiv> oneParamCons N PI_Remote_Replace_ref"

lemma PI_Remote_Replace_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_PI_Remote_Replace N) j i) (PI_Remote_Replace i) = PI_Remote_Replace_ref i"
                 unfolding lemmasFor_PI_Remote_Replace_def  PI_Remote_Replace_def PI_Remote_Replace_ref_def  apply(auto      )    
 
done

lemma abs_PI_Remote_Replace_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (PI_Remote_Replace_ref i) = PI_Remote_Replace_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (PI_Remote_Replace_ref i) = skipRule"
                 
 
             unfolding PI_Remote_Replace_ref_def PI_Remote_Replace_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_PI_Local_Replace :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_PI_Local_Replace N = []"

definition PI_Local_Replace_ref :: "rule" where
 "PI_Local_Replace_ref \<equiv> 
   IVar (Ident ''Sta.HomeProc.ProcCmd'') =\<^sub>f Const NODE_None \<and>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_S
  \<triangleright>
   assign (Ident ''Sta.Dir.Local'', Const false) ||
   assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_I)"

lemma symPI_Local_Replace_ref : 
             " 
                  symProtRules' N {PI_Local_Replace_ref}"
                 

" 
                  wellFormedRule (env N) N (PI_Local_Replace_ref)"
                 
 
             unfolding PI_Local_Replace_ref_def  apply(auto      )    
 
done

definition PI_Local_Replace_refs :: "rule set" where
 "PI_Local_Replace_refs \<equiv> {PI_Local_Replace_ref}"

lemma PI_Local_Replace_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_PI_Local_Replace N) j i) (PI_Local_Replace) = PI_Local_Replace_ref"
                 unfolding lemmasFor_PI_Local_Replace_def  PI_Local_Replace_def PI_Local_Replace_ref_def  apply(auto      )    
 
done

lemma abs_PI_Local_Replace : 
             "[|M <= N|] 
                 ==> absTransfRule (env N) M (PI_Local_Replace_ref) = PI_Local_Replace_ref"
                 
 
             unfolding PI_Local_Replace_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Nak :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Nak N = []"

definition NI_Nak_ref :: "nat \<Rightarrow> rule" where
 "NI_Nak_ref dst \<equiv> 
   IVar (Para ''Sta.UniMsg.Cmd'' dst) =\<^sub>f Const UNI_Nak
  \<triangleright>
   assign (Para ''Sta.UniMsg.Cmd'' dst, Const UNI_None) ||
   assign (Para ''Sta.UniMsg.HomeProc'' dst, Const false) ||
   assign (Para ''Sta.Proc.ProcCmd'' dst, Const NODE_None) ||
   assign (Para ''Sta.Proc.InvMarked'' dst, Const false)"

lemma symNI_Nak_ref : 
             " 
                  symParamRule N NI_Nak_ref"
                 

"[|dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Nak_ref dst)"
                 
 
             unfolding NI_Nak_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Nak_refs :: "nat \<Rightarrow> rule set" where
 "NI_Nak_refs N \<equiv> oneParamCons N NI_Nak_ref"

lemma NI_Nak_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Nak N) j i) (NI_Nak i) = NI_Nak_ref i"
                 unfolding lemmasFor_NI_Nak_def  NI_Nak_def NI_Nak_ref_def  apply(auto      )    
 
done

lemma abs_NI_Nak_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (NI_Nak_ref i) = NI_Nak_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (NI_Nak_ref i) = skipRule"
                 
 
             unfolding NI_Nak_ref_def NI_Nak_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Nak_Home :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Nak_Home N = []"

definition NI_Nak_Home_ref :: "rule" where
 "NI_Nak_Home_ref \<equiv> 
   IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Nak
  \<triangleright>
   assign (Ident ''Sta.HomeUniMsg.Cmd'', Const UNI_None) ||
   assign (Ident ''Sta.HomeUniMsg.HomeProc'', Const false) ||
   assign (Ident ''Sta.HomeProc.ProcCmd'', Const NODE_None) ||
   assign (Ident ''Sta.HomeProc.InvMarked'', Const false)"

lemma symNI_Nak_Home_ref : 
             " 
                  symProtRules' N {NI_Nak_Home_ref}"
                 

" 
                  wellFormedRule (env N) N (NI_Nak_Home_ref)"
                 
 
             unfolding NI_Nak_Home_ref_def  apply(auto      )    
 
done

definition NI_Nak_Home_refs :: "rule set" where
 "NI_Nak_Home_refs \<equiv> {NI_Nak_Home_ref}"

lemma NI_Nak_Home_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Nak_Home N) j i) (NI_Nak_Home) = NI_Nak_Home_ref"
                 unfolding lemmasFor_NI_Nak_Home_def  NI_Nak_Home_def NI_Nak_Home_ref_def  apply(auto      )    
 
done

lemma abs_NI_Nak_Home : 
             "[|M <= N|] 
                 ==> absTransfRule (env N) M (NI_Nak_Home_ref) = NI_Nak_Home_ref"
                 
 
             unfolding NI_Nak_Home_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Nak_Clear :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Nak_Clear N = []"

definition NI_Nak_Clear_ref :: "rule" where
 "NI_Nak_Clear_ref \<equiv> 
   IVar (Ident ''Sta.NakcMsg.Cmd'') =\<^sub>f Const NAKC_Nakc
  \<triangleright>
   assign (Ident ''Sta.NakcMsg.Cmd'', Const NAKC_None) ||
   assign (Ident ''Sta.Dir.Pending'', Const false)"

lemma symNI_Nak_Clear_ref : 
             " 
                  symProtRules' N {NI_Nak_Clear_ref}"
                 

" 
                  wellFormedRule (env N) N (NI_Nak_Clear_ref)"
                 
 
             unfolding NI_Nak_Clear_ref_def  apply(auto      )    
 
done

definition NI_Nak_Clear_refs :: "rule set" where
 "NI_Nak_Clear_refs \<equiv> {NI_Nak_Clear_ref}"

lemma NI_Nak_Clear_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Nak_Clear N) j i) (NI_Nak_Clear) = NI_Nak_Clear_ref"
                 unfolding lemmasFor_NI_Nak_Clear_def  NI_Nak_Clear_def NI_Nak_Clear_ref_def  apply(auto      )    
 
done

lemma abs_NI_Nak_Clear : 
             "[|M <= N|] 
                 ==> absTransfRule (env N) M (NI_Nak_Clear_ref) = NI_Nak_Clear_ref"
                 
 
             unfolding NI_Nak_Clear_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Local_Get_Nak :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Local_Get_Nak N = []"

definition NI_Local_Get_Nak_ref :: "nat \<Rightarrow> rule" where
 "NI_Local_Get_Nak_ref src \<equiv> 
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_Get \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.RpMsg.Cmd'' src) =\<^sub>f Const RP_Replace \<and>\<^sub>f
   (IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<or>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E \<or>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.HeadPtr'') =\<^sub>f Const (index src))
  \<triangleright>
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_Nak) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const true)"

lemma symNI_Local_Get_Nak_ref : 
             " 
                  symParamRule N NI_Local_Get_Nak_ref"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_Local_Get_Nak_ref src)"
                 
 
             unfolding NI_Local_Get_Nak_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Local_Get_Nak_refs :: "nat \<Rightarrow> rule set" where
 "NI_Local_Get_Nak_refs N \<equiv> oneParamCons N NI_Local_Get_Nak_ref"

lemma NI_Local_Get_Nak_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Local_Get_Nak N) j i) (NI_Local_Get_Nak i) = NI_Local_Get_Nak_ref i"
                 unfolding lemmasFor_NI_Local_Get_Nak_def  NI_Local_Get_Nak_def NI_Local_Get_Nak_ref_def  apply(auto      )    
 
done

lemma abs_NI_Local_Get_Nak_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (NI_Local_Get_Nak_ref i) = NI_Local_Get_Nak_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (NI_Local_Get_Nak_ref i) = skipRule"
                 
 
             unfolding NI_Local_Get_Nak_ref_def NI_Local_Get_Nak_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Local_Get_Get :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Local_Get_Get N = []"

definition NI_Local_Get_Get_ref :: "nat \<Rightarrow> rule" where
 "NI_Local_Get_Get_ref src \<equiv> 
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_Get \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.RpMsg.Cmd'' src) =\<^sub>f Const RP_Replace \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.Dir.HeadPtr'') =\<^sub>f Const (index src)
  \<triangleright>
   assign (Ident ''Sta.Dir.Pending'', Const true) ||
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_Get) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const false) ||
   assign (Para ''Sta.UniMsg.Proc'' src, IVar (Ident ''Sta.Dir.HeadPtr'')) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_Get) ||
   assign (Ident ''Sta.HomePendReqSrc'', Const false) ||
   assign (Ident ''Sta.PendReqSrc'', Const (index src)) ||
   assign (Ident ''Sta.Collecting'', Const false)"

lemma symNI_Local_Get_Get_ref : 
             " 
                  symParamRule N NI_Local_Get_Get_ref"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_Local_Get_Get_ref src)"
                 
 
             unfolding NI_Local_Get_Get_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Local_Get_Get_refs :: "nat \<Rightarrow> rule set" where
 "NI_Local_Get_Get_refs N \<equiv> oneParamCons N NI_Local_Get_Get_ref"

lemma NI_Local_Get_Get_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Local_Get_Get N) j i) (NI_Local_Get_Get i) = NI_Local_Get_Get_ref i"
                 unfolding lemmasFor_NI_Local_Get_Get_def  NI_Local_Get_Get_def NI_Local_Get_Get_ref_def  apply(auto      )    
 
done

lemma abs_NI_Local_Get_Get_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (NI_Local_Get_Get_ref i) = NI_Local_Get_Get_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (NI_Local_Get_Get_ref i) = ABS_NI_Local_Get_Get M"
                 
 
             unfolding NI_Local_Get_Get_ref_def NI_Local_Get_Get_ref_def ABS_NI_Local_Get_Get_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Local_Get_Put :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Local_Get_Put N = []"

definition NI_Local_Get_Put_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "NI_Local_Get_Put_ref N src \<equiv> 
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_Get \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.RpMsg.Cmd'' src) =\<^sub>f Const RP_Replace \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   (IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<longrightarrow>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E)
  \<triangleright>
   (IF IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true DO
     assign (Ident ''Sta.Dir.Dirty'', Const false) ||
     assign (Ident ''Sta.Dir.HeadVld'', Const true) ||
     assign (Ident ''Sta.Dir.HeadPtr'', Const (index src)) ||
     assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_S) ||
     assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_Put) ||
     assign (Para ''Sta.UniMsg.HomeProc'' src, Const true)
   ELSE
     (IF IVar (Ident ''Sta.Dir.HeadVld'') =\<^sub>f Const true DO
       assign (Ident ''Sta.Dir.ShrVld'', Const true) ||
       assign (Para ''Sta.Dir.ShrSet'' src, Const true) ||
       assign (Para ''Sta.Dir.InvSet'' src, Const true) ||
       forallStmExcl (\<lambda>p. assign (Para ''Sta.Dir.InvSet'' p, IVar (Para ''Sta.Dir.ShrSet'' p))) src N
     ELSE
       assign (Ident ''Sta.Dir.HeadVld'', Const true) ||
       assign (Ident ''Sta.Dir.HeadPtr'', Const (index src))
     FI) ||
     assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_Put) ||
     assign (Para ''Sta.UniMsg.HomeProc'' src, Const true)
   FI)"

lemma symNI_Local_Get_Put_ref : 
             " 
                  symParamRule N (NI_Local_Get_Put_ref N)"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_Local_Get_Put_ref N src)"
                 
 
             unfolding NI_Local_Get_Put_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Local_Get_Put_refs :: "nat \<Rightarrow> rule set" where
 "NI_Local_Get_Put_refs N \<equiv> oneParamCons N (NI_Local_Get_Put_ref N)"

lemma NI_Local_Get_Put_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Local_Get_Put N) j i) (NI_Local_Get_Put N i) = NI_Local_Get_Put_ref N i"
                 unfolding lemmasFor_NI_Local_Get_Put_def  NI_Local_Get_Put_def NI_Local_Get_Put_ref_def  apply(auto      )    
 
done

lemma abs_NI_Local_Get_Put_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (NI_Local_Get_Put_ref N i) = NI_Local_Get_Put_ref M i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (NI_Local_Get_Put_ref N i) = ABS_NI_Local_Get_Put M"
                 
 
             unfolding NI_Local_Get_Put_ref_def NI_Local_Get_Put_ref_def ABS_NI_Local_Get_Put_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Remote_Get_Nak :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Remote_Get_Nak N = [Lemma_2a N]"

definition NI_Remote_Get_Nak_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "NI_Remote_Get_Nak_ref src dst \<equiv> 
   \<not>\<^sub>f Const (index src) =\<^sub>f Const (index dst) \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_Get \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const false \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Proc'' src) =\<^sub>f Const (index dst) \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' dst) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index src) \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_Get
  \<triangleright>
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_Nak) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const false) ||
   assign (Para ''Sta.UniMsg.Proc'' src, Const (index dst)) ||
   assign (Ident ''Sta.NakcMsg.Cmd'', Const NAKC_Nakc) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

lemma symNI_Remote_Get_Nak_ref : 
             " 
                  symParamRule2' N NI_Remote_Get_Nak_ref"
                 

"[|src <= N;dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Remote_Get_Nak_ref src dst)"
                 
 
             unfolding NI_Remote_Get_Nak_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamForm2And symParamForm2Forall1 symParamForm2Forall2 symParamFormForallExcl2 symParamForm2Imply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Remote_Get_Nak_refs :: "nat \<Rightarrow> rule set" where
 "NI_Remote_Get_Nak_refs N \<equiv> twoParamsCons N NI_Remote_Get_Nak_ref"

lemma NI_Remote_Get_Nak_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Remote_Get_Nak N) i j) (NI_Remote_Get_Nak i j) = NI_Remote_Get_Nak_ref i j"
                 unfolding lemmasFor_NI_Remote_Get_Nak_def Lemma_2a_def NI_Remote_Get_Nak_def NI_Remote_Get_Nak_ref_def  apply(auto      )    
 
done

lemma abs_NI_Remote_Get_Nak_ref : 
             "[|M <= N;src <= M;dst <= M|] 
                 ==> absTransfRule (env N) M (NI_Remote_Get_Nak_ref src dst) = NI_Remote_Get_Nak_ref src dst"
                 

"[|M <= N;src > M;dst <= M|] 
                 ==> absTransfRule (env N) M (NI_Remote_Get_Nak_ref src dst) = ABS_NI_Remote_Get_Nak_src M dst"
                 

"[|M <= N;src <= M;dst > M|] 
                 ==> absTransfRule (env N) M (NI_Remote_Get_Nak_ref src dst) = ABS_NI_Remote_Get_Nak_dst M src"
                 

"[|M <= N;src > M;dst > M|] 
                 ==> absTransfRule (env N) M (NI_Remote_Get_Nak_ref src dst) = ABS_NI_Remote_Get_Nak_src_dst M"
                 
 
             unfolding NI_Remote_Get_Nak_ref_def NI_Remote_Get_Nak_ref_def ABS_NI_Remote_Get_Nak_src_def ABS_NI_Remote_Get_Nak_dst_def ABS_NI_Remote_Get_Nak_src_dst_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Remote_Get_Nak_Home :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Remote_Get_Nak_Home N = [Lemma_2b N]"

definition NI_Remote_Get_Nak_Home_ref :: "nat \<Rightarrow> rule" where
 "NI_Remote_Get_Nak_Home_ref dst \<equiv> 
   IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Get \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.HomeProc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.Proc'') =\<^sub>f Const (index dst) \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_Get
  \<triangleright>
   assign (Ident ''Sta.HomeUniMsg.Cmd'', Const UNI_Nak) ||
   assign (Ident ''Sta.HomeUniMsg.HomeProc'', Const false) ||
   assign (Ident ''Sta.HomeUniMsg.Proc'', Const (index dst)) ||
   assign (Ident ''Sta.NakcMsg.Cmd'', Const NAKC_Nakc) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

lemma symNI_Remote_Get_Nak_Home_ref : 
             " 
                  symParamRule N NI_Remote_Get_Nak_Home_ref"
                 

"[|dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Remote_Get_Nak_Home_ref dst)"
                 
 
             unfolding NI_Remote_Get_Nak_Home_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Remote_Get_Nak_Home_refs :: "nat \<Rightarrow> rule set" where
 "NI_Remote_Get_Nak_Home_refs N \<equiv> oneParamCons N NI_Remote_Get_Nak_Home_ref"

lemma NI_Remote_Get_Nak_Home_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Remote_Get_Nak_Home N) j i) (NI_Remote_Get_Nak_Home i) = NI_Remote_Get_Nak_Home_ref i"
                 unfolding lemmasFor_NI_Remote_Get_Nak_Home_def Lemma_2b_def NI_Remote_Get_Nak_Home_def NI_Remote_Get_Nak_Home_ref_def  apply(auto      )    
 
done

lemma abs_NI_Remote_Get_Nak_Home_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (NI_Remote_Get_Nak_Home_ref i) = NI_Remote_Get_Nak_Home_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (NI_Remote_Get_Nak_Home_ref i) = ABS_NI_Remote_Get_Nak_Home M"
                 
 
             unfolding NI_Remote_Get_Nak_Home_ref_def NI_Remote_Get_Nak_Home_ref_def ABS_NI_Remote_Get_Nak_Home_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Remote_Get_Put :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Remote_Get_Put N = [Lemma_2a N, Lemma_1 N]"

definition NI_Remote_Get_Put_ref :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rule" where
 "NI_Remote_Get_Put_ref N src dst \<equiv> 
   \<not>\<^sub>f Const (index src) =\<^sub>f Const (index dst) \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_Get \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const false \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Proc'' src) =\<^sub>f Const (index dst) \<and>\<^sub>f
   IVar (Para ''Sta.Proc.CacheState'' dst) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   forallFormExcl (\<lambda>p. IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.WbMsg.Cmd'') =\<^sub>f Const WB_Wb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_ShWb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' p) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Put \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.UniMsg.Cmd'' p) =\<^sub>f Const UNI_PutX \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_PutX) dst N \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index src) \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_Get
  \<triangleright>
   assign (Para ''Sta.Proc.CacheState'' dst, Const CACHE_S) ||
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_Put) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const false) ||
   assign (Para ''Sta.UniMsg.Proc'' src, Const (index dst)) ||
   assign (Ident ''Sta.ShWbMsg.Cmd'', Const SHWB_ShWb) ||
   assign (Ident ''Sta.ShWbMsg.Proc'', Const (index src)) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

lemma symNI_Remote_Get_Put_ref : 
             " 
                  symParamRule2' N (NI_Remote_Get_Put_ref N)"
                 

"[|src <= N;dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Remote_Get_Put_ref N src dst)"
                 
 
             unfolding NI_Remote_Get_Put_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamForm2And symParamForm2Forall1 symParamForm2Forall2 symParamFormForallExcl2 symParamForm2Imply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Remote_Get_Put_refs :: "nat \<Rightarrow> rule set" where
 "NI_Remote_Get_Put_refs N \<equiv> twoParamsCons N (NI_Remote_Get_Put_ref N)"

lemma NI_Remote_Get_Put_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Remote_Get_Put N) i j) (NI_Remote_Get_Put i j) = NI_Remote_Get_Put_ref N i j"
                 unfolding lemmasFor_NI_Remote_Get_Put_def Lemma_2a_def Lemma_1_def NI_Remote_Get_Put_def NI_Remote_Get_Put_ref_def  apply(auto      )    
 
done

lemma abs_NI_Remote_Get_Put_ref : 
             "[|M <= N;src <= M;dst <= M|] 
                 ==> absTransfRule (env N) M (NI_Remote_Get_Put_ref N src dst) = NI_Remote_Get_Put_ref M src dst"
                 

"[|M <= N;src > M;dst <= M|] 
                 ==> absTransfRule (env N) M (NI_Remote_Get_Put_ref N src dst) = ABS_NI_Remote_Get_Put_src M dst"
                 

"[|M <= N;src <= M;dst > M|] 
                 ==> absTransfRule (env N) M (NI_Remote_Get_Put_ref N src dst) = ABS_NI_Remote_Get_Put_dst M src"
                 

"[|M <= N;src > M;dst > M|] 
                 ==> absTransfRule (env N) M (NI_Remote_Get_Put_ref N src dst) = ABS_NI_Remote_Get_Put_src_dst M"
                 
 
             unfolding NI_Remote_Get_Put_ref_def NI_Remote_Get_Put_ref_def ABS_NI_Remote_Get_Put_src_def ABS_NI_Remote_Get_Put_dst_def ABS_NI_Remote_Get_Put_src_dst_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Remote_Get_Put_Home :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Remote_Get_Put_Home N = [Lemma_2b N, Lemma_1 N]"

definition NI_Remote_Get_Put_Home_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "NI_Remote_Get_Put_Home_ref N dst \<equiv> 
   IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Get \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.HomeProc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.Proc'') =\<^sub>f Const (index dst) \<and>\<^sub>f
   IVar (Para ''Sta.Proc.CacheState'' dst) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   forallFormExcl (\<lambda>p. IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.WbMsg.Cmd'') =\<^sub>f Const WB_Wb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_ShWb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' p) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Put \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.UniMsg.Cmd'' p) =\<^sub>f Const UNI_PutX \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_PutX) dst N \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_Get
  \<triangleright>
   assign (Para ''Sta.Proc.CacheState'' dst, Const CACHE_S) ||
   assign (Ident ''Sta.HomeUniMsg.Cmd'', Const UNI_Put) ||
   assign (Ident ''Sta.HomeUniMsg.HomeProc'', Const false) ||
   assign (Ident ''Sta.HomeUniMsg.Proc'', Const (index dst)) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

lemma symNI_Remote_Get_Put_Home_ref : 
             " 
                  symParamRule N (NI_Remote_Get_Put_Home_ref N)"
                 

"[|dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Remote_Get_Put_Home_ref N dst)"
                 
 
             unfolding NI_Remote_Get_Put_Home_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Remote_Get_Put_Home_refs :: "nat \<Rightarrow> rule set" where
 "NI_Remote_Get_Put_Home_refs N \<equiv> oneParamCons N (NI_Remote_Get_Put_Home_ref N)"

lemma NI_Remote_Get_Put_Home_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Remote_Get_Put_Home N) j i) (NI_Remote_Get_Put_Home i) = NI_Remote_Get_Put_Home_ref N i"
                 unfolding lemmasFor_NI_Remote_Get_Put_Home_def Lemma_2b_def Lemma_1_def NI_Remote_Get_Put_Home_def NI_Remote_Get_Put_Home_ref_def  apply(auto      )    
 
done

lemma abs_NI_Remote_Get_Put_Home_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (NI_Remote_Get_Put_Home_ref N i) = NI_Remote_Get_Put_Home_ref M i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (NI_Remote_Get_Put_Home_ref N i) = ABS_NI_Remote_Get_Put_Home M"
                 
 
             unfolding NI_Remote_Get_Put_Home_ref_def NI_Remote_Get_Put_Home_ref_def ABS_NI_Remote_Get_Put_Home_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Local_GetX_Nak :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Local_GetX_Nak N = []"

definition NI_Local_GetX_Nak_ref :: "nat \<Rightarrow> rule" where
 "NI_Local_GetX_Nak_ref src \<equiv> 
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_GetX \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const true \<and>\<^sub>f
   (IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<or>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E \<or>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.HeadPtr'') =\<^sub>f Const (index src))
  \<triangleright>
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_Nak) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const true)"

lemma symNI_Local_GetX_Nak_ref : 
             " 
                  symParamRule N NI_Local_GetX_Nak_ref"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_Local_GetX_Nak_ref src)"
                 
 
             unfolding NI_Local_GetX_Nak_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Local_GetX_Nak_refs :: "nat \<Rightarrow> rule set" where
 "NI_Local_GetX_Nak_refs N \<equiv> oneParamCons N NI_Local_GetX_Nak_ref"

lemma NI_Local_GetX_Nak_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Local_GetX_Nak N) j i) (NI_Local_GetX_Nak i) = NI_Local_GetX_Nak_ref i"
                 unfolding lemmasFor_NI_Local_GetX_Nak_def  NI_Local_GetX_Nak_def NI_Local_GetX_Nak_ref_def  apply(auto      )    
 
done

lemma abs_NI_Local_GetX_Nak_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (NI_Local_GetX_Nak_ref i) = NI_Local_GetX_Nak_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (NI_Local_GetX_Nak_ref i) = skipRule"
                 
 
             unfolding NI_Local_GetX_Nak_ref_def NI_Local_GetX_Nak_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Local_GetX_GetX :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Local_GetX_GetX N = []"

definition NI_Local_GetX_GetX_ref :: "nat \<Rightarrow> rule" where
 "NI_Local_GetX_GetX_ref src \<equiv> 
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_GetX \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.Dir.HeadPtr'') =\<^sub>f Const (index src)
  \<triangleright>
   assign (Ident ''Sta.Dir.Pending'', Const true) ||
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_GetX) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const false) ||
   assign (Para ''Sta.UniMsg.Proc'' src, IVar (Ident ''Sta.Dir.HeadPtr'')) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_GetX) ||
   assign (Ident ''Sta.HomePendReqSrc'', Const false) ||
   assign (Ident ''Sta.PendReqSrc'', Const (index src)) ||
   assign (Ident ''Sta.Collecting'', Const false)"

lemma symNI_Local_GetX_GetX_ref : 
             " 
                  symParamRule N NI_Local_GetX_GetX_ref"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_Local_GetX_GetX_ref src)"
                 
 
             unfolding NI_Local_GetX_GetX_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Local_GetX_GetX_refs :: "nat \<Rightarrow> rule set" where
 "NI_Local_GetX_GetX_refs N \<equiv> oneParamCons N NI_Local_GetX_GetX_ref"

lemma NI_Local_GetX_GetX_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Local_GetX_GetX N) j i) (NI_Local_GetX_GetX i) = NI_Local_GetX_GetX_ref i"
                 unfolding lemmasFor_NI_Local_GetX_GetX_def  NI_Local_GetX_GetX_def NI_Local_GetX_GetX_ref_def  apply(auto      )    
 
done

lemma abs_NI_Local_GetX_GetX_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (NI_Local_GetX_GetX_ref i) = NI_Local_GetX_GetX_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (NI_Local_GetX_GetX_ref i) = ABS_NI_Local_GetX_GetX M"
                 
 
             unfolding NI_Local_GetX_GetX_ref_def NI_Local_GetX_GetX_ref_def ABS_NI_Local_GetX_GetX_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Local_GetX_PutX1 :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Local_GetX_PutX1 N = []"

definition NI_Local_GetX_PutX1_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "NI_Local_GetX_PutX1_ref N src \<equiv> 
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_GetX \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   (IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<longrightarrow>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E) \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true
  \<triangleright>
   assign (Ident ''Sta.Dir.Local'', Const false) ||
   assign (Ident ''Sta.Dir.Dirty'', Const true) ||
   assign (Ident ''Sta.Dir.HeadVld'', Const true) ||
   assign (Ident ''Sta.Dir.HeadPtr'', Const (index src)) ||
   assign (Ident ''Sta.Dir.ShrVld'', Const false) ||
   forallStm (\<lambda>p. assign (Para ''Sta.Dir.ShrSet'' p, Const false) ||
   assign (Para ''Sta.Dir.InvSet'' p, Const false)) N ||
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_PutX) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const true) ||
   assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_I)"

lemma symNI_Local_GetX_PutX1_ref : 
             " 
                  symParamRule N (NI_Local_GetX_PutX1_ref N)"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_Local_GetX_PutX1_ref N src)"
                 
 
             unfolding NI_Local_GetX_PutX1_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Local_GetX_PutX1_refs :: "nat \<Rightarrow> rule set" where
 "NI_Local_GetX_PutX1_refs N \<equiv> oneParamCons N (NI_Local_GetX_PutX1_ref N)"

lemma NI_Local_GetX_PutX1_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Local_GetX_PutX1 N) j i) (NI_Local_GetX_PutX1 N i) = NI_Local_GetX_PutX1_ref N i"
                 unfolding lemmasFor_NI_Local_GetX_PutX1_def  NI_Local_GetX_PutX1_def NI_Local_GetX_PutX1_ref_def  apply(auto      )    
 
done

lemma abs_NI_Local_GetX_PutX1_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (NI_Local_GetX_PutX1_ref N i) = NI_Local_GetX_PutX1_ref M i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (NI_Local_GetX_PutX1_ref N i) = ABS_NI_Local_GetX_PutX1 M"
                 
 
             unfolding NI_Local_GetX_PutX1_ref_def NI_Local_GetX_PutX1_ref_def ABS_NI_Local_GetX_PutX1_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Local_GetX_PutX2 :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Local_GetX_PutX2 N = []"

definition NI_Local_GetX_PutX2_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "NI_Local_GetX_PutX2_ref N src \<equiv> 
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_GetX \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   (IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<longrightarrow>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E) \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const false \<and>\<^sub>f
   (IVar (Ident ''Sta.Dir.HeadVld'') =\<^sub>f Const true \<longrightarrow>\<^sub>f
   IVar (Ident ''Sta.Dir.HeadPtr'') =\<^sub>f Const (index src) \<and>\<^sub>f
   forallFormExcl (\<lambda>p. IVar (Para ''Sta.Dir.ShrSet'' p) =\<^sub>f Const false) src N)
  \<triangleright>
   assign (Ident ''Sta.Dir.Dirty'', Const true) ||
   assign (Ident ''Sta.Dir.HeadVld'', Const true) ||
   assign (Ident ''Sta.Dir.HeadPtr'', Const (index src)) ||
   assign (Ident ''Sta.Dir.ShrVld'', Const false) ||
   forallStm (\<lambda>p. assign (Para ''Sta.Dir.ShrSet'' p, Const false) ||
   assign (Para ''Sta.Dir.InvSet'' p, Const false)) N ||
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_PutX) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const true) ||
   assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_I) ||
   (IF IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true DO
     assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_I) ||
     (IF IVar (Ident ''Sta.HomeProc.ProcCmd'') =\<^sub>f Const NODE_Get DO
       assign (Ident ''Sta.HomeProc.InvMarked'', Const true)
     ELSE
       skip
     FI)
   ELSE
     skip
   FI) ||
   assign (Ident ''Sta.Dir.Local'', Const false)"

lemma symNI_Local_GetX_PutX2_ref : 
             " 
                  symParamRule N (NI_Local_GetX_PutX2_ref N)"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_Local_GetX_PutX2_ref N src)"
                 
 
             unfolding NI_Local_GetX_PutX2_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Local_GetX_PutX2_refs :: "nat \<Rightarrow> rule set" where
 "NI_Local_GetX_PutX2_refs N \<equiv> oneParamCons N (NI_Local_GetX_PutX2_ref N)"

lemma NI_Local_GetX_PutX2_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Local_GetX_PutX2 N) j i) (NI_Local_GetX_PutX2 N i) = NI_Local_GetX_PutX2_ref N i"
                 unfolding lemmasFor_NI_Local_GetX_PutX2_def  NI_Local_GetX_PutX2_def NI_Local_GetX_PutX2_ref_def  apply(auto      )    
 
done

lemma abs_NI_Local_GetX_PutX2_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (NI_Local_GetX_PutX2_ref N i) = NI_Local_GetX_PutX2_ref M i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (NI_Local_GetX_PutX2_ref N i) = ABS_NI_Local_GetX_PutX2 M"
                 
 
             unfolding NI_Local_GetX_PutX2_ref_def NI_Local_GetX_PutX2_ref_def ABS_NI_Local_GetX_PutX2_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Local_GetX_PutX3 :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Local_GetX_PutX3 N = []"

definition NI_Local_GetX_PutX3_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "NI_Local_GetX_PutX3_ref N src \<equiv> 
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_GetX \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const false \<and>\<^sub>f
   (IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<longrightarrow>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E) \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const false
  \<triangleright>
   assign (Ident ''Sta.Dir.Pending'', Const true) ||
   assign (Ident ''Sta.Dir.Dirty'', Const true) ||
   assign (Para ''Sta.Dir.InvSet'' src, Const false) ||
   assign (Para ''Sta.InvMsg.Cmd'' src, Const INV_None) ||
   assign (Para ''Sta.Dir.ShrSet'' src, Const false) ||
   forallStmExcl (\<lambda>p. assign (Para ''Sta.Dir.InvSet'' p, iteForm (IVar (Ident ''Sta.Dir.ShrVld'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Para ''Sta.Dir.ShrSet'' p) =\<^sub>f Const true \<or>\<^sub>f
   IVar (Ident ''Sta.Dir.HeadVld'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.HeadPtr'') =\<^sub>f Const (index p)) (Const true) (Const false)) ||
   assign (Para ''Sta.InvMsg.Cmd'' p, iteForm (IVar (Ident ''Sta.Dir.ShrVld'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Para ''Sta.Dir.ShrSet'' p) =\<^sub>f Const true \<or>\<^sub>f
   IVar (Ident ''Sta.Dir.HeadVld'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.HeadPtr'') =\<^sub>f Const (index p)) (Const INV_Inv) (Const INV_None)) ||
   assign (Para ''Sta.Dir.ShrSet'' p, Const false)) src N ||
   assign (Ident ''Sta.Dir.HeadVld'', Const true) ||
   assign (Ident ''Sta.Dir.HeadPtr'', Const (index src)) ||
   assign (Ident ''Sta.Dir.ShrVld'', Const false) ||
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_PutX) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const true) ||
   (IF IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true DO
     assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_I) ||
     (IF IVar (Ident ''Sta.HomeProc.ProcCmd'') =\<^sub>f Const NODE_Get DO
       assign (Ident ''Sta.HomeProc.InvMarked'', Const true)
     ELSE
       skip
     FI)
   ELSE
     skip
   FI) ||
   assign (Ident ''Sta.Dir.Local'', Const false) ||
   assign (Ident ''Sta.HomePendReqSrc'', Const false) ||
   assign (Ident ''Sta.PendReqSrc'', Const (index src)) ||
   assign (Ident ''Sta.Collecting'', Const true)"

lemma symNI_Local_GetX_PutX3_ref : 
             " 
                  symParamRule N (NI_Local_GetX_PutX3_ref N)"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_Local_GetX_PutX3_ref N src)"
                 
 
             unfolding NI_Local_GetX_PutX3_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Local_GetX_PutX3_refs :: "nat \<Rightarrow> rule set" where
 "NI_Local_GetX_PutX3_refs N \<equiv> oneParamCons N (NI_Local_GetX_PutX3_ref N)"

lemma NI_Local_GetX_PutX3_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Local_GetX_PutX3 N) j i) (NI_Local_GetX_PutX3 N i) = NI_Local_GetX_PutX3_ref N i"
                 unfolding lemmasFor_NI_Local_GetX_PutX3_def  NI_Local_GetX_PutX3_def NI_Local_GetX_PutX3_ref_def  apply(auto      )    
 
done

lemma abs_NI_Local_GetX_PutX3_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (NI_Local_GetX_PutX3_ref N i) = NI_Local_GetX_PutX3_ref M i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (NI_Local_GetX_PutX3_ref N i) = ABS_NI_Local_GetX_PutX3 M"
                 
 
             unfolding NI_Local_GetX_PutX3_ref_def NI_Local_GetX_PutX3_ref_def ABS_NI_Local_GetX_PutX3_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Remote_GetX_Nak :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Remote_GetX_Nak N = [Lemma_3a N]"

definition NI_Remote_GetX_Nak_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "NI_Remote_GetX_Nak_ref src dst \<equiv> 
   \<not>\<^sub>f Const (index src) =\<^sub>f Const (index dst) \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_GetX \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const false \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Proc'' src) =\<^sub>f Const (index dst) \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' dst) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index src) \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_GetX
  \<triangleright>
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_Nak) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const false) ||
   assign (Para ''Sta.UniMsg.Proc'' src, Const (index dst)) ||
   assign (Ident ''Sta.NakcMsg.Cmd'', Const NAKC_Nakc) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

lemma symNI_Remote_GetX_Nak_ref : 
             " 
                  symParamRule2' N NI_Remote_GetX_Nak_ref"
                 

"[|src <= N;dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Remote_GetX_Nak_ref src dst)"
                 
 
             unfolding NI_Remote_GetX_Nak_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamForm2And symParamForm2Forall1 symParamForm2Forall2 symParamFormForallExcl2 symParamForm2Imply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Remote_GetX_Nak_refs :: "nat \<Rightarrow> rule set" where
 "NI_Remote_GetX_Nak_refs N \<equiv> twoParamsCons N NI_Remote_GetX_Nak_ref"

lemma NI_Remote_GetX_Nak_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Remote_GetX_Nak N) i j) (NI_Remote_GetX_Nak i j) = NI_Remote_GetX_Nak_ref i j"
                 unfolding lemmasFor_NI_Remote_GetX_Nak_def Lemma_3a_def NI_Remote_GetX_Nak_def NI_Remote_GetX_Nak_ref_def  apply(auto      )    
 
done

lemma abs_NI_Remote_GetX_Nak_ref : 
             "[|M <= N;src <= M;dst <= M|] 
                 ==> absTransfRule (env N) M (NI_Remote_GetX_Nak_ref src dst) = NI_Remote_GetX_Nak_ref src dst"
                 

"[|M <= N;src > M;dst <= M|] 
                 ==> absTransfRule (env N) M (NI_Remote_GetX_Nak_ref src dst) = ABS_NI_Remote_GetX_Nak_src M dst"
                 

"[|M <= N;src <= M;dst > M|] 
                 ==> absTransfRule (env N) M (NI_Remote_GetX_Nak_ref src dst) = ABS_NI_Remote_GetX_Nak_dst M src"
                 

"[|M <= N;src > M;dst > M|] 
                 ==> absTransfRule (env N) M (NI_Remote_GetX_Nak_ref src dst) = ABS_NI_Remote_GetX_Nak_src_dst M"
                 
 
             unfolding NI_Remote_GetX_Nak_ref_def NI_Remote_GetX_Nak_ref_def ABS_NI_Remote_GetX_Nak_src_def ABS_NI_Remote_GetX_Nak_dst_def ABS_NI_Remote_GetX_Nak_src_dst_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Remote_GetX_Nak_Home :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Remote_GetX_Nak_Home N = [Lemma_3b N]"

definition NI_Remote_GetX_Nak_Home_ref :: "nat \<Rightarrow> rule" where
 "NI_Remote_GetX_Nak_Home_ref dst \<equiv> 
   IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_GetX \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.HomeProc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.Proc'') =\<^sub>f Const (index dst) \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' dst) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_GetX
  \<triangleright>
   assign (Ident ''Sta.HomeUniMsg.Cmd'', Const UNI_Nak) ||
   assign (Ident ''Sta.HomeUniMsg.HomeProc'', Const false) ||
   assign (Ident ''Sta.HomeUniMsg.Proc'', Const (index dst)) ||
   assign (Ident ''Sta.NakcMsg.Cmd'', Const NAKC_Nakc) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

lemma symNI_Remote_GetX_Nak_Home_ref : 
             " 
                  symParamRule N NI_Remote_GetX_Nak_Home_ref"
                 

"[|dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Remote_GetX_Nak_Home_ref dst)"
                 
 
             unfolding NI_Remote_GetX_Nak_Home_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Remote_GetX_Nak_Home_refs :: "nat \<Rightarrow> rule set" where
 "NI_Remote_GetX_Nak_Home_refs N \<equiv> oneParamCons N NI_Remote_GetX_Nak_Home_ref"

lemma NI_Remote_GetX_Nak_Home_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Remote_GetX_Nak_Home N) j i) (NI_Remote_GetX_Nak_Home i) = NI_Remote_GetX_Nak_Home_ref i"
                 unfolding lemmasFor_NI_Remote_GetX_Nak_Home_def Lemma_3b_def NI_Remote_GetX_Nak_Home_def NI_Remote_GetX_Nak_Home_ref_def  apply(auto      )    
 
done

lemma abs_NI_Remote_GetX_Nak_Home_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (NI_Remote_GetX_Nak_Home_ref i) = NI_Remote_GetX_Nak_Home_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (NI_Remote_GetX_Nak_Home_ref i) = ABS_NI_Remote_GetX_Nak_Home M"
                 
 
             unfolding NI_Remote_GetX_Nak_Home_ref_def NI_Remote_GetX_Nak_Home_ref_def ABS_NI_Remote_GetX_Nak_Home_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Remote_GetX_PutX :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Remote_GetX_PutX N = [Lemma_3a N, Lemma_1 N]"

definition NI_Remote_GetX_PutX_ref :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rule" where
 "NI_Remote_GetX_PutX_ref N src dst \<equiv> 
   \<not>\<^sub>f Const (index src) =\<^sub>f Const (index dst) \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_GetX \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const false \<and>\<^sub>f
   IVar (Para ''Sta.UniMsg.Proc'' src) =\<^sub>f Const (index dst) \<and>\<^sub>f
   IVar (Para ''Sta.Proc.CacheState'' dst) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   forallFormExcl (\<lambda>p. IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.WbMsg.Cmd'') =\<^sub>f Const WB_Wb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_ShWb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' p) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Put \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.UniMsg.Cmd'' p) =\<^sub>f Const UNI_PutX \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_PutX) dst N \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index src) \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_GetX
  \<triangleright>
   assign (Para ''Sta.Proc.CacheState'' dst, Const CACHE_I) ||
   assign (Para ''Sta.UniMsg.Cmd'' src, Const UNI_PutX) ||
   assign (Para ''Sta.UniMsg.HomeProc'' src, Const false) ||
   assign (Para ''Sta.UniMsg.Proc'' src, Const (index dst)) ||
   assign (Ident ''Sta.ShWbMsg.Cmd'', Const SHWB_FAck) ||
   assign (Ident ''Sta.ShWbMsg.Proc'', Const (index src)) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

lemma symNI_Remote_GetX_PutX_ref : 
             " 
                  symParamRule2' N (NI_Remote_GetX_PutX_ref N)"
                 

"[|src <= N;dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Remote_GetX_PutX_ref N src dst)"
                 
 
             unfolding NI_Remote_GetX_PutX_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamForm2And symParamForm2Forall1 symParamForm2Forall2 symParamFormForallExcl2 symParamForm2Imply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Remote_GetX_PutX_refs :: "nat \<Rightarrow> rule set" where
 "NI_Remote_GetX_PutX_refs N \<equiv> twoParamsCons N (NI_Remote_GetX_PutX_ref N)"

lemma NI_Remote_GetX_PutX_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Remote_GetX_PutX N) i j) (NI_Remote_GetX_PutX i j) = NI_Remote_GetX_PutX_ref N i j"
                 unfolding lemmasFor_NI_Remote_GetX_PutX_def Lemma_3a_def Lemma_1_def NI_Remote_GetX_PutX_def NI_Remote_GetX_PutX_ref_def  apply(auto      )    
 
done

lemma abs_NI_Remote_GetX_PutX_ref : 
             "[|M <= N;src <= M;dst <= M|] 
                 ==> absTransfRule (env N) M (NI_Remote_GetX_PutX_ref N src dst) = NI_Remote_GetX_PutX_ref M src dst"
                 

"[|M <= N;src > M;dst <= M|] 
                 ==> absTransfRule (env N) M (NI_Remote_GetX_PutX_ref N src dst) = ABS_NI_Remote_GetX_PutX_src M dst"
                 

"[|M <= N;src <= M;dst > M|] 
                 ==> absTransfRule (env N) M (NI_Remote_GetX_PutX_ref N src dst) = ABS_NI_Remote_GetX_PutX_dst M src"
                 

"[|M <= N;src > M;dst > M|] 
                 ==> absTransfRule (env N) M (NI_Remote_GetX_PutX_ref N src dst) = ABS_NI_Remote_GetX_PutX_src_dst M"
                 
 
             unfolding NI_Remote_GetX_PutX_ref_def NI_Remote_GetX_PutX_ref_def ABS_NI_Remote_GetX_PutX_src_def ABS_NI_Remote_GetX_PutX_dst_def ABS_NI_Remote_GetX_PutX_src_dst_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Remote_GetX_PutX_Home :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Remote_GetX_PutX_Home N = [Lemma_3b N, Lemma_1 N]"

definition NI_Remote_GetX_PutX_Home_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "NI_Remote_GetX_PutX_Home_ref N dst \<equiv> 
   IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_GetX \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.HomeProc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomeUniMsg.Proc'') =\<^sub>f Const (index dst) \<and>\<^sub>f
   IVar (Para ''Sta.Proc.CacheState'' dst) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   forallFormExcl (\<lambda>p. IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.WbMsg.Cmd'') =\<^sub>f Const WB_Wb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_ShWb \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' p) =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Put \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Sta.UniMsg.Cmd'' p) =\<^sub>f Const UNI_PutX \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_PutX) dst N \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_GetX
  \<triangleright>
   assign (Para ''Sta.Proc.CacheState'' dst, Const CACHE_I) ||
   assign (Ident ''Sta.HomeUniMsg.Cmd'', Const UNI_PutX) ||
   assign (Ident ''Sta.HomeUniMsg.HomeProc'', Const false) ||
   assign (Ident ''Sta.HomeUniMsg.Proc'', Const (index dst)) ||
   assign (Ident ''Sta.FwdCmd'', Const UNI_None)"

lemma symNI_Remote_GetX_PutX_Home_ref : 
             " 
                  symParamRule N (NI_Remote_GetX_PutX_Home_ref N)"
                 

"[|dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Remote_GetX_PutX_Home_ref N dst)"
                 
 
             unfolding NI_Remote_GetX_PutX_Home_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Remote_GetX_PutX_Home_refs :: "nat \<Rightarrow> rule set" where
 "NI_Remote_GetX_PutX_Home_refs N \<equiv> oneParamCons N (NI_Remote_GetX_PutX_Home_ref N)"

lemma NI_Remote_GetX_PutX_Home_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Remote_GetX_PutX_Home N) j i) (NI_Remote_GetX_PutX_Home i) = NI_Remote_GetX_PutX_Home_ref N i"
                 unfolding lemmasFor_NI_Remote_GetX_PutX_Home_def Lemma_3b_def Lemma_1_def NI_Remote_GetX_PutX_Home_def NI_Remote_GetX_PutX_Home_ref_def  apply(auto      )    
 
done

lemma abs_NI_Remote_GetX_PutX_Home_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (NI_Remote_GetX_PutX_Home_ref N i) = NI_Remote_GetX_PutX_Home_ref M i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (NI_Remote_GetX_PutX_Home_ref N i) = ABS_NI_Remote_GetX_PutX_Home M"
                 
 
             unfolding NI_Remote_GetX_PutX_Home_ref_def NI_Remote_GetX_PutX_Home_ref_def ABS_NI_Remote_GetX_PutX_Home_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Local_Put :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Local_Put N = []"

definition NI_Local_Put_ref :: "rule" where
 "NI_Local_Put_ref \<equiv> 
   IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Put
  \<triangleright>
   assign (Ident ''Sta.HomeUniMsg.Cmd'', Const UNI_None) ||
   assign (Ident ''Sta.Dir.Pending'', Const false) ||
   assign (Ident ''Sta.Dir.Dirty'', Const false) ||
   assign (Ident ''Sta.Dir.Local'', Const true) ||
   assign (Ident ''Sta.HomeProc.ProcCmd'', Const NODE_None) ||
   (IF IVar (Ident ''Sta.HomeProc.InvMarked'') =\<^sub>f Const true DO
     assign (Ident ''Sta.HomeProc.InvMarked'', Const false) ||
     assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_I)
   ELSE
     assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_S)
   FI)"

lemma symNI_Local_Put_ref : 
             " 
                  symProtRules' N {NI_Local_Put_ref}"
                 

" 
                  wellFormedRule (env N) N (NI_Local_Put_ref)"
                 
 
             unfolding NI_Local_Put_ref_def  apply(auto      )    
 
done

definition NI_Local_Put_refs :: "rule set" where
 "NI_Local_Put_refs \<equiv> {NI_Local_Put_ref}"

lemma NI_Local_Put_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Local_Put N) j i) (NI_Local_Put) = NI_Local_Put_ref"
                 unfolding lemmasFor_NI_Local_Put_def  NI_Local_Put_def NI_Local_Put_ref_def  apply(auto      )    
 
done

lemma abs_NI_Local_Put : 
             "[|M <= N|] 
                 ==> absTransfRule (env N) M (NI_Local_Put_ref) = NI_Local_Put_ref"
                 
 
             unfolding NI_Local_Put_ref_def ABS_NI_Remote_GetX_PutX_Home_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Remote_Put :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Remote_Put N = []"

definition NI_Remote_Put_ref :: "nat \<Rightarrow> rule" where
 "NI_Remote_Put_ref dst \<equiv> 
   IVar (Para ''Sta.UniMsg.Cmd'' dst) =\<^sub>f Const UNI_Put
  \<triangleright>
   assign (Para ''Sta.UniMsg.Cmd'' dst, Const UNI_None) ||
   assign (Para ''Sta.UniMsg.HomeProc'' dst, Const false) ||
   assign (Para ''Sta.Proc.ProcCmd'' dst, Const NODE_None) ||
   assign (Para ''Sta.Proc.CacheState'' dst, iteForm (IVar (Para ''Sta.Proc.InvMarked'' dst) =\<^sub>f Const true) (Const CACHE_I) (Const CACHE_S)) ||
   assign (Para ''Sta.Proc.InvMarked'' dst, Const false)"

lemma symNI_Remote_Put_ref : 
             " 
                  symParamRule N NI_Remote_Put_ref"
                 

"[|dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Remote_Put_ref dst)"
                 
 
             unfolding NI_Remote_Put_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Remote_Put_refs :: "nat \<Rightarrow> rule set" where
 "NI_Remote_Put_refs N \<equiv> oneParamCons N NI_Remote_Put_ref"

lemma NI_Remote_Put_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Remote_Put N) j i) (NI_Remote_Put i) = NI_Remote_Put_ref i"
                 unfolding lemmasFor_NI_Remote_Put_def  NI_Remote_Put_def NI_Remote_Put_ref_def  apply(auto      )    
 
done

lemma abs_NI_Remote_Put_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (NI_Remote_Put_ref i) = NI_Remote_Put_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (NI_Remote_Put_ref i) = skipRule"
                 
 
             unfolding NI_Remote_Put_ref_def NI_Remote_Put_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Local_PutXAcksDone :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Local_PutXAcksDone N = []"

definition NI_Local_PutXAcksDone_ref :: "rule" where
 "NI_Local_PutXAcksDone_ref \<equiv> 
   IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_PutX
  \<triangleright>
   assign (Ident ''Sta.HomeUniMsg.Cmd'', Const UNI_None) ||
   assign (Ident ''Sta.Dir.Pending'', Const false) ||
   assign (Ident ''Sta.Dir.Local'', Const true) ||
   assign (Ident ''Sta.Dir.HeadVld'', Const false) ||
   assign (Ident ''Sta.HomeProc.ProcCmd'', Const NODE_None) ||
   assign (Ident ''Sta.HomeProc.InvMarked'', Const false) ||
   assign (Ident ''Sta.HomeProc.CacheState'', Const CACHE_E)"

lemma symNI_Local_PutXAcksDone_ref : 
             " 
                  symProtRules' N {NI_Local_PutXAcksDone_ref}"
                 

" 
                  wellFormedRule (env N) N (NI_Local_PutXAcksDone_ref)"
                 
 
             unfolding NI_Local_PutXAcksDone_ref_def  apply(auto      )    
 
done

definition NI_Local_PutXAcksDone_refs :: "rule set" where
 "NI_Local_PutXAcksDone_refs \<equiv> {NI_Local_PutXAcksDone_ref}"

lemma NI_Local_PutXAcksDone_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Local_PutXAcksDone N) j i) (NI_Local_PutXAcksDone) = NI_Local_PutXAcksDone_ref"
                 unfolding lemmasFor_NI_Local_PutXAcksDone_def  NI_Local_PutXAcksDone_def NI_Local_PutXAcksDone_ref_def  apply(auto      )    
 
done

lemma abs_NI_Local_PutXAcksDone : 
             "[|M <= N|] 
                 ==> absTransfRule (env N) M (NI_Local_PutXAcksDone_ref) = NI_Local_PutXAcksDone_ref"
                 
 
             unfolding NI_Local_PutXAcksDone_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Remote_PutX :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Remote_PutX N = []"

definition NI_Remote_PutX_ref :: "nat \<Rightarrow> rule" where
 "NI_Remote_PutX_ref dst \<equiv> 
   IVar (Para ''Sta.UniMsg.Cmd'' dst) =\<^sub>f Const UNI_PutX \<and>\<^sub>f
   IVar (Para ''Sta.Proc.ProcCmd'' dst) =\<^sub>f Const NODE_GetX
  \<triangleright>
   assign (Para ''Sta.UniMsg.Cmd'' dst, Const UNI_None) ||
   assign (Para ''Sta.UniMsg.HomeProc'' dst, Const false) ||
   assign (Para ''Sta.Proc.ProcCmd'' dst, Const NODE_None) ||
   assign (Para ''Sta.Proc.InvMarked'' dst, Const false) ||
   assign (Para ''Sta.Proc.CacheState'' dst, Const CACHE_E)"

lemma symNI_Remote_PutX_ref : 
             " 
                  symParamRule N NI_Remote_PutX_ref"
                 

"[|dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Remote_PutX_ref dst)"
                 
 
             unfolding NI_Remote_PutX_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Remote_PutX_refs :: "nat \<Rightarrow> rule set" where
 "NI_Remote_PutX_refs N \<equiv> oneParamCons N NI_Remote_PutX_ref"

lemma NI_Remote_PutX_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Remote_PutX N) j i) (NI_Remote_PutX i) = NI_Remote_PutX_ref i"
                 unfolding lemmasFor_NI_Remote_PutX_def  NI_Remote_PutX_def NI_Remote_PutX_ref_def  apply(auto      )    
 
done

lemma abs_NI_Remote_PutX_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (NI_Remote_PutX_ref i) = NI_Remote_PutX_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (NI_Remote_PutX_ref i) = skipRule"
                 
 
             unfolding NI_Remote_PutX_ref_def NI_Remote_PutX_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Inv :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Inv N = []"

definition NI_Inv_ref :: "nat \<Rightarrow> rule" where
 "NI_Inv_ref dst \<equiv> 
   IVar (Para ''Sta.InvMsg.Cmd'' dst) =\<^sub>f Const INV_Inv
  \<triangleright>
   assign (Para ''Sta.InvMsg.Cmd'' dst, Const INV_InvAck) ||
   assign (Para ''Sta.Proc.CacheState'' dst, Const CACHE_I) ||
   assign (Para ''Sta.Proc.InvMarked'' dst, iteForm (IVar (Para ''Sta.Proc.ProcCmd'' dst) =\<^sub>f Const NODE_Get) (Const true) (IVar (Para ''Sta.Proc.InvMarked'' dst)))"

lemma symNI_Inv_ref : 
             " 
                  symParamRule N NI_Inv_ref"
                 

"[|dst <= N|] 
                 ==> wellFormedRule (env N) N (NI_Inv_ref dst)"
                 
 
             unfolding NI_Inv_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Inv_refs :: "nat \<Rightarrow> rule set" where
 "NI_Inv_refs N \<equiv> oneParamCons N NI_Inv_ref"

lemma NI_Inv_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Inv N) j i) (NI_Inv i) = NI_Inv_ref i"
                 unfolding lemmasFor_NI_Inv_def  NI_Inv_def NI_Inv_ref_def  apply(auto      )    
 
done

lemma abs_NI_Inv_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (NI_Inv_ref i) = NI_Inv_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (NI_Inv_ref i) = skipRule"
                 
 
             unfolding NI_Inv_ref_def NI_Inv_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_InvAck1 :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_InvAck1 N = [Lemma_4 N]"

definition NI_InvAck1_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "NI_InvAck1_ref N src \<equiv> 
   IVar (Para ''Sta.InvMsg.Cmd'' src) =\<^sub>f Const INV_InvAck \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Para ''Sta.Dir.InvSet'' src) =\<^sub>f Const true \<and>\<^sub>f
   forallFormExcl (\<lambda>p. IVar (Para ''Sta.Dir.InvSet'' p) =\<^sub>f Const false) src N \<and>\<^sub>f
   forallFormExcl (\<lambda>q. IVar (Ident ''Sta.Collecting'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.NakcMsg.Cmd'') =\<^sub>f Const NAKC_None \<and>\<^sub>f
   IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_None \<and>\<^sub>f
   (IVar (Para ''Sta.UniMsg.Cmd'' q) =\<^sub>f Const UNI_Get \<or>\<^sub>f
   IVar (Para ''Sta.UniMsg.Cmd'' q) =\<^sub>f Const UNI_GetX \<longrightarrow>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' q) =\<^sub>f Const true) \<and>\<^sub>f
   (IVar (Para ''Sta.UniMsg.Cmd'' q) =\<^sub>f Const UNI_PutX \<longrightarrow>\<^sub>f
   IVar (Para ''Sta.UniMsg.HomeProc'' q) =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
   IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index q))) src N
  \<triangleright>
   assign (Para ''Sta.InvMsg.Cmd'' src, Const INV_None) ||
   assign (Para ''Sta.Dir.InvSet'' src, Const false) ||
   assign (Ident ''Sta.Dir.Pending'', Const false) ||
   (IF IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const false DO
     assign (Ident ''Sta.Dir.Local'', Const false)
   ELSE
     skip
   FI) ||
   assign (Ident ''Sta.Collecting'', Const false)"

lemma symNI_InvAck1_ref : 
             " 
                  symParamRule N (NI_InvAck1_ref N)"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_InvAck1_ref N src)"
                 
 
             unfolding NI_InvAck1_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_InvAck1_refs :: "nat \<Rightarrow> rule set" where
 "NI_InvAck1_refs N \<equiv> oneParamCons N (NI_InvAck1_ref N)"

lemma NI_InvAck1_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_InvAck1 N) j i) (NI_InvAck1 N i) = NI_InvAck1_ref N i"
                 unfolding lemmasFor_NI_InvAck1_def Lemma_4_def NI_InvAck1_def NI_InvAck1_ref_def  apply(auto      )    
 
done

lemma abs_NI_InvAck1_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (NI_InvAck1_ref N i) = NI_InvAck1_ref M i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (NI_InvAck1_ref N i) = ABS_NI_InvAck1 M"
                 
 
             unfolding NI_InvAck1_ref_def NI_InvAck1_ref_def ABS_NI_InvAck1_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_InvAck2 :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_InvAck2 N = []"

definition NI_InvAck2_ref :: "nat \<Rightarrow> rule" where
 "NI_InvAck2_ref src \<equiv> 
   IVar (Para ''Sta.InvMsg.Cmd'' src) =\<^sub>f Const INV_InvAck \<and>\<^sub>f
   IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
   IVar (Para ''Sta.Dir.InvSet'' src) =\<^sub>f Const true
  \<triangleright>
   assign (Para ''Sta.InvMsg.Cmd'' src, Const INV_None) ||
   assign (Para ''Sta.Dir.InvSet'' src, Const false)"

lemma symNI_InvAck2_ref : 
             " 
                  symParamRule N NI_InvAck2_ref"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_InvAck2_ref src)"
                 
 
             unfolding NI_InvAck2_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_InvAck2_refs :: "nat \<Rightarrow> rule set" where
 "NI_InvAck2_refs N \<equiv> oneParamCons N NI_InvAck2_ref"

lemma NI_InvAck2_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_InvAck2 N) j i) (NI_InvAck2 i) = NI_InvAck2_ref i"
                 unfolding lemmasFor_NI_InvAck2_def  NI_InvAck2_def NI_InvAck2_ref_def  apply(auto      )    
 
done

lemma abs_NI_InvAck2_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (NI_InvAck2_ref i) = NI_InvAck2_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (NI_InvAck2_ref i) = skipRule"
                 
 
             unfolding NI_InvAck2_ref_def NI_InvAck2_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Wb :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Wb N = []"

definition NI_Wb_ref :: "rule" where
 "NI_Wb_ref \<equiv> 
   IVar (Ident ''Sta.WbMsg.Cmd'') =\<^sub>f Const WB_Wb
  \<triangleright>
   assign (Ident ''Sta.WbMsg.Cmd'', Const WB_None) ||
   assign (Ident ''Sta.Dir.Dirty'', Const false) ||
   assign (Ident ''Sta.Dir.HeadVld'', Const false)"

lemma symNI_Wb_ref : 
             " 
                  symProtRules' N {NI_Wb_ref}"
                 

" 
                  wellFormedRule (env N) N (NI_Wb_ref)"
                 
 
             unfolding NI_Wb_ref_def  apply(auto      )    
 
done

definition NI_Wb_refs :: "rule set" where
 "NI_Wb_refs \<equiv> {NI_Wb_ref}"

lemma NI_Wb_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Wb N) j i) (NI_Wb) = NI_Wb_ref"
                 unfolding lemmasFor_NI_Wb_def  NI_Wb_def NI_Wb_ref_def  apply(auto      )    
 
done

lemma abs_NI_Wb : 
             "[|M <= N|] 
                 ==> absTransfRule (env N) M (NI_Wb_ref) = NI_Wb_ref"
                 
 
             unfolding NI_Wb_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_FAck :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_FAck N = []"

definition NI_FAck_ref :: "rule" where
 "NI_FAck_ref \<equiv> 
   IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_FAck
  \<triangleright>
   assign (Ident ''Sta.ShWbMsg.Cmd'', Const SHWB_None) ||
   assign (Ident ''Sta.Dir.Pending'', Const false) ||
   (IF IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true DO
     assign (Ident ''Sta.Dir.HeadPtr'', IVar (Ident ''Sta.ShWbMsg.Proc''))
   ELSE
     skip
   FI)"

lemma symNI_FAck_ref : 
             " 
                  symProtRules' N {NI_FAck_ref}"
                 

" 
                  wellFormedRule (env N) N (NI_FAck_ref)"
                 
 
             unfolding NI_FAck_ref_def  apply(auto      )    
 
done

definition NI_FAck_refs :: "rule set" where
 "NI_FAck_refs \<equiv> {NI_FAck_ref}"

lemma NI_FAck_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_FAck N) j i) (NI_FAck) = NI_FAck_ref"
                 unfolding lemmasFor_NI_FAck_def  NI_FAck_def NI_FAck_ref_def  apply(auto      )    
 
done

lemma abs_NI_FAck : 
             "[|M <= N|] 
                 ==> absTransfRule (env N) M (NI_FAck_ref) = NI_FAck_ref"
                 
 
             unfolding NI_FAck_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_ShWb :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_ShWb N = []"

definition NI_ShWb_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "NI_ShWb_ref N src \<equiv> 
   IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_ShWb \<and>\<^sub>f
   IVar (Ident ''Sta.ShWbMsg.Proc'') =\<^sub>f Const (index src)
  \<triangleright>
   assign (Ident ''Sta.ShWbMsg.Cmd'', Const SHWB_None) ||
   assign (Ident ''Sta.Dir.Pending'', Const false) ||
   assign (Ident ''Sta.Dir.Dirty'', Const false) ||
   assign (Ident ''Sta.Dir.ShrVld'', Const true) ||
   assign (Para ''Sta.Dir.ShrSet'' src, Const true) ||
   assign (Para ''Sta.Dir.InvSet'' src, Const true) ||
   forallStmExcl (\<lambda>p. assign (Para ''Sta.Dir.InvSet'' p, IVar (Para ''Sta.Dir.ShrSet'' p))) src N"

lemma symNI_ShWb_ref : 
             " 
                  symParamRule N (NI_ShWb_ref N)"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_ShWb_ref N src)"
                 
 
             unfolding NI_ShWb_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_ShWb_refs :: "nat \<Rightarrow> rule set" where
 "NI_ShWb_refs N \<equiv> oneParamCons N (NI_ShWb_ref N)"

lemma NI_ShWb_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_ShWb N) j i) (NI_ShWb N i) = NI_ShWb_ref N i"
                 unfolding lemmasFor_NI_ShWb_def  NI_ShWb_def NI_ShWb_ref_def  apply(auto      )    
 
done

lemma abs_NI_ShWb_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (NI_ShWb_ref N i) = NI_ShWb_ref M i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (NI_ShWb_ref N i) = ABS_NI_ShWb M"
                 
 
             unfolding NI_ShWb_ref_def NI_ShWb_ref_def ABS_NI_ShWb_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_NI_Replace :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Replace N = []"

definition NI_Replace_ref :: "nat \<Rightarrow> rule" where
 "NI_Replace_ref src \<equiv> 
   IVar (Para ''Sta.RpMsg.Cmd'' src) =\<^sub>f Const RP_Replace
  \<triangleright>
   assign (Para ''Sta.RpMsg.Cmd'' src, Const RP_None) ||
   (IF IVar (Ident ''Sta.Dir.ShrVld'') =\<^sub>f Const true DO
     assign (Para ''Sta.Dir.ShrSet'' src, Const false) ||
     assign (Para ''Sta.Dir.InvSet'' src, Const false)
   ELSE
     skip
   FI)"

lemma symNI_Replace_ref : 
             " 
                  symParamRule N NI_Replace_ref"
                 

"[|src <= N|] 
                 ==> wellFormedRule (env N) N (NI_Replace_ref src)"
                 
 
             unfolding NI_Replace_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition NI_Replace_refs :: "nat \<Rightarrow> rule set" where
 "NI_Replace_refs N \<equiv> oneParamCons N NI_Replace_ref"

lemma NI_Replace_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_NI_Replace N) j i) (NI_Replace i) = NI_Replace_ref i"
                 unfolding lemmasFor_NI_Replace_def  NI_Replace_def NI_Replace_ref_def  apply(auto      )    
 
done

lemma abs_NI_Replace_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (NI_Replace_ref i) = NI_Replace_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (NI_Replace_ref i) = skipRule"
                 
 
             unfolding NI_Replace_ref_def NI_Replace_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition InvS :: "nat \<Rightarrow> (((nat \<Rightarrow> nat \<Rightarrow> formula) list) list)" where
 "InvS N = [lemmasFor_PI_Remote_Get N, lemmasFor_PI_Local_Get_Get N, lemmasFor_PI_Local_Get_Put N, lemmasFor_PI_Remote_GetX N, lemmasFor_PI_Local_GetX_GetX N, lemmasFor_PI_Local_GetX_PutX N, lemmasFor_PI_Remote_PutX N, lemmasFor_PI_Local_PutX N, lemmasFor_PI_Remote_Replace N, lemmasFor_PI_Local_Replace N, lemmasFor_NI_Nak N, lemmasFor_NI_Nak_Home N, lemmasFor_NI_Nak_Clear N, lemmasFor_NI_Local_Get_Nak N, lemmasFor_NI_Local_Get_Get N, lemmasFor_NI_Local_Get_Put N, lemmasFor_NI_Remote_Get_Nak N, lemmasFor_NI_Remote_Get_Nak_Home N, lemmasFor_NI_Remote_Get_Put N, lemmasFor_NI_Remote_Get_Put_Home N, lemmasFor_NI_Local_GetX_Nak N, lemmasFor_NI_Local_GetX_GetX N, lemmasFor_NI_Local_GetX_PutX1 N, lemmasFor_NI_Local_GetX_PutX2 N, lemmasFor_NI_Local_GetX_PutX3 N, lemmasFor_NI_Remote_GetX_Nak N, lemmasFor_NI_Remote_GetX_Nak_Home N, lemmasFor_NI_Remote_GetX_PutX N, lemmasFor_NI_Remote_GetX_PutX_Home N, lemmasFor_NI_Local_Put N, lemmasFor_NI_Remote_Put N, lemmasFor_NI_Local_PutXAcksDone N, lemmasFor_NI_Remote_PutX N, lemmasFor_NI_Inv N, lemmasFor_NI_InvAck1 N, lemmasFor_NI_InvAck2 N, lemmasFor_NI_Wb N, lemmasFor_NI_FAck N, lemmasFor_NI_ShWb N, lemmasFor_NI_Replace N]"

definition rule_refs :: "nat \<Rightarrow> rule set" where
 "rule_refs N = (PI_Remote_Get_refs N \<union> (PI_Local_Get_Get_refs \<union> (PI_Local_Get_Put_refs \<union> (PI_Remote_GetX_refs N \<union> (PI_Local_GetX_GetX_refs \<union> (PI_Local_GetX_PutX_refs N \<union> (PI_Remote_PutX_refs N \<union> (PI_Local_PutX_refs \<union> (PI_Remote_Replace_refs N \<union> (PI_Local_Replace_refs \<union> (NI_Nak_refs N \<union> (NI_Nak_Home_refs \<union> (NI_Nak_Clear_refs \<union> (NI_Local_Get_Nak_refs N \<union> (NI_Local_Get_Get_refs N \<union> (NI_Local_Get_Put_refs N \<union> (NI_Remote_Get_Nak_refs N \<union> (NI_Remote_Get_Nak_Home_refs N \<union> (NI_Remote_Get_Put_refs N \<union> (NI_Remote_Get_Put_Home_refs N \<union> (NI_Local_GetX_Nak_refs N \<union> (NI_Local_GetX_GetX_refs N \<union> (NI_Local_GetX_PutX1_refs N \<union> (NI_Local_GetX_PutX2_refs N \<union> (NI_Local_GetX_PutX3_refs N \<union> (NI_Remote_GetX_Nak_refs N \<union> (NI_Remote_GetX_Nak_Home_refs N \<union> (NI_Remote_GetX_PutX_refs N \<union> (NI_Remote_GetX_PutX_Home_refs N \<union> (NI_Local_Put_refs \<union> (NI_Remote_Put_refs N \<union> (NI_Local_PutXAcksDone_refs \<union> (NI_Remote_PutX_refs N \<union> (NI_Inv_refs N \<union> (NI_InvAck1_refs N \<union> (NI_InvAck2_refs N \<union> (NI_Wb_refs \<union> (NI_FAck_refs \<union> (NI_ShWb_refs N \<union> NI_Replace_refs N)))))))))))))))))))))))))))))))))))))))"

lemma PI_Remote_GetStrengthRel : 
                  " 
                  strengthenRel (PI_Remote_Gets N) (set (InvS N)) (PI_Remote_Get_refs N) N"
                 unfolding PI_Remote_Gets_def PI_Remote_Get_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_PI_Remote_Get" in strengthenExt1)
 using PI_Remote_Get_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma PI_Local_Get_GetStrengthRel : 
                  " 
                  strengthenRel (PI_Local_Get_Gets) (set (InvS N)) (PI_Local_Get_Get_refs) N"
                 unfolding PI_Local_Get_Gets_def PI_Local_Get_Get_refs_def PI_Local_Get_Get_def PI_Local_Get_Get_ref_def using strengthenRefl apply(blast      )

done

lemma PI_Local_Get_PutStrengthRel : 
                  " 
                  strengthenRel (PI_Local_Get_Puts) (set (InvS N)) (PI_Local_Get_Put_refs) N"
                 unfolding PI_Local_Get_Puts_def PI_Local_Get_Put_refs_def PI_Local_Get_Put_def PI_Local_Get_Put_ref_def using strengthenRefl apply(blast      )

done

lemma PI_Remote_GetXStrengthRel : 
                  " 
                  strengthenRel (PI_Remote_GetXs N) (set (InvS N)) (PI_Remote_GetX_refs N) N"
                 unfolding PI_Remote_GetXs_def PI_Remote_GetX_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_PI_Remote_GetX" in strengthenExt1)
 using PI_Remote_GetX_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma PI_Local_GetX_GetXStrengthRel : 
                  " 
                  strengthenRel (PI_Local_GetX_GetXs) (set (InvS N)) (PI_Local_GetX_GetX_refs) N"
                 unfolding PI_Local_GetX_GetXs_def PI_Local_GetX_GetX_refs_def PI_Local_GetX_GetX_def PI_Local_GetX_GetX_ref_def using strengthenRefl apply(blast      )

done

lemma PI_Local_GetX_PutXStrengthRel : 
                  " 
                  strengthenRel (PI_Local_GetX_PutXs N) (set (InvS N)) (PI_Local_GetX_PutX_refs N) N"
                 unfolding PI_Local_GetX_PutXs_def PI_Local_GetX_PutX_refs_def PI_Local_GetX_PutX_def PI_Local_GetX_PutX_ref_def using strengthenRefl apply(blast      )

done

lemma PI_Remote_PutXStrengthRel : 
                  " 
                  strengthenRel (PI_Remote_PutXs N) (set (InvS N)) (PI_Remote_PutX_refs N) N"
                 unfolding PI_Remote_PutXs_def PI_Remote_PutX_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_PI_Remote_PutX" in strengthenExt1)
 using PI_Remote_PutX_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma PI_Local_PutXStrengthRel : 
                  " 
                  strengthenRel (PI_Local_PutXs) (set (InvS N)) (PI_Local_PutX_refs) N"
                 unfolding PI_Local_PutXs_def PI_Local_PutX_refs_def PI_Local_PutX_def PI_Local_PutX_ref_def using strengthenRefl apply(blast      )

done

lemma PI_Remote_ReplaceStrengthRel : 
                  " 
                  strengthenRel (PI_Remote_Replaces N) (set (InvS N)) (PI_Remote_Replace_refs N) N"
                 unfolding PI_Remote_Replaces_def PI_Remote_Replace_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_PI_Remote_Replace" in strengthenExt1)
 using PI_Remote_Replace_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma PI_Local_ReplaceStrengthRel : 
                  " 
                  strengthenRel (PI_Local_Replaces) (set (InvS N)) (PI_Local_Replace_refs) N"
                 unfolding PI_Local_Replaces_def PI_Local_Replace_refs_def PI_Local_Replace_def PI_Local_Replace_ref_def using strengthenRefl apply(blast      )

done

lemma NI_NakStrengthRel : 
                  " 
                  strengthenRel (NI_Naks N) (set (InvS N)) (NI_Nak_refs N) N"
                 unfolding NI_Naks_def NI_Nak_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_Nak" in strengthenExt1)
 using NI_Nak_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_Nak_HomeStrengthRel : 
                  " 
                  strengthenRel (NI_Nak_Homes) (set (InvS N)) (NI_Nak_Home_refs) N"
                 unfolding NI_Nak_Homes_def NI_Nak_Home_refs_def NI_Nak_Home_def NI_Nak_Home_ref_def using strengthenRefl apply(blast      )

done

lemma NI_Nak_ClearStrengthRel : 
                  " 
                  strengthenRel (NI_Nak_Clears) (set (InvS N)) (NI_Nak_Clear_refs) N"
                 unfolding NI_Nak_Clears_def NI_Nak_Clear_refs_def NI_Nak_Clear_def NI_Nak_Clear_ref_def using strengthenRefl apply(blast      )

done

lemma NI_Local_Get_NakStrengthRel : 
                  " 
                  strengthenRel (NI_Local_Get_Naks N) (set (InvS N)) (NI_Local_Get_Nak_refs N) N"
                 unfolding NI_Local_Get_Naks_def NI_Local_Get_Nak_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_Local_Get_Nak" in strengthenExt1)
 using NI_Local_Get_Nak_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_Local_Get_GetStrengthRel : 
                  " 
                  strengthenRel (NI_Local_Get_Gets N) (set (InvS N)) (NI_Local_Get_Get_refs N) N"
                 unfolding NI_Local_Get_Gets_def NI_Local_Get_Get_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_Local_Get_Get" in strengthenExt1)
 using NI_Local_Get_Get_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_Local_Get_PutStrengthRel : 
                  " 
                  strengthenRel (NI_Local_Get_Puts N) (set (InvS N)) (NI_Local_Get_Put_refs N) N"
                 unfolding NI_Local_Get_Puts_def NI_Local_Get_Put_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_Local_Get_Put" in strengthenExt1)
 using NI_Local_Get_Put_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_Remote_Get_NakStrengthRel : 
                  " 
                  strengthenRel (NI_Remote_Get_Naks N) (set (InvS N)) (NI_Remote_Get_Nak_refs N) N"
                 unfolding NI_Remote_Get_Naks_def NI_Remote_Get_Nak_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_Remote_Get_Nak" in strengthenExt2)
 using NI_Remote_Get_Nak_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_Remote_Get_Nak_HomeStrengthRel : 
                  " 
                  strengthenRel (NI_Remote_Get_Nak_Homes N) (set (InvS N)) (NI_Remote_Get_Nak_Home_refs N) N"
                 unfolding NI_Remote_Get_Nak_Homes_def NI_Remote_Get_Nak_Home_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_Remote_Get_Nak_Home" in strengthenExt1)
 using NI_Remote_Get_Nak_Home_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_Remote_Get_PutStrengthRel : 
                  " 
                  strengthenRel (NI_Remote_Get_Puts N) (set (InvS N)) (NI_Remote_Get_Put_refs N) N"
                 unfolding NI_Remote_Get_Puts_def NI_Remote_Get_Put_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_Remote_Get_Put" in strengthenExt2)
 using NI_Remote_Get_Put_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_Remote_Get_Put_HomeStrengthRel : 
                  " 
                  strengthenRel (NI_Remote_Get_Put_Homes N) (set (InvS N)) (NI_Remote_Get_Put_Home_refs N) N"
                 unfolding NI_Remote_Get_Put_Homes_def NI_Remote_Get_Put_Home_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_Remote_Get_Put_Home" in strengthenExt1)
 using NI_Remote_Get_Put_Home_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_Local_GetX_NakStrengthRel : 
                  " 
                  strengthenRel (NI_Local_GetX_Naks N) (set (InvS N)) (NI_Local_GetX_Nak_refs N) N"
                 unfolding NI_Local_GetX_Naks_def NI_Local_GetX_Nak_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_Local_GetX_Nak" in strengthenExt1)
 using NI_Local_GetX_Nak_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_Local_GetX_GetXStrengthRel : 
                  " 
                  strengthenRel (NI_Local_GetX_GetXs N) (set (InvS N)) (NI_Local_GetX_GetX_refs N) N"
                 unfolding NI_Local_GetX_GetXs_def NI_Local_GetX_GetX_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_Local_GetX_GetX" in strengthenExt1)
 using NI_Local_GetX_GetX_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_Local_GetX_PutX1StrengthRel : 
                  " 
                  strengthenRel (NI_Local_GetX_PutX1s N) (set (InvS N)) (NI_Local_GetX_PutX1_refs N) N"
                 unfolding NI_Local_GetX_PutX1s_def NI_Local_GetX_PutX1_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_Local_GetX_PutX1" in strengthenExt1)
 using NI_Local_GetX_PutX1_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_Local_GetX_PutX2StrengthRel : 
                  " 
                  strengthenRel (NI_Local_GetX_PutX2s N) (set (InvS N)) (NI_Local_GetX_PutX2_refs N) N"
                 unfolding NI_Local_GetX_PutX2s_def NI_Local_GetX_PutX2_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_Local_GetX_PutX2" in strengthenExt1)
 using NI_Local_GetX_PutX2_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_Local_GetX_PutX3StrengthRel : 
                  " 
                  strengthenRel (NI_Local_GetX_PutX3s N) (set (InvS N)) (NI_Local_GetX_PutX3_refs N) N"
                 unfolding NI_Local_GetX_PutX3s_def NI_Local_GetX_PutX3_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_Local_GetX_PutX3" in strengthenExt1)
 using NI_Local_GetX_PutX3_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_Remote_GetX_NakStrengthRel : 
                  " 
                  strengthenRel (NI_Remote_GetX_Naks N) (set (InvS N)) (NI_Remote_GetX_Nak_refs N) N"
                 unfolding NI_Remote_GetX_Naks_def NI_Remote_GetX_Nak_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_Remote_GetX_Nak" in strengthenExt2)
 using NI_Remote_GetX_Nak_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_Remote_GetX_Nak_HomeStrengthRel : 
                  " 
                  strengthenRel (NI_Remote_GetX_Nak_Homes N) (set (InvS N)) (NI_Remote_GetX_Nak_Home_refs N) N"
                 unfolding NI_Remote_GetX_Nak_Homes_def NI_Remote_GetX_Nak_Home_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_Remote_GetX_Nak_Home" in strengthenExt1)
 using NI_Remote_GetX_Nak_Home_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_Remote_GetX_PutXStrengthRel : 
                  " 
                  strengthenRel (NI_Remote_GetX_PutXs N) (set (InvS N)) (NI_Remote_GetX_PutX_refs N) N"
                 unfolding NI_Remote_GetX_PutXs_def NI_Remote_GetX_PutX_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_Remote_GetX_PutX" in strengthenExt2)
 using NI_Remote_GetX_PutX_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_Remote_GetX_PutX_HomeStrengthRel : 
                  " 
                  strengthenRel (NI_Remote_GetX_PutX_Homes N) (set (InvS N)) (NI_Remote_GetX_PutX_Home_refs N) N"
                 unfolding NI_Remote_GetX_PutX_Homes_def NI_Remote_GetX_PutX_Home_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_Remote_GetX_PutX_Home" in strengthenExt1)
 using NI_Remote_GetX_PutX_Home_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_Local_PutStrengthRel : 
                  " 
                  strengthenRel (NI_Local_Puts) (set (InvS N)) (NI_Local_Put_refs) N"
                 unfolding NI_Local_Puts_def NI_Local_Put_refs_def NI_Local_Put_def NI_Local_Put_ref_def using strengthenRefl apply(blast      )

done

lemma NI_Remote_PutStrengthRel : 
                  " 
                  strengthenRel (NI_Remote_Puts N) (set (InvS N)) (NI_Remote_Put_refs N) N"
                 unfolding NI_Remote_Puts_def NI_Remote_Put_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_Remote_Put" in strengthenExt1)
 using NI_Remote_Put_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_Local_PutXAcksDoneStrengthRel : 
                  " 
                  strengthenRel (NI_Local_PutXAcksDones) (set (InvS N)) (NI_Local_PutXAcksDone_refs) N"
                 unfolding NI_Local_PutXAcksDones_def NI_Local_PutXAcksDone_refs_def NI_Local_PutXAcksDone_def NI_Local_PutXAcksDone_ref_def using strengthenRefl apply(blast      )

done

lemma NI_Remote_PutXStrengthRel : 
                  " 
                  strengthenRel (NI_Remote_PutXs N) (set (InvS N)) (NI_Remote_PutX_refs N) N"
                 unfolding NI_Remote_PutXs_def NI_Remote_PutX_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_Remote_PutX" in strengthenExt1)
 using NI_Remote_PutX_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_InvStrengthRel : 
                  " 
                  strengthenRel (NI_Invs N) (set (InvS N)) (NI_Inv_refs N) N"
                 unfolding NI_Invs_def NI_Inv_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_Inv" in strengthenExt1)
 using NI_Inv_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_InvAck1StrengthRel : 
                  " 
                  strengthenRel (NI_InvAck1s N) (set (InvS N)) (NI_InvAck1_refs N) N"
                 unfolding NI_InvAck1s_def NI_InvAck1_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_InvAck1" in strengthenExt1)
 using NI_InvAck1_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_InvAck2StrengthRel : 
                  " 
                  strengthenRel (NI_InvAck2s N) (set (InvS N)) (NI_InvAck2_refs N) N"
                 unfolding NI_InvAck2s_def NI_InvAck2_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_InvAck2" in strengthenExt1)
 using NI_InvAck2_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_WbStrengthRel : 
                  " 
                  strengthenRel (NI_Wbs) (set (InvS N)) (NI_Wb_refs) N"
                 unfolding NI_Wbs_def NI_Wb_refs_def NI_Wb_def NI_Wb_ref_def using strengthenRefl apply(blast      )

done

lemma NI_FAckStrengthRel : 
                  " 
                  strengthenRel (NI_FAcks) (set (InvS N)) (NI_FAck_refs) N"
                 unfolding NI_FAcks_def NI_FAck_refs_def NI_FAck_def NI_FAck_ref_def using strengthenRefl apply(blast      )

done

lemma NI_ShWbStrengthRel : 
                  " 
                  strengthenRel (NI_ShWbs N) (set (InvS N)) (NI_ShWb_refs N) N"
                 unfolding NI_ShWbs_def NI_ShWb_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_ShWb" in strengthenExt1)
 using NI_ShWb_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma NI_ReplaceStrengthRel : 
                  " 
                  strengthenRel (NI_Replaces N) (set (InvS N)) (NI_Replace_refs N) N"
                 unfolding NI_Replaces_def NI_Replace_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_NI_Replace" in strengthenExt1)
 using NI_Replace_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma deriveAllRef : 
             "[|r : PI_Remote_Get_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : PI_Local_Get_Get_refs|] 
                 ==> deriveRule (env N) r"
                 

"[|r : PI_Local_Get_Put_refs|] 
                 ==> deriveRule (env N) r"
                 

"[|r : PI_Remote_GetX_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : PI_Local_GetX_GetX_refs|] 
                 ==> deriveRule (env N) r"
                 

"[|r : PI_Local_GetX_PutX_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : PI_Remote_PutX_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : PI_Local_PutX_refs|] 
                 ==> deriveRule (env N) r"
                 

"[|r : PI_Remote_Replace_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : PI_Local_Replace_refs|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Nak_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Nak_Home_refs|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Nak_Clear_refs|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Local_Get_Nak_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Local_Get_Get_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Local_Get_Put_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Remote_Get_Nak_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Remote_Get_Nak_Home_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Remote_Get_Put_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Remote_Get_Put_Home_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Local_GetX_Nak_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Local_GetX_GetX_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Local_GetX_PutX1_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Local_GetX_PutX2_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Local_GetX_PutX3_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Remote_GetX_Nak_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Remote_GetX_Nak_Home_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Remote_GetX_PutX_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Remote_GetX_PutX_Home_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Local_Put_refs|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Remote_Put_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Local_PutXAcksDone_refs|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Remote_PutX_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Inv_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_InvAck1_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_InvAck2_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Wb_refs|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_FAck_refs|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_ShWb_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : NI_Replace_refs N|] 
                 ==> deriveRule (env N) r"
                 
 
             unfolding deriveRule_def deriveForm_def deriveStmt_def PI_Remote_Get_refs_def PI_Remote_Get_ref_def PI_Local_Get_Get_refs_def PI_Local_Get_Get_ref_def PI_Local_Get_Put_refs_def PI_Local_Get_Put_ref_def PI_Remote_GetX_refs_def PI_Remote_GetX_ref_def PI_Local_GetX_GetX_refs_def PI_Local_GetX_GetX_ref_def PI_Local_GetX_PutX_refs_def PI_Local_GetX_PutX_ref_def PI_Remote_PutX_refs_def PI_Remote_PutX_ref_def PI_Local_PutX_refs_def PI_Local_PutX_ref_def PI_Remote_Replace_refs_def PI_Remote_Replace_ref_def PI_Local_Replace_refs_def PI_Local_Replace_ref_def NI_Nak_refs_def NI_Nak_ref_def NI_Nak_Home_refs_def NI_Nak_Home_ref_def NI_Nak_Clear_refs_def NI_Nak_Clear_ref_def NI_Local_Get_Nak_refs_def NI_Local_Get_Nak_ref_def NI_Local_Get_Get_refs_def NI_Local_Get_Get_ref_def NI_Local_Get_Put_refs_def NI_Local_Get_Put_ref_def NI_Remote_Get_Nak_refs_def NI_Remote_Get_Nak_ref_def NI_Remote_Get_Nak_Home_refs_def NI_Remote_Get_Nak_Home_ref_def NI_Remote_Get_Put_refs_def NI_Remote_Get_Put_ref_def NI_Remote_Get_Put_Home_refs_def NI_Remote_Get_Put_Home_ref_def NI_Local_GetX_Nak_refs_def NI_Local_GetX_Nak_ref_def NI_Local_GetX_GetX_refs_def NI_Local_GetX_GetX_ref_def NI_Local_GetX_PutX1_refs_def NI_Local_GetX_PutX1_ref_def NI_Local_GetX_PutX2_refs_def NI_Local_GetX_PutX2_ref_def NI_Local_GetX_PutX3_refs_def NI_Local_GetX_PutX3_ref_def NI_Remote_GetX_Nak_refs_def NI_Remote_GetX_Nak_ref_def NI_Remote_GetX_Nak_Home_refs_def NI_Remote_GetX_Nak_Home_ref_def NI_Remote_GetX_PutX_refs_def NI_Remote_GetX_PutX_ref_def NI_Remote_GetX_PutX_Home_refs_def NI_Remote_GetX_PutX_Home_ref_def NI_Local_Put_refs_def NI_Local_Put_ref_def NI_Remote_Put_refs_def NI_Remote_Put_ref_def NI_Local_PutXAcksDone_refs_def NI_Local_PutXAcksDone_ref_def NI_Remote_PutX_refs_def NI_Remote_PutX_ref_def NI_Inv_refs_def NI_Inv_ref_def NI_InvAck1_refs_def NI_InvAck1_ref_def NI_InvAck2_refs_def NI_InvAck2_ref_def NI_Wb_refs_def NI_Wb_ref_def NI_FAck_refs_def NI_FAck_ref_def NI_ShWb_refs_def NI_ShWb_ref_def NI_Replace_refs_def NI_Replace_ref_def  apply(auto      )    
 
done

lemma symProtAllRef : 
             " 
                  symProtRules' N (PI_Remote_Get_refs N)"
                 

" 
                  symProtRules' N (PI_Local_Get_Get_refs)"
                 

" 
                  symProtRules' N (PI_Local_Get_Put_refs)"
                 

" 
                  symProtRules' N (PI_Remote_GetX_refs N)"
                 

" 
                  symProtRules' N (PI_Local_GetX_GetX_refs)"
                 

" 
                  symProtRules' N (PI_Local_GetX_PutX_refs N)"
                 

" 
                  symProtRules' N (PI_Remote_PutX_refs N)"
                 

" 
                  symProtRules' N (PI_Local_PutX_refs)"
                 

" 
                  symProtRules' N (PI_Remote_Replace_refs N)"
                 

" 
                  symProtRules' N (PI_Local_Replace_refs)"
                 

" 
                  symProtRules' N (NI_Nak_refs N)"
                 

" 
                  symProtRules' N (NI_Nak_Home_refs)"
                 

" 
                  symProtRules' N (NI_Nak_Clear_refs)"
                 

" 
                  symProtRules' N (NI_Local_Get_Nak_refs N)"
                 

" 
                  symProtRules' N (NI_Local_Get_Get_refs N)"
                 

" 
                  symProtRules' N (NI_Local_Get_Put_refs N)"
                 

" 
                  symProtRules' N (NI_Remote_Get_Nak_refs N)"
                 

" 
                  symProtRules' N (NI_Remote_Get_Nak_Home_refs N)"
                 

" 
                  symProtRules' N (NI_Remote_Get_Put_refs N)"
                 

" 
                  symProtRules' N (NI_Remote_Get_Put_Home_refs N)"
                 

" 
                  symProtRules' N (NI_Local_GetX_Nak_refs N)"
                 

" 
                  symProtRules' N (NI_Local_GetX_GetX_refs N)"
                 

" 
                  symProtRules' N (NI_Local_GetX_PutX1_refs N)"
                 

" 
                  symProtRules' N (NI_Local_GetX_PutX2_refs N)"
                 

" 
                  symProtRules' N (NI_Local_GetX_PutX3_refs N)"
                 

" 
                  symProtRules' N (NI_Remote_GetX_Nak_refs N)"
                 

" 
                  symProtRules' N (NI_Remote_GetX_Nak_Home_refs N)"
                 

" 
                  symProtRules' N (NI_Remote_GetX_PutX_refs N)"
                 

" 
                  symProtRules' N (NI_Remote_GetX_PutX_Home_refs N)"
                 

" 
                  symProtRules' N (NI_Local_Put_refs)"
                 

" 
                  symProtRules' N (NI_Remote_Put_refs N)"
                 

" 
                  symProtRules' N (NI_Local_PutXAcksDone_refs)"
                 

" 
                  symProtRules' N (NI_Remote_PutX_refs N)"
                 

" 
                  symProtRules' N (NI_Inv_refs N)"
                 

" 
                  symProtRules' N (NI_InvAck1_refs N)"
                 

" 
                  symProtRules' N (NI_InvAck2_refs N)"
                 

" 
                  symProtRules' N (NI_Wb_refs)"
                 

" 
                  symProtRules' N (NI_FAck_refs)"
                 

" 
                  symProtRules' N (NI_ShWb_refs N)"
                 

" 
                  symProtRules' N (NI_Replace_refs N)"
                 
 
              using symPI_Remote_Get_ref(1) PI_Remote_Get_refs_def symPI_Local_Get_Get_ref(1) PI_Local_Get_Get_refs_def symPI_Local_Get_Put_ref(1) PI_Local_Get_Put_refs_def symPI_Remote_GetX_ref(1) PI_Remote_GetX_refs_def symPI_Local_GetX_GetX_ref(1) PI_Local_GetX_GetX_refs_def symPI_Local_GetX_PutX_ref(1) PI_Local_GetX_PutX_refs_def symPI_Remote_PutX_ref(1) PI_Remote_PutX_refs_def symPI_Local_PutX_ref(1) PI_Local_PutX_refs_def symPI_Remote_Replace_ref(1) PI_Remote_Replace_refs_def symPI_Local_Replace_ref(1) PI_Local_Replace_refs_def symNI_Nak_ref(1) NI_Nak_refs_def symNI_Nak_Home_ref(1) NI_Nak_Home_refs_def symNI_Nak_Clear_ref(1) NI_Nak_Clear_refs_def symNI_Local_Get_Nak_ref(1) NI_Local_Get_Nak_refs_def symNI_Local_Get_Get_ref(1) NI_Local_Get_Get_refs_def symNI_Local_Get_Put_ref(1) NI_Local_Get_Put_refs_def symNI_Remote_Get_Nak_ref(1) NI_Remote_Get_Nak_refs_def symNI_Remote_Get_Nak_Home_ref(1) NI_Remote_Get_Nak_Home_refs_def symNI_Remote_Get_Put_ref(1) NI_Remote_Get_Put_refs_def symNI_Remote_Get_Put_Home_ref(1) NI_Remote_Get_Put_Home_refs_def symNI_Local_GetX_Nak_ref(1) NI_Local_GetX_Nak_refs_def symNI_Local_GetX_GetX_ref(1) NI_Local_GetX_GetX_refs_def symNI_Local_GetX_PutX1_ref(1) NI_Local_GetX_PutX1_refs_def symNI_Local_GetX_PutX2_ref(1) NI_Local_GetX_PutX2_refs_def symNI_Local_GetX_PutX3_ref(1) NI_Local_GetX_PutX3_refs_def symNI_Remote_GetX_Nak_ref(1) NI_Remote_GetX_Nak_refs_def symNI_Remote_GetX_Nak_Home_ref(1) NI_Remote_GetX_Nak_Home_refs_def symNI_Remote_GetX_PutX_ref(1) NI_Remote_GetX_PutX_refs_def symNI_Remote_GetX_PutX_Home_ref(1) NI_Remote_GetX_PutX_Home_refs_def symNI_Local_Put_ref(1) NI_Local_Put_refs_def symNI_Remote_Put_ref(1) NI_Remote_Put_refs_def symNI_Local_PutXAcksDone_ref(1) NI_Local_PutXAcksDone_refs_def symNI_Remote_PutX_ref(1) NI_Remote_PutX_refs_def symNI_Inv_ref(1) NI_Inv_refs_def symNI_InvAck1_ref(1) NI_InvAck1_refs_def symNI_InvAck2_ref(1) NI_InvAck2_refs_def symNI_Wb_ref(1) NI_Wb_refs_def symNI_FAck_ref(1) NI_FAck_refs_def symNI_ShWb_ref(1) NI_ShWb_refs_def symNI_Replace_ref(1) NI_Replace_refs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )    
 
done

lemma StrengthRelRules2Rule_refs : 
                  " 
                  strengthenRel (rules N) (set (InvS N)) (rule_refs N) N"
                 unfolding rules_def rule_refs_def   apply(rule strenRelUnion)
  apply(blast intro: PI_Remote_GetStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: PI_Local_Get_GetStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: PI_Local_Get_PutStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: PI_Remote_GetXStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: PI_Local_GetX_GetXStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: PI_Local_GetX_PutXStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: PI_Remote_PutXStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: PI_Local_PutXStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: PI_Remote_ReplaceStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: PI_Local_ReplaceStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_NakStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_Nak_HomeStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_Nak_ClearStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_Local_Get_NakStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_Local_Get_GetStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_Local_Get_PutStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_Remote_Get_NakStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_Remote_Get_Nak_HomeStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_Remote_Get_PutStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_Remote_Get_Put_HomeStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_Local_GetX_NakStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_Local_GetX_GetXStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_Local_GetX_PutX1StrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_Local_GetX_PutX2StrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_Local_GetX_PutX3StrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_Remote_GetX_NakStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_Remote_GetX_Nak_HomeStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_Remote_GetX_PutXStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_Remote_GetX_PutX_HomeStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_Local_PutStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_Remote_PutStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_Local_PutXAcksDoneStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_Remote_PutXStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_InvStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_InvAck1StrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_InvAck2StrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_WbStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_FAckStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: NI_ShWbStrengthRel     )

  apply(blast intro: NI_ReplaceStrengthRel     )

done

lemma Abs_PI_Remote_Get_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` PI_Remote_Get_refs N) = (PI_Remote_Get_refs M Un {skipRule})"
                 unfolding PI_Remote_Get_refs_def   apply(rule absGen)
 using abs_PI_Remote_Get_ref apply(auto      )    
 
done

lemma Abs_PI_Local_Get_Gets : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` PI_Local_Get_Get_refs) = PI_Local_Get_Get_refs"
                 unfolding PI_Local_Get_Get_refs_def PI_Local_Get_Get_ref_def  apply(auto      )    
 
done

lemma Abs_PI_Local_Get_Puts : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` PI_Local_Get_Put_refs) = PI_Local_Get_Put_refs"
                 unfolding PI_Local_Get_Put_refs_def PI_Local_Get_Put_ref_def  apply(auto      )    
 
done

lemma Abs_PI_Remote_GetX_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` PI_Remote_GetX_refs N) = (PI_Remote_GetX_refs M Un {skipRule})"
                 unfolding PI_Remote_GetX_refs_def   apply(rule absGen)
 using abs_PI_Remote_GetX_ref apply(auto      )    
 
done

lemma Abs_PI_Local_GetX_GetXs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` PI_Local_GetX_GetX_refs) = PI_Local_GetX_GetX_refs"
                 unfolding PI_Local_GetX_GetX_refs_def PI_Local_GetX_GetX_ref_def  apply(auto      )    
 
done

lemma Abs_PI_Local_GetX_PutXs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` PI_Local_GetX_PutX_refs N) = PI_Local_GetX_PutX_refs M"
                 unfolding PI_Local_GetX_PutX_refs_def PI_Local_GetX_PutX_ref_def  apply(auto      )    
 
done

lemma Abs_PI_Remote_PutX_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` PI_Remote_PutX_refs N) = (PI_Remote_PutX_refs M Un ABS_PI_Remote_PutXs M)"
                 unfolding PI_Remote_PutX_refs_def ABS_PI_Remote_PutXs_def   apply(rule absGen)
 using abs_PI_Remote_PutX_ref apply(auto      )    
 
done

lemma Abs_PI_Local_PutXs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` PI_Local_PutX_refs) = PI_Local_PutX_refs"
                 unfolding PI_Local_PutX_refs_def PI_Local_PutX_ref_def  apply(auto      )    
 
done

lemma Abs_PI_Remote_Replace_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` PI_Remote_Replace_refs N) = (PI_Remote_Replace_refs M Un {skipRule})"
                 unfolding PI_Remote_Replace_refs_def   apply(rule absGen)
 using abs_PI_Remote_Replace_ref apply(auto      )    
 
done

lemma Abs_PI_Local_Replaces : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` PI_Local_Replace_refs) = PI_Local_Replace_refs"
                 unfolding PI_Local_Replace_refs_def PI_Local_Replace_ref_def  apply(auto      )    
 
done

lemma Abs_NI_Nak_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Nak_refs N) = (NI_Nak_refs M Un {skipRule})"
                 unfolding NI_Nak_refs_def   apply(rule absGen)
 using abs_NI_Nak_ref apply(auto      )    
 
done

lemma Abs_NI_Nak_Homes : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Nak_Home_refs) = NI_Nak_Home_refs"
                 unfolding NI_Nak_Home_refs_def NI_Nak_Home_ref_def  apply(auto      )    
 
done

lemma Abs_NI_Nak_Clears : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Nak_Clear_refs) = NI_Nak_Clear_refs"
                 unfolding NI_Nak_Clear_refs_def NI_Nak_Clear_ref_def  apply(auto      )    
 
done

lemma Abs_NI_Local_Get_Nak_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Local_Get_Nak_refs N) = (NI_Local_Get_Nak_refs M Un {skipRule})"
                 unfolding NI_Local_Get_Nak_refs_def   apply(rule absGen)
 using abs_NI_Local_Get_Nak_ref apply(auto      )    
 
done

lemma Abs_NI_Local_Get_Get_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Local_Get_Get_refs N) = (NI_Local_Get_Get_refs M Un ABS_NI_Local_Get_Gets M)"
                 unfolding NI_Local_Get_Get_refs_def ABS_NI_Local_Get_Gets_def   apply(rule absGen)
 using abs_NI_Local_Get_Get_ref apply(auto      )    
 
done

lemma Abs_NI_Local_Get_Put_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Local_Get_Put_refs N) = (NI_Local_Get_Put_refs M Un ABS_NI_Local_Get_Puts M)"
                 unfolding NI_Local_Get_Put_refs_def ABS_NI_Local_Get_Puts_def   apply(rule absGen)
 using abs_NI_Local_Get_Put_ref apply(auto      )    
 
done

lemma Abs_NI_Remote_Get_Nak_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Remote_Get_Nak_refs N) = (NI_Remote_Get_Nak_refs M Un ABS_NI_Remote_Get_Nak_dsts M Un ABS_NI_Remote_Get_Nak_srcs M Un ABS_NI_Remote_Get_Nak_src_dsts M)"
                 unfolding NI_Remote_Get_Nak_refs_def ABS_NI_Remote_Get_Nak_dsts_def ABS_NI_Remote_Get_Nak_srcs_def ABS_NI_Remote_Get_Nak_src_dsts_def   apply(rule absGen2)
 using abs_NI_Remote_Get_Nak_ref apply(auto      )    
 
done

lemma Abs_NI_Remote_Get_Nak_Home_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Remote_Get_Nak_Home_refs N) = (NI_Remote_Get_Nak_Home_refs M Un ABS_NI_Remote_Get_Nak_Homes M)"
                 unfolding NI_Remote_Get_Nak_Home_refs_def ABS_NI_Remote_Get_Nak_Homes_def   apply(rule absGen)
 using abs_NI_Remote_Get_Nak_Home_ref apply(auto      )    
 
done

lemma Abs_NI_Remote_Get_Put_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Remote_Get_Put_refs N) = (NI_Remote_Get_Put_refs M Un ABS_NI_Remote_Get_Put_dsts M Un ABS_NI_Remote_Get_Put_srcs M Un ABS_NI_Remote_Get_Put_src_dsts M)"
                 unfolding NI_Remote_Get_Put_refs_def ABS_NI_Remote_Get_Put_dsts_def ABS_NI_Remote_Get_Put_srcs_def ABS_NI_Remote_Get_Put_src_dsts_def   apply(rule absGen2)
 using abs_NI_Remote_Get_Put_ref apply(auto      )    
 
done

lemma Abs_NI_Remote_Get_Put_Home_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Remote_Get_Put_Home_refs N) = (NI_Remote_Get_Put_Home_refs M Un ABS_NI_Remote_Get_Put_Homes M)"
                 unfolding NI_Remote_Get_Put_Home_refs_def ABS_NI_Remote_Get_Put_Homes_def   apply(rule absGen)
 using abs_NI_Remote_Get_Put_Home_ref apply(auto      )    
 
done

lemma Abs_NI_Local_GetX_Nak_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Local_GetX_Nak_refs N) = (NI_Local_GetX_Nak_refs M Un {skipRule})"
                 unfolding NI_Local_GetX_Nak_refs_def   apply(rule absGen)
 using abs_NI_Local_GetX_Nak_ref apply(auto      )    
 
done

lemma Abs_NI_Local_GetX_GetX_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Local_GetX_GetX_refs N) = (NI_Local_GetX_GetX_refs M Un ABS_NI_Local_GetX_GetXs M)"
                 unfolding NI_Local_GetX_GetX_refs_def ABS_NI_Local_GetX_GetXs_def   apply(rule absGen)
 using abs_NI_Local_GetX_GetX_ref apply(auto      )    
 
done

lemma Abs_NI_Local_GetX_PutX1_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Local_GetX_PutX1_refs N) = (NI_Local_GetX_PutX1_refs M Un ABS_NI_Local_GetX_PutX1s M)"
                 unfolding NI_Local_GetX_PutX1_refs_def ABS_NI_Local_GetX_PutX1s_def   apply(rule absGen)
 using abs_NI_Local_GetX_PutX1_ref apply(auto      )    
 
done

lemma Abs_NI_Local_GetX_PutX2_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Local_GetX_PutX2_refs N) = (NI_Local_GetX_PutX2_refs M Un ABS_NI_Local_GetX_PutX2s M)"
                 unfolding NI_Local_GetX_PutX2_refs_def ABS_NI_Local_GetX_PutX2s_def   apply(rule absGen)
 using abs_NI_Local_GetX_PutX2_ref apply(auto      )    
 
done

lemma Abs_NI_Local_GetX_PutX3_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Local_GetX_PutX3_refs N) = (NI_Local_GetX_PutX3_refs M Un ABS_NI_Local_GetX_PutX3s M)"
                 unfolding NI_Local_GetX_PutX3_refs_def ABS_NI_Local_GetX_PutX3s_def   apply(rule absGen)
 using abs_NI_Local_GetX_PutX3_ref apply(auto      )    
 
done

lemma Abs_NI_Remote_GetX_Nak_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Remote_GetX_Nak_refs N) = (NI_Remote_GetX_Nak_refs M Un ABS_NI_Remote_GetX_Nak_dsts M Un ABS_NI_Remote_GetX_Nak_srcs M Un ABS_NI_Remote_GetX_Nak_src_dsts M)"
                 unfolding NI_Remote_GetX_Nak_refs_def ABS_NI_Remote_GetX_Nak_dsts_def ABS_NI_Remote_GetX_Nak_srcs_def ABS_NI_Remote_GetX_Nak_src_dsts_def   apply(rule absGen2)
 using abs_NI_Remote_GetX_Nak_ref apply(auto      )    
 
done

lemma Abs_NI_Remote_GetX_Nak_Home_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Remote_GetX_Nak_Home_refs N) = (NI_Remote_GetX_Nak_Home_refs M Un ABS_NI_Remote_GetX_Nak_Homes M)"
                 unfolding NI_Remote_GetX_Nak_Home_refs_def ABS_NI_Remote_GetX_Nak_Homes_def   apply(rule absGen)
 using abs_NI_Remote_GetX_Nak_Home_ref apply(auto      )    
 
done

lemma Abs_NI_Remote_GetX_PutX_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Remote_GetX_PutX_refs N) = (NI_Remote_GetX_PutX_refs M Un ABS_NI_Remote_GetX_PutX_dsts M Un ABS_NI_Remote_GetX_PutX_srcs M Un ABS_NI_Remote_GetX_PutX_src_dsts M)"
                 unfolding NI_Remote_GetX_PutX_refs_def ABS_NI_Remote_GetX_PutX_dsts_def ABS_NI_Remote_GetX_PutX_srcs_def ABS_NI_Remote_GetX_PutX_src_dsts_def   apply(rule absGen2)
 using abs_NI_Remote_GetX_PutX_ref apply(auto      )    
 
done

lemma Abs_NI_Remote_GetX_PutX_Home_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Remote_GetX_PutX_Home_refs N) = (NI_Remote_GetX_PutX_Home_refs M Un ABS_NI_Remote_GetX_PutX_Homes M)"
                 unfolding NI_Remote_GetX_PutX_Home_refs_def ABS_NI_Remote_GetX_PutX_Homes_def   apply(rule absGen)
 using abs_NI_Remote_GetX_PutX_Home_ref apply(auto      )    
 
done

lemma Abs_NI_Local_Puts : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Local_Put_refs) = NI_Local_Put_refs"
                 unfolding NI_Local_Put_refs_def NI_Local_Put_ref_def  apply(auto      )    
 
done

lemma Abs_NI_Remote_Put_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Remote_Put_refs N) = (NI_Remote_Put_refs M Un {skipRule})"
                 unfolding NI_Remote_Put_refs_def   apply(rule absGen)
 using abs_NI_Remote_Put_ref apply(auto      )    
 
done

lemma Abs_NI_Local_PutXAcksDones : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Local_PutXAcksDone_refs) = NI_Local_PutXAcksDone_refs"
                 unfolding NI_Local_PutXAcksDone_refs_def NI_Local_PutXAcksDone_ref_def  apply(auto      )    
 
done

lemma Abs_NI_Remote_PutX_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Remote_PutX_refs N) = (NI_Remote_PutX_refs M Un {skipRule})"
                 unfolding NI_Remote_PutX_refs_def   apply(rule absGen)
 using abs_NI_Remote_PutX_ref apply(auto      )    
 
done

lemma Abs_NI_Inv_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Inv_refs N) = (NI_Inv_refs M Un {skipRule})"
                 unfolding NI_Inv_refs_def   apply(rule absGen)
 using abs_NI_Inv_ref apply(auto      )    
 
done

lemma Abs_NI_InvAck1_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_InvAck1_refs N) = (NI_InvAck1_refs M Un ABS_NI_InvAck1s M)"
                 unfolding NI_InvAck1_refs_def ABS_NI_InvAck1s_def   apply(rule absGen)
 using abs_NI_InvAck1_ref apply(auto      )    
 
done

lemma Abs_NI_InvAck2_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_InvAck2_refs N) = (NI_InvAck2_refs M Un {skipRule})"
                 unfolding NI_InvAck2_refs_def   apply(rule absGen)
 using abs_NI_InvAck2_ref apply(auto      )    
 
done

lemma Abs_NI_Wbs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Wb_refs) = NI_Wb_refs"
                 unfolding NI_Wb_refs_def NI_Wb_ref_def  apply(auto      )    
 
done

lemma Abs_NI_FAcks : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_FAck_refs) = NI_FAck_refs"
                 unfolding NI_FAck_refs_def NI_FAck_ref_def  apply(auto      )    
 
done

lemma Abs_NI_ShWb_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_ShWb_refs N) = (NI_ShWb_refs M Un ABS_NI_ShWbs M)"
                 unfolding NI_ShWb_refs_def ABS_NI_ShWbs_def   apply(rule absGen)
 using abs_NI_ShWb_ref apply(auto      )    
 
done

lemma Abs_NI_Replace_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` NI_Replace_refs N) = (NI_Replace_refs M Un {skipRule})"
                 unfolding NI_Replace_refs_def   apply(rule absGen)
 using abs_NI_Replace_ref apply(auto      )    
 
done

definition ABS_rules :: "nat \<Rightarrow> rule set" where [simp]:
 "ABS_rules N = (PI_Remote_Get_refs N \<union> (PI_Local_Get_Get_refs \<union> (PI_Local_Get_Put_refs \<union> (PI_Remote_GetX_refs N \<union> (PI_Local_GetX_GetX_refs \<union> (PI_Local_GetX_PutX_refs N \<union> (PI_Remote_PutX_refs N \<union> (ABS_PI_Remote_PutXs N \<union> (PI_Local_PutX_refs \<union> (PI_Remote_Replace_refs N \<union> (PI_Local_Replace_refs \<union> (NI_Nak_refs N \<union> (NI_Nak_Home_refs \<union> (NI_Nak_Clear_refs \<union> (NI_Local_Get_Nak_refs N \<union> (NI_Local_Get_Get_refs N \<union> (ABS_NI_Local_Get_Gets N \<union> (NI_Local_Get_Put_refs N \<union> (ABS_NI_Local_Get_Puts N \<union> (NI_Remote_Get_Nak_refs N \<union> (ABS_NI_Remote_Get_Nak_srcs N \<union> (ABS_NI_Remote_Get_Nak_dsts N \<union> (ABS_NI_Remote_Get_Nak_src_dsts N \<union> (NI_Remote_Get_Nak_Home_refs N \<union> (ABS_NI_Remote_Get_Nak_Homes N \<union> (NI_Remote_Get_Put_refs N \<union> (ABS_NI_Remote_Get_Put_srcs N \<union> (ABS_NI_Remote_Get_Put_dsts N \<union> (ABS_NI_Remote_Get_Put_src_dsts N \<union> (NI_Remote_Get_Put_Home_refs N \<union> (ABS_NI_Remote_Get_Put_Homes N \<union> (NI_Local_GetX_Nak_refs N \<union> (NI_Local_GetX_GetX_refs N \<union> (ABS_NI_Local_GetX_GetXs N \<union> (NI_Local_GetX_PutX1_refs N \<union> (ABS_NI_Local_GetX_PutX1s N \<union> (NI_Local_GetX_PutX2_refs N \<union> (ABS_NI_Local_GetX_PutX2s N \<union> (NI_Local_GetX_PutX3_refs N \<union> (ABS_NI_Local_GetX_PutX3s N \<union> (NI_Remote_GetX_Nak_refs N \<union> (ABS_NI_Remote_GetX_Nak_srcs N \<union> (ABS_NI_Remote_GetX_Nak_dsts N \<union> (ABS_NI_Remote_GetX_Nak_src_dsts N \<union> (NI_Remote_GetX_Nak_Home_refs N \<union> (ABS_NI_Remote_GetX_Nak_Homes N \<union> (NI_Remote_GetX_PutX_refs N \<union> (ABS_NI_Remote_GetX_PutX_srcs N \<union> (ABS_NI_Remote_GetX_PutX_dsts N \<union> (ABS_NI_Remote_GetX_PutX_src_dsts N \<union> (NI_Remote_GetX_PutX_Home_refs N \<union> (ABS_NI_Remote_GetX_PutX_Homes N \<union> (NI_Local_Put_refs \<union> (NI_Remote_Put_refs N \<union> (NI_Local_PutXAcksDone_refs \<union> (NI_Remote_PutX_refs N \<union> (NI_Inv_refs N \<union> (NI_InvAck1_refs N \<union> (ABS_NI_InvAck1s N \<union> (NI_InvAck2_refs N \<union> (NI_Wb_refs \<union> (NI_FAck_refs \<union> (NI_ShWb_refs N \<union> (ABS_NI_ShWbs N \<union> (NI_Replace_refs N \<union> {skipRule})))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))"

definition ABS_rules' :: "nat \<Rightarrow> rule set" where [simp]:
 "ABS_rules' N = ((PI_Remote_Get_refs N \<union> {skipRule}) \<union> ((PI_Local_Get_Get_refs) \<union> ((PI_Local_Get_Put_refs) \<union> ((PI_Remote_GetX_refs N \<union> {skipRule}) \<union> ((PI_Local_GetX_GetX_refs) \<union> ((PI_Local_GetX_PutX_refs N) \<union> ((PI_Remote_PutX_refs N \<union> ABS_PI_Remote_PutXs N) \<union> ((PI_Local_PutX_refs) \<union> ((PI_Remote_Replace_refs N \<union> {skipRule}) \<union> ((PI_Local_Replace_refs) \<union> ((NI_Nak_refs N \<union> {skipRule}) \<union> ((NI_Nak_Home_refs) \<union> ((NI_Nak_Clear_refs) \<union> ((NI_Local_Get_Nak_refs N \<union> {skipRule}) \<union> ((NI_Local_Get_Get_refs N \<union> ABS_NI_Local_Get_Gets N) \<union> ((NI_Local_Get_Put_refs N \<union> ABS_NI_Local_Get_Puts N) \<union> ((NI_Remote_Get_Nak_refs N \<union> (ABS_NI_Remote_Get_Nak_srcs N \<union> (ABS_NI_Remote_Get_Nak_dsts N \<union> ABS_NI_Remote_Get_Nak_src_dsts N))) \<union> ((NI_Remote_Get_Nak_Home_refs N \<union> ABS_NI_Remote_Get_Nak_Homes N) \<union> ((NI_Remote_Get_Put_refs N \<union> (ABS_NI_Remote_Get_Put_srcs N \<union> (ABS_NI_Remote_Get_Put_dsts N \<union> ABS_NI_Remote_Get_Put_src_dsts N))) \<union> ((NI_Remote_Get_Put_Home_refs N \<union> ABS_NI_Remote_Get_Put_Homes N) \<union> ((NI_Local_GetX_Nak_refs N \<union> {skipRule}) \<union> ((NI_Local_GetX_GetX_refs N \<union> ABS_NI_Local_GetX_GetXs N) \<union> ((NI_Local_GetX_PutX1_refs N \<union> ABS_NI_Local_GetX_PutX1s N) \<union> ((NI_Local_GetX_PutX2_refs N \<union> ABS_NI_Local_GetX_PutX2s N) \<union> ((NI_Local_GetX_PutX3_refs N \<union> ABS_NI_Local_GetX_PutX3s N) \<union> ((NI_Remote_GetX_Nak_refs N \<union> (ABS_NI_Remote_GetX_Nak_srcs N \<union> (ABS_NI_Remote_GetX_Nak_dsts N \<union> ABS_NI_Remote_GetX_Nak_src_dsts N))) \<union> ((NI_Remote_GetX_Nak_Home_refs N \<union> ABS_NI_Remote_GetX_Nak_Homes N) \<union> ((NI_Remote_GetX_PutX_refs N \<union> (ABS_NI_Remote_GetX_PutX_srcs N \<union> (ABS_NI_Remote_GetX_PutX_dsts N \<union> ABS_NI_Remote_GetX_PutX_src_dsts N))) \<union> ((NI_Remote_GetX_PutX_Home_refs N \<union> ABS_NI_Remote_GetX_PutX_Homes N) \<union> ((NI_Local_Put_refs) \<union> ((NI_Remote_Put_refs N \<union> {skipRule}) \<union> ((NI_Local_PutXAcksDone_refs) \<union> ((NI_Remote_PutX_refs N \<union> {skipRule}) \<union> ((NI_Inv_refs N \<union> {skipRule}) \<union> ((NI_InvAck1_refs N \<union> ABS_NI_InvAck1s N) \<union> ((NI_InvAck2_refs N \<union> {skipRule}) \<union> ((NI_Wb_refs) \<union> ((NI_FAck_refs) \<union> ((NI_ShWb_refs N \<union> ABS_NI_ShWbs N) \<union> (NI_Replace_refs N \<union> {skipRule}))))))))))))))))))))))))))))))))))))))))"

lemma ABS_rules_eq_rules' : 
                  " 
                  ABS_rules M = ABS_rules' M"
                   apply(auto      )    
 
done

lemma ABS_all : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` rule_refs N) = ABS_rules M"
                   apply(subst ABS_rules_eq_rules'       )

unfolding rule_refs_def ABS_rules'_def  apply(intro  image_UnI )

  apply(auto     simp add: Abs_PI_Local_Get_Gets Abs_PI_Local_Get_Puts Abs_PI_Local_GetX_GetXs Abs_PI_Local_GetX_PutXs Abs_PI_Local_PutXs Abs_PI_Local_Replaces Abs_NI_Nak_Homes Abs_NI_Nak_Clears Abs_NI_Local_Puts Abs_NI_Local_PutXAcksDones Abs_NI_Wbs Abs_NI_FAcks Abs_PI_Remote_Get_refs Abs_PI_Remote_GetX_refs Abs_PI_Remote_PutX_refs Abs_PI_Remote_Replace_refs Abs_NI_Nak_refs Abs_NI_Local_Get_Nak_refs Abs_NI_Local_Get_Get_refs Abs_NI_Local_Get_Put_refs Abs_NI_Remote_Get_Nak_refs Abs_NI_Remote_Get_Nak_Home_refs Abs_NI_Remote_Get_Put_refs Abs_NI_Remote_Get_Put_Home_refs Abs_NI_Local_GetX_Nak_refs Abs_NI_Local_GetX_GetX_refs Abs_NI_Local_GetX_PutX1_refs Abs_NI_Local_GetX_PutX2_refs Abs_NI_Local_GetX_PutX3_refs Abs_NI_Remote_GetX_Nak_refs Abs_NI_Remote_GetX_Nak_Home_refs Abs_NI_Remote_GetX_PutX_refs Abs_NI_Remote_GetX_PutX_Home_refs Abs_NI_Remote_Put_refs Abs_NI_Remote_PutX_refs Abs_NI_Inv_refs Abs_NI_InvAck1_refs Abs_NI_InvAck2_refs Abs_NI_ShWb_refs Abs_NI_Replace_refs )    
 
done

definition Lemma_1' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_1' N dst p \<equiv> \<not>\<^sub>f Const (index dst) =\<^sub>f Const (index p) \<and>\<^sub>f
  IVar (Para ''Sta.Proc.CacheState'' dst) =\<^sub>f Const CACHE_E \<longrightarrow>\<^sub>f
  IVar (Ident ''Sta.Dir.Dirty'') =\<^sub>f Const true \<and>\<^sub>f
  \<not>\<^sub>f IVar (Ident ''Sta.WbMsg.Cmd'') =\<^sub>f Const WB_Wb \<and>\<^sub>f
  \<not>\<^sub>f IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_ShWb \<and>\<^sub>f
  \<not>\<^sub>f IVar (Para ''Sta.Proc.CacheState'' p) =\<^sub>f Const CACHE_E \<and>\<^sub>f
  \<not>\<^sub>f IVar (Ident ''Sta.HomeProc.CacheState'') =\<^sub>f Const CACHE_E \<and>\<^sub>f
  \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Put \<and>\<^sub>f
  \<not>\<^sub>f IVar (Para ''Sta.UniMsg.Cmd'' p) =\<^sub>f Const UNI_PutX \<and>\<^sub>f
  \<not>\<^sub>f IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_PutX"

lemma absTransfLemma_1' : 
                  "[|M < N;M = 1;l <= 1|] 
                 ==> absTransfForm (env N) M (Lemma_1' N 0 l) = Lemma_1' N 0 l"
                 unfolding Lemma_1'_def  apply(auto      )    
 
done

lemma strengthenVsObsLemma_1 : 
                  " 
                  strengthenVsObs (Lemma_1 N) (Lemma_1' N) N"
                 unfolding Lemma_1_def Lemma_1'_def   apply(rule strengthenVsObsDiff)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma SafeAndderiveFormLemma_1' : 
                  "[|M < N;M = 1;l <= M;k <= M|] 
                 ==> safeForm (env N) M (Lemma_1' N k l) & deriveForm (env N) (Lemma_1' N k l)"
                 unfolding Lemma_1'_def  apply(auto      )    
 
done

definition Lemma_2a' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_2a' N src dst \<equiv> \<not>\<^sub>f Const (index src) =\<^sub>f Const (index dst) \<and>\<^sub>f
  IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_Get \<and>\<^sub>f
  IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const false \<and>\<^sub>f
  IVar (Para ''Sta.UniMsg.Proc'' src) =\<^sub>f Const (index dst) \<longrightarrow>\<^sub>f
  IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
  IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
  IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
  IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index src) \<and>\<^sub>f
  IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_Get"

lemma absTransfLemma_2a' : 
                  "[|M < N;M = 1;l <= 1|] 
                 ==> absTransfForm (env N) M (Lemma_2a' N 0 l) = Lemma_2a' N 0 l"
                 unfolding Lemma_2a'_def  apply(auto      )    
 
done

lemma strengthenVsObsLemma_2a : 
                  " 
                  strengthenVsObs (Lemma_2a N) (Lemma_2a' N) N"
                 unfolding Lemma_2a_def Lemma_2a'_def   apply(rule strengthenVsObsSame)
done

lemma SafeAndderiveFormLemma_2a' : 
                  "[|M < N;M = 1;l <= M;k <= M|] 
                 ==> safeForm (env N) M (Lemma_2a' N k l) & deriveForm (env N) (Lemma_2a' N k l)"
                 unfolding Lemma_2a'_def  apply(auto      )    
 
done

definition Lemma_2b' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_2b' N src dst \<equiv> IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_Get \<and>\<^sub>f
  IVar (Ident ''Sta.HomeUniMsg.HomeProc'') =\<^sub>f Const false \<and>\<^sub>f
  IVar (Ident ''Sta.HomeUniMsg.Proc'') =\<^sub>f Const (index dst) \<longrightarrow>\<^sub>f
  IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
  IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
  IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const true \<and>\<^sub>f
  IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_Get"

lemma absTransfLemma_2b' : 
                  "[|M < N;M = 1;l <= 1|] 
                 ==> absTransfForm (env N) M (Lemma_2b' N 0 l) = Lemma_2b' N 0 l"
                 unfolding Lemma_2b'_def  apply(auto      )    
 
done

lemma strengthenVsObsLemma_2b : 
                  " 
                  strengthenVsObs (Lemma_2b N) (Lemma_2b' N) N"
                 unfolding Lemma_2b_def Lemma_2b'_def   apply(rule strengthenVsObsSame)
done

lemma SafeAndderiveFormLemma_2b' : 
                  "[|M < N;M = 1;l <= M;k <= M|] 
                 ==> safeForm (env N) M (Lemma_2b' N k l) & deriveForm (env N) (Lemma_2b' N k l)"
                 unfolding Lemma_2b'_def  apply(auto      )    
 
done

definition Lemma_3a' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_3a' N src dst \<equiv> \<not>\<^sub>f Const (index src) =\<^sub>f Const (index dst) \<and>\<^sub>f
  IVar (Para ''Sta.UniMsg.Cmd'' src) =\<^sub>f Const UNI_GetX \<and>\<^sub>f
  IVar (Para ''Sta.UniMsg.HomeProc'' src) =\<^sub>f Const false \<and>\<^sub>f
  IVar (Para ''Sta.UniMsg.Proc'' src) =\<^sub>f Const (index dst) \<longrightarrow>\<^sub>f
  IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
  IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
  IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
  IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index src) \<and>\<^sub>f
  IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_GetX"

lemma absTransfLemma_3a' : 
                  "[|M < N;M = 1;l <= 1|] 
                 ==> absTransfForm (env N) M (Lemma_3a' N 0 l) = Lemma_3a' N 0 l"
                 unfolding Lemma_3a'_def  apply(auto      )    
 
done

lemma strengthenVsObsLemma_3a : 
                  " 
                  strengthenVsObs (Lemma_3a N) (Lemma_3a' N) N"
                 unfolding Lemma_3a_def Lemma_3a'_def   apply(rule strengthenVsObsSame)
done

lemma SafeAndderiveFormLemma_3a' : 
                  "[|M < N;M = 1;l <= M;k <= M|] 
                 ==> safeForm (env N) M (Lemma_3a' N k l) & deriveForm (env N) (Lemma_3a' N k l)"
                 unfolding Lemma_3a'_def  apply(auto      )    
 
done

definition Lemma_3b' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_3b' N src dst \<equiv> IVar (Ident ''Sta.HomeUniMsg.Cmd'') =\<^sub>f Const UNI_GetX \<and>\<^sub>f
  IVar (Ident ''Sta.HomeUniMsg.HomeProc'') =\<^sub>f Const false \<and>\<^sub>f
  IVar (Ident ''Sta.HomeUniMsg.Proc'') =\<^sub>f Const (index dst) \<longrightarrow>\<^sub>f
  IVar (Ident ''Sta.Dir.Pending'') =\<^sub>f Const true \<and>\<^sub>f
  IVar (Ident ''Sta.Dir.Local'') =\<^sub>f Const false \<and>\<^sub>f
  IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const true \<and>\<^sub>f
  IVar (Ident ''Sta.FwdCmd'') =\<^sub>f Const UNI_GetX"

lemma absTransfLemma_3b' : 
                  "[|M < N;M = 1;l <= 1|] 
                 ==> absTransfForm (env N) M (Lemma_3b' N 0 l) = Lemma_3b' N 0 l"
                 unfolding Lemma_3b'_def  apply(auto      )    
 
done

lemma strengthenVsObsLemma_3b : 
                  " 
                  strengthenVsObs (Lemma_3b N) (Lemma_3b' N) N"
                 unfolding Lemma_3b_def Lemma_3b'_def   apply(rule strengthenVsObsSame)
done

lemma SafeAndderiveFormLemma_3b' : 
                  "[|M < N;M = 1;l <= M;k <= M|] 
                 ==> safeForm (env N) M (Lemma_3b' N k l) & deriveForm (env N) (Lemma_3b' N k l)"
                 unfolding Lemma_3b'_def  apply(auto      )    
 
done

definition Lemma_4' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_4' N src q \<equiv> \<not>\<^sub>f Const (index src) =\<^sub>f Const (index q) \<and>\<^sub>f
  IVar (Para ''Sta.InvMsg.Cmd'' src) =\<^sub>f Const INV_InvAck \<longrightarrow>\<^sub>f
  IVar (Ident ''Sta.Collecting'') =\<^sub>f Const true \<and>\<^sub>f
  IVar (Ident ''Sta.NakcMsg.Cmd'') =\<^sub>f Const NAKC_None \<and>\<^sub>f
  IVar (Ident ''Sta.ShWbMsg.Cmd'') =\<^sub>f Const SHWB_None \<and>\<^sub>f
  (IVar (Para ''Sta.UniMsg.Cmd'' q) =\<^sub>f Const UNI_Get \<or>\<^sub>f
  IVar (Para ''Sta.UniMsg.Cmd'' q) =\<^sub>f Const UNI_GetX \<longrightarrow>\<^sub>f
  IVar (Para ''Sta.UniMsg.HomeProc'' q) =\<^sub>f Const true) \<and>\<^sub>f
  (IVar (Para ''Sta.UniMsg.Cmd'' q) =\<^sub>f Const UNI_PutX \<longrightarrow>\<^sub>f
  IVar (Para ''Sta.UniMsg.HomeProc'' q) =\<^sub>f Const true \<and>\<^sub>f
  IVar (Ident ''Sta.HomePendReqSrc'') =\<^sub>f Const false \<and>\<^sub>f
  IVar (Ident ''Sta.PendReqSrc'') =\<^sub>f Const (index q))"

lemma absTransfLemma_4' : 
                  "[|M < N;M = 1;l <= 1|] 
                 ==> absTransfForm (env N) M (Lemma_4' N 0 l) = Lemma_4' N 0 l"
                 unfolding Lemma_4'_def  apply(auto      )    
 
done

lemma strengthenVsObsLemma_4 : 
                  " 
                  strengthenVsObs (Lemma_4 N) (Lemma_4' N) N"
                 unfolding Lemma_4_def Lemma_4'_def   apply(rule strengthenVsObsDiff)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma SafeAndderiveFormLemma_4' : 
                  "[|M < N;M = 1;l <= M;k <= M|] 
                 ==> safeForm (env N) M (Lemma_4' N k l) & deriveForm (env N) (Lemma_4' N k l)"
                 unfolding Lemma_4'_def  apply(auto      )    
 
done

lemma symInvs : 
             " 
                  symParamForm2 N (Lemma_1' N)"
                 

" 
                  symParamForm2 N (Lemma_2a' N)"
                 

" 
                  symParamForm2 N (Lemma_2b' N)"
                 

" 
                  symParamForm2 N (Lemma_3a' N)"
                 

" 
                  symParamForm2 N (Lemma_3b' N)"
                 

" 
                  symParamForm2 N (Lemma_4' N)"
                 
 
             unfolding Lemma_1'_def Lemma_2a'_def Lemma_2b'_def Lemma_3a'_def Lemma_3b'_def Lemma_4'_def  apply(auto      )    
 
subgoal    apply(intro  symParamForm2Imply symParamFormForallExcl2 )
  
  unfolding symParamForm2_def  apply(auto      )    
   done

subgoal    apply(intro  symParamForm2Imply symParamFormForallExcl2 )
  
  unfolding symParamForm2_def  apply(auto      )    
   done

subgoal    apply(intro  symParamForm2Imply symParamFormForallExcl2 )
  
  unfolding symParamForm2_def  apply(auto      )    
   done

subgoal    apply(intro  symParamForm2Imply symParamFormForallExcl2 )
  
  unfolding symParamForm2_def  apply(auto      )    
   done

subgoal    apply(intro  symParamForm2Imply symParamFormForallExcl2 )
  
  unfolding symParamForm2_def  apply(auto      )    
   done

subgoal    apply(intro  symParamForm2Imply symParamFormForallExcl2 )
  
  unfolding symParamForm2_def  apply(auto      )    
   done

done

definition lemmasFor_PI_Remote_Get' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_PI_Remote_Get' N = []"

lemma strengthenVsObsLs_lemmasFor_PI_Remote_Get : 
                  " 
                  strengthenVsObsLs (lemmasFor_PI_Remote_Get N) (lemmasFor_PI_Remote_Get' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_PI_Remote_Get_def lemmasFor_PI_Remote_Get'_def  apply(auto      )    
 
done

lemma lemmaPI_Remote_Get_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : PI_Remote_Get_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding PI_Remote_Get_refs_def PI_Remote_Get_ref_def  apply(auto      )    
 
done

definition lemmasFor_PI_Local_Get_Get' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_PI_Local_Get_Get' N = []"

lemma strengthenVsObsLs_lemmasFor_PI_Local_Get_Get : 
                  " 
                  strengthenVsObsLs (lemmasFor_PI_Local_Get_Get N) (lemmasFor_PI_Local_Get_Get' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_PI_Local_Get_Get_def lemmasFor_PI_Local_Get_Get'_def  apply(auto      )    
 
done

lemma lemmaPI_Local_Get_Get_fitEnv [intro]: 
                  "[|formEval (pre r) s;fitEnv s (env N);r : PI_Local_Get_Get_refs|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding PI_Local_Get_Get_refs_def PI_Local_Get_Get_ref_def  apply(auto      )    
 
done

definition lemmasFor_PI_Local_Get_Put' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_PI_Local_Get_Put' N = []"

lemma strengthenVsObsLs_lemmasFor_PI_Local_Get_Put : 
                  " 
                  strengthenVsObsLs (lemmasFor_PI_Local_Get_Put N) (lemmasFor_PI_Local_Get_Put' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_PI_Local_Get_Put_def lemmasFor_PI_Local_Get_Put'_def  apply(auto      )    
 
done

lemma lemmaPI_Local_Get_Put_fitEnv [intro]: 
                  "[|formEval (pre r) s;fitEnv s (env N);r : PI_Local_Get_Put_refs|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding PI_Local_Get_Put_refs_def PI_Local_Get_Put_ref_def  apply(auto      )    
 
done

definition lemmasFor_PI_Remote_GetX' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_PI_Remote_GetX' N = []"

lemma strengthenVsObsLs_lemmasFor_PI_Remote_GetX : 
                  " 
                  strengthenVsObsLs (lemmasFor_PI_Remote_GetX N) (lemmasFor_PI_Remote_GetX' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_PI_Remote_GetX_def lemmasFor_PI_Remote_GetX'_def  apply(auto      )    
 
done

lemma lemmaPI_Remote_GetX_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : PI_Remote_GetX_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding PI_Remote_GetX_refs_def PI_Remote_GetX_ref_def  apply(auto      )    
 
done

definition lemmasFor_PI_Local_GetX_GetX' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_PI_Local_GetX_GetX' N = []"

lemma strengthenVsObsLs_lemmasFor_PI_Local_GetX_GetX : 
                  " 
                  strengthenVsObsLs (lemmasFor_PI_Local_GetX_GetX N) (lemmasFor_PI_Local_GetX_GetX' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_PI_Local_GetX_GetX_def lemmasFor_PI_Local_GetX_GetX'_def  apply(auto      )    
 
done

lemma lemmaPI_Local_GetX_GetX_fitEnv [intro]: 
                  "[|formEval (pre r) s;fitEnv s (env N);r : PI_Local_GetX_GetX_refs|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding PI_Local_GetX_GetX_refs_def PI_Local_GetX_GetX_ref_def  apply(auto      )    
 
done

definition lemmasFor_PI_Local_GetX_PutX' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_PI_Local_GetX_PutX' N = []"

lemma strengthenVsObsLs_lemmasFor_PI_Local_GetX_PutX : 
                  " 
                  strengthenVsObsLs (lemmasFor_PI_Local_GetX_PutX N) (lemmasFor_PI_Local_GetX_PutX' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_PI_Local_GetX_PutX_def lemmasFor_PI_Local_GetX_PutX'_def  apply(auto      )    
 
done

lemma lemmaPI_Local_GetX_PutX_fitEnv [intro]: 
                  "[|formEval (pre r) s;fitEnv s (env N);r : PI_Local_GetX_PutX_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding PI_Local_GetX_PutX_refs_def PI_Local_GetX_PutX_ref_def  apply(auto      )    
 
done

definition lemmasFor_PI_Remote_PutX' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_PI_Remote_PutX' N = [Lemma_1' N]"

lemma strengthenVsObsLs_lemmasFor_PI_Remote_PutX : 
                  " 
                  strengthenVsObsLs (lemmasFor_PI_Remote_PutX N) (lemmasFor_PI_Remote_PutX' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_PI_Remote_PutX_def lemmasFor_PI_Remote_PutX'_def  apply(auto intro: strengthenVsObsLemma_1     )    
 
done

lemma lemmaPI_Remote_PutX_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : PI_Remote_PutX_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding PI_Remote_PutX_refs_def PI_Remote_PutX_ref_def  apply(auto      )    
 
done

definition lemmasFor_PI_Local_PutX' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_PI_Local_PutX' N = []"

lemma strengthenVsObsLs_lemmasFor_PI_Local_PutX : 
                  " 
                  strengthenVsObsLs (lemmasFor_PI_Local_PutX N) (lemmasFor_PI_Local_PutX' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_PI_Local_PutX_def lemmasFor_PI_Local_PutX'_def  apply(auto      )    
 
done

lemma lemmaPI_Local_PutX_fitEnv [intro]: 
                  "[|formEval (pre r) s;fitEnv s (env N);r : PI_Local_PutX_refs|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding PI_Local_PutX_refs_def PI_Local_PutX_ref_def  apply(auto      )    
 
done

definition lemmasFor_PI_Remote_Replace' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_PI_Remote_Replace' N = []"

lemma strengthenVsObsLs_lemmasFor_PI_Remote_Replace : 
                  " 
                  strengthenVsObsLs (lemmasFor_PI_Remote_Replace N) (lemmasFor_PI_Remote_Replace' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_PI_Remote_Replace_def lemmasFor_PI_Remote_Replace'_def  apply(auto      )    
 
done

lemma lemmaPI_Remote_Replace_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : PI_Remote_Replace_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding PI_Remote_Replace_refs_def PI_Remote_Replace_ref_def  apply(auto      )    
 
done

definition lemmasFor_PI_Local_Replace' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_PI_Local_Replace' N = []"

lemma strengthenVsObsLs_lemmasFor_PI_Local_Replace : 
                  " 
                  strengthenVsObsLs (lemmasFor_PI_Local_Replace N) (lemmasFor_PI_Local_Replace' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_PI_Local_Replace_def lemmasFor_PI_Local_Replace'_def  apply(auto      )    
 
done

lemma lemmaPI_Local_Replace_fitEnv [intro]: 
                  "[|formEval (pre r) s;fitEnv s (env N);r : PI_Local_Replace_refs|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding PI_Local_Replace_refs_def PI_Local_Replace_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Nak' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Nak' N = []"

lemma strengthenVsObsLs_lemmasFor_NI_Nak : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Nak N) (lemmasFor_NI_Nak' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Nak_def lemmasFor_NI_Nak'_def  apply(auto      )    
 
done

lemma lemmaNI_Nak_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Nak_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Nak_refs_def NI_Nak_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Nak_Home' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Nak_Home' N = []"

lemma strengthenVsObsLs_lemmasFor_NI_Nak_Home : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Nak_Home N) (lemmasFor_NI_Nak_Home' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Nak_Home_def lemmasFor_NI_Nak_Home'_def  apply(auto      )    
 
done

lemma lemmaNI_Nak_Home_fitEnv [intro]: 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Nak_Home_refs|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Nak_Home_refs_def NI_Nak_Home_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Nak_Clear' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Nak_Clear' N = []"

lemma strengthenVsObsLs_lemmasFor_NI_Nak_Clear : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Nak_Clear N) (lemmasFor_NI_Nak_Clear' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Nak_Clear_def lemmasFor_NI_Nak_Clear'_def  apply(auto      )    
 
done

lemma lemmaNI_Nak_Clear_fitEnv [intro]: 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Nak_Clear_refs|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Nak_Clear_refs_def NI_Nak_Clear_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Local_Get_Nak' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Local_Get_Nak' N = []"

lemma strengthenVsObsLs_lemmasFor_NI_Local_Get_Nak : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Local_Get_Nak N) (lemmasFor_NI_Local_Get_Nak' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Local_Get_Nak_def lemmasFor_NI_Local_Get_Nak'_def  apply(auto      )    
 
done

lemma lemmaNI_Local_Get_Nak_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Local_Get_Nak_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Local_Get_Nak_refs_def NI_Local_Get_Nak_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Local_Get_Get' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Local_Get_Get' N = []"

lemma strengthenVsObsLs_lemmasFor_NI_Local_Get_Get : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Local_Get_Get N) (lemmasFor_NI_Local_Get_Get' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Local_Get_Get_def lemmasFor_NI_Local_Get_Get'_def  apply(auto      )    
 
done

lemma lemmaNI_Local_Get_Get_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Local_Get_Get_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Local_Get_Get_refs_def NI_Local_Get_Get_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Local_Get_Put' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Local_Get_Put' N = []"

lemma strengthenVsObsLs_lemmasFor_NI_Local_Get_Put : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Local_Get_Put N) (lemmasFor_NI_Local_Get_Put' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Local_Get_Put_def lemmasFor_NI_Local_Get_Put'_def  apply(auto      )    
 
done

lemma lemmaNI_Local_Get_Put_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Local_Get_Put_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Local_Get_Put_refs_def NI_Local_Get_Put_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Remote_Get_Nak' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Remote_Get_Nak' N = [Lemma_2a' N]"

lemma strengthenVsObsLs_lemmasFor_NI_Remote_Get_Nak : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Remote_Get_Nak N) (lemmasFor_NI_Remote_Get_Nak' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Remote_Get_Nak_def lemmasFor_NI_Remote_Get_Nak'_def  apply(auto intro: strengthenVsObsLemma_2a     )    
 
done

lemma lemmaNI_Remote_Get_Nak_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Remote_Get_Nak_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Remote_Get_Nak_refs_def NI_Remote_Get_Nak_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Remote_Get_Nak_Home' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Remote_Get_Nak_Home' N = [Lemma_2b' N]"

lemma strengthenVsObsLs_lemmasFor_NI_Remote_Get_Nak_Home : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Remote_Get_Nak_Home N) (lemmasFor_NI_Remote_Get_Nak_Home' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Remote_Get_Nak_Home_def lemmasFor_NI_Remote_Get_Nak_Home'_def  apply(auto intro: strengthenVsObsLemma_2b     )    
 
done

lemma lemmaNI_Remote_Get_Nak_Home_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Remote_Get_Nak_Home_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Remote_Get_Nak_Home_refs_def NI_Remote_Get_Nak_Home_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Remote_Get_Put' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Remote_Get_Put' N = [Lemma_2a' N, Lemma_1' N]"

lemma strengthenVsObsLs_lemmasFor_NI_Remote_Get_Put : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Remote_Get_Put N) (lemmasFor_NI_Remote_Get_Put' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Remote_Get_Put_def lemmasFor_NI_Remote_Get_Put'_def  apply(auto intro: strengthenVsObsLemma_2a strengthenVsObsLemma_1     )    
 
done

lemma lemmaNI_Remote_Get_Put_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Remote_Get_Put_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Remote_Get_Put_refs_def NI_Remote_Get_Put_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Remote_Get_Put_Home' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Remote_Get_Put_Home' N = [Lemma_2b' N, Lemma_1' N]"

lemma strengthenVsObsLs_lemmasFor_NI_Remote_Get_Put_Home : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Remote_Get_Put_Home N) (lemmasFor_NI_Remote_Get_Put_Home' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Remote_Get_Put_Home_def lemmasFor_NI_Remote_Get_Put_Home'_def  apply(auto intro: strengthenVsObsLemma_2b strengthenVsObsLemma_1     )    
 
done

lemma lemmaNI_Remote_Get_Put_Home_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Remote_Get_Put_Home_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Remote_Get_Put_Home_refs_def NI_Remote_Get_Put_Home_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Local_GetX_Nak' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Local_GetX_Nak' N = []"

lemma strengthenVsObsLs_lemmasFor_NI_Local_GetX_Nak : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Local_GetX_Nak N) (lemmasFor_NI_Local_GetX_Nak' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Local_GetX_Nak_def lemmasFor_NI_Local_GetX_Nak'_def  apply(auto      )    
 
done

lemma lemmaNI_Local_GetX_Nak_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Local_GetX_Nak_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Local_GetX_Nak_refs_def NI_Local_GetX_Nak_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Local_GetX_GetX' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Local_GetX_GetX' N = []"

lemma strengthenVsObsLs_lemmasFor_NI_Local_GetX_GetX : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Local_GetX_GetX N) (lemmasFor_NI_Local_GetX_GetX' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Local_GetX_GetX_def lemmasFor_NI_Local_GetX_GetX'_def  apply(auto      )    
 
done

lemma lemmaNI_Local_GetX_GetX_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Local_GetX_GetX_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Local_GetX_GetX_refs_def NI_Local_GetX_GetX_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Local_GetX_PutX1' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Local_GetX_PutX1' N = []"

lemma strengthenVsObsLs_lemmasFor_NI_Local_GetX_PutX1 : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Local_GetX_PutX1 N) (lemmasFor_NI_Local_GetX_PutX1' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Local_GetX_PutX1_def lemmasFor_NI_Local_GetX_PutX1'_def  apply(auto      )    
 
done

lemma lemmaNI_Local_GetX_PutX1_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Local_GetX_PutX1_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Local_GetX_PutX1_refs_def NI_Local_GetX_PutX1_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Local_GetX_PutX2' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Local_GetX_PutX2' N = []"

lemma strengthenVsObsLs_lemmasFor_NI_Local_GetX_PutX2 : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Local_GetX_PutX2 N) (lemmasFor_NI_Local_GetX_PutX2' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Local_GetX_PutX2_def lemmasFor_NI_Local_GetX_PutX2'_def  apply(auto      )    
 
done

lemma lemmaNI_Local_GetX_PutX2_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Local_GetX_PutX2_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Local_GetX_PutX2_refs_def NI_Local_GetX_PutX2_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Local_GetX_PutX3' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Local_GetX_PutX3' N = []"

lemma strengthenVsObsLs_lemmasFor_NI_Local_GetX_PutX3 : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Local_GetX_PutX3 N) (lemmasFor_NI_Local_GetX_PutX3' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Local_GetX_PutX3_def lemmasFor_NI_Local_GetX_PutX3'_def  apply(auto      )    
 
done

lemma lemmaNI_Local_GetX_PutX3_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Local_GetX_PutX3_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Local_GetX_PutX3_refs_def NI_Local_GetX_PutX3_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Remote_GetX_Nak' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Remote_GetX_Nak' N = [Lemma_3a' N]"

lemma strengthenVsObsLs_lemmasFor_NI_Remote_GetX_Nak : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Remote_GetX_Nak N) (lemmasFor_NI_Remote_GetX_Nak' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Remote_GetX_Nak_def lemmasFor_NI_Remote_GetX_Nak'_def  apply(auto intro: strengthenVsObsLemma_3a     )    
 
done

lemma lemmaNI_Remote_GetX_Nak_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Remote_GetX_Nak_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Remote_GetX_Nak_refs_def NI_Remote_GetX_Nak_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Remote_GetX_Nak_Home' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Remote_GetX_Nak_Home' N = [Lemma_3b' N]"

lemma strengthenVsObsLs_lemmasFor_NI_Remote_GetX_Nak_Home : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Remote_GetX_Nak_Home N) (lemmasFor_NI_Remote_GetX_Nak_Home' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Remote_GetX_Nak_Home_def lemmasFor_NI_Remote_GetX_Nak_Home'_def  apply(auto intro: strengthenVsObsLemma_3b     )    
 
done

lemma lemmaNI_Remote_GetX_Nak_Home_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Remote_GetX_Nak_Home_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Remote_GetX_Nak_Home_refs_def NI_Remote_GetX_Nak_Home_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Remote_GetX_PutX' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Remote_GetX_PutX' N = [Lemma_3a' N, Lemma_1' N]"

lemma strengthenVsObsLs_lemmasFor_NI_Remote_GetX_PutX : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Remote_GetX_PutX N) (lemmasFor_NI_Remote_GetX_PutX' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Remote_GetX_PutX_def lemmasFor_NI_Remote_GetX_PutX'_def  apply(auto intro: strengthenVsObsLemma_3a strengthenVsObsLemma_1     )    
 
done

lemma lemmaNI_Remote_GetX_PutX_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Remote_GetX_PutX_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Remote_GetX_PutX_refs_def NI_Remote_GetX_PutX_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Remote_GetX_PutX_Home' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Remote_GetX_PutX_Home' N = [Lemma_3b' N, Lemma_1' N]"

lemma strengthenVsObsLs_lemmasFor_NI_Remote_GetX_PutX_Home : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Remote_GetX_PutX_Home N) (lemmasFor_NI_Remote_GetX_PutX_Home' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Remote_GetX_PutX_Home_def lemmasFor_NI_Remote_GetX_PutX_Home'_def  apply(auto intro: strengthenVsObsLemma_3b strengthenVsObsLemma_1     )    
 
done

lemma lemmaNI_Remote_GetX_PutX_Home_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Remote_GetX_PutX_Home_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Remote_GetX_PutX_Home_refs_def NI_Remote_GetX_PutX_Home_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Local_Put' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Local_Put' N = []"

lemma strengthenVsObsLs_lemmasFor_NI_Local_Put : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Local_Put N) (lemmasFor_NI_Local_Put' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Local_Put_def lemmasFor_NI_Local_Put'_def  apply(auto      )    
 
done

lemma lemmaNI_Local_Put_fitEnv [intro]: 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Local_Put_refs|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Local_Put_refs_def NI_Local_Put_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Remote_Put' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Remote_Put' N = []"

lemma strengthenVsObsLs_lemmasFor_NI_Remote_Put : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Remote_Put N) (lemmasFor_NI_Remote_Put' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Remote_Put_def lemmasFor_NI_Remote_Put'_def  apply(auto      )    
 
done

lemma lemmaNI_Remote_Put_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Remote_Put_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Remote_Put_refs_def NI_Remote_Put_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Local_PutXAcksDone' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Local_PutXAcksDone' N = []"

lemma strengthenVsObsLs_lemmasFor_NI_Local_PutXAcksDone : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Local_PutXAcksDone N) (lemmasFor_NI_Local_PutXAcksDone' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Local_PutXAcksDone_def lemmasFor_NI_Local_PutXAcksDone'_def  apply(auto      )    
 
done

lemma lemmaNI_Local_PutXAcksDone_fitEnv [intro]: 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Local_PutXAcksDone_refs|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Local_PutXAcksDone_refs_def NI_Local_PutXAcksDone_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Remote_PutX' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Remote_PutX' N = []"

lemma strengthenVsObsLs_lemmasFor_NI_Remote_PutX : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Remote_PutX N) (lemmasFor_NI_Remote_PutX' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Remote_PutX_def lemmasFor_NI_Remote_PutX'_def  apply(auto      )    
 
done

lemma lemmaNI_Remote_PutX_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Remote_PutX_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Remote_PutX_refs_def NI_Remote_PutX_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Inv' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Inv' N = []"

lemma strengthenVsObsLs_lemmasFor_NI_Inv : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Inv N) (lemmasFor_NI_Inv' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Inv_def lemmasFor_NI_Inv'_def  apply(auto      )    
 
done

lemma lemmaNI_Inv_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Inv_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Inv_refs_def NI_Inv_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_InvAck1' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_InvAck1' N = [Lemma_4' N]"

lemma strengthenVsObsLs_lemmasFor_NI_InvAck1 : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_InvAck1 N) (lemmasFor_NI_InvAck1' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_InvAck1_def lemmasFor_NI_InvAck1'_def  apply(auto intro: strengthenVsObsLemma_4     )    
 
done

lemma lemmaNI_InvAck1_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_InvAck1_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_InvAck1_refs_def NI_InvAck1_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_InvAck2' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_InvAck2' N = []"

lemma strengthenVsObsLs_lemmasFor_NI_InvAck2 : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_InvAck2 N) (lemmasFor_NI_InvAck2' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_InvAck2_def lemmasFor_NI_InvAck2'_def  apply(auto      )    
 
done

lemma lemmaNI_InvAck2_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_InvAck2_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_InvAck2_refs_def NI_InvAck2_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Wb' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Wb' N = []"

lemma strengthenVsObsLs_lemmasFor_NI_Wb : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Wb N) (lemmasFor_NI_Wb' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Wb_def lemmasFor_NI_Wb'_def  apply(auto      )    
 
done

lemma lemmaNI_Wb_fitEnv [intro]: 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Wb_refs|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Wb_refs_def NI_Wb_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_FAck' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_FAck' N = []"

lemma strengthenVsObsLs_lemmasFor_NI_FAck : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_FAck N) (lemmasFor_NI_FAck' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_FAck_def lemmasFor_NI_FAck'_def  apply(auto      )    
 
done

lemma lemmaNI_FAck_fitEnv [intro]: 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_FAck_refs|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_FAck_refs_def NI_FAck_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_ShWb' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_ShWb' N = []"

lemma strengthenVsObsLs_lemmasFor_NI_ShWb : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_ShWb N) (lemmasFor_NI_ShWb' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_ShWb_def lemmasFor_NI_ShWb'_def  apply(auto      )    
 
done

lemma lemmaNI_ShWb_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_ShWb_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_ShWb_refs_def NI_ShWb_ref_def  apply(auto      )    
 
done

definition lemmasFor_NI_Replace' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_NI_Replace' N = []"

lemma strengthenVsObsLs_lemmasFor_NI_Replace : 
                  " 
                  strengthenVsObsLs (lemmasFor_NI_Replace N) (lemmasFor_NI_Replace' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_NI_Replace_def lemmasFor_NI_Replace'_def  apply(auto      )    
 
done

lemma lemmaNI_Replace_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : NI_Replace_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding NI_Replace_refs_def NI_Replace_ref_def  apply(auto      )    
 
done

definition InvS' :: "nat \<Rightarrow> (((nat \<Rightarrow> nat \<Rightarrow> formula) list) list)" where
 "InvS' N = [lemmasFor_PI_Remote_Get' N, lemmasFor_PI_Local_Get_Get' N, lemmasFor_PI_Local_Get_Put' N, lemmasFor_PI_Remote_GetX' N, lemmasFor_PI_Local_GetX_GetX' N, lemmasFor_PI_Local_GetX_PutX' N, lemmasFor_PI_Remote_PutX' N, lemmasFor_PI_Local_PutX' N, lemmasFor_PI_Remote_Replace' N, lemmasFor_PI_Local_Replace' N, lemmasFor_NI_Nak' N, lemmasFor_NI_Nak_Home' N, lemmasFor_NI_Nak_Clear' N, lemmasFor_NI_Local_Get_Nak' N, lemmasFor_NI_Local_Get_Get' N, lemmasFor_NI_Local_Get_Put' N, lemmasFor_NI_Remote_Get_Nak' N, lemmasFor_NI_Remote_Get_Nak_Home' N, lemmasFor_NI_Remote_Get_Put' N, lemmasFor_NI_Remote_Get_Put_Home' N, lemmasFor_NI_Local_GetX_Nak' N, lemmasFor_NI_Local_GetX_GetX' N, lemmasFor_NI_Local_GetX_PutX1' N, lemmasFor_NI_Local_GetX_PutX2' N, lemmasFor_NI_Local_GetX_PutX3' N, lemmasFor_NI_Remote_GetX_Nak' N, lemmasFor_NI_Remote_GetX_Nak_Home' N, lemmasFor_NI_Remote_GetX_PutX' N, lemmasFor_NI_Remote_GetX_PutX_Home' N, lemmasFor_NI_Local_Put' N, lemmasFor_NI_Remote_Put' N, lemmasFor_NI_Local_PutXAcksDone' N, lemmasFor_NI_Remote_PutX' N, lemmasFor_NI_Inv' N, lemmasFor_NI_InvAck1' N, lemmasFor_NI_InvAck2' N, lemmasFor_NI_Wb' N, lemmasFor_NI_FAck' N, lemmasFor_NI_ShWb' N, lemmasFor_NI_Replace' N]"

lemma wellFormedRule_refs : 
                  "[|r : rule_refs N|] 
                 ==> wellFormedRule (env N) N r"
                   apply(auto     simp add: rule_refs_def   PI_Remote_Get_refs_def PI_Local_Get_Get_refs_def PI_Local_Get_Put_refs_def PI_Remote_GetX_refs_def PI_Local_GetX_GetX_refs_def PI_Local_GetX_PutX_refs_def PI_Remote_PutX_refs_def PI_Local_PutX_refs_def PI_Remote_Replace_refs_def PI_Local_Replace_refs_def NI_Nak_refs_def NI_Nak_Home_refs_def NI_Nak_Clear_refs_def NI_Local_Get_Nak_refs_def NI_Local_Get_Get_refs_def NI_Local_Get_Put_refs_def NI_Remote_Get_Nak_refs_def NI_Remote_Get_Nak_Home_refs_def NI_Remote_Get_Put_refs_def NI_Remote_Get_Put_Home_refs_def NI_Local_GetX_Nak_refs_def NI_Local_GetX_GetX_refs_def NI_Local_GetX_PutX1_refs_def NI_Local_GetX_PutX2_refs_def NI_Local_GetX_PutX3_refs_def NI_Remote_GetX_Nak_refs_def NI_Remote_GetX_Nak_Home_refs_def NI_Remote_GetX_PutX_refs_def NI_Remote_GetX_PutX_Home_refs_def NI_Local_Put_refs_def NI_Remote_Put_refs_def NI_Local_PutXAcksDone_refs_def NI_Remote_PutX_refs_def NI_Inv_refs_def NI_InvAck1_refs_def NI_InvAck2_refs_def NI_Wb_refs_def NI_FAck_refs_def NI_ShWb_refs_def NI_Replace_refs_def symPI_Remote_Get_ref symPI_Local_Get_Get_ref symPI_Local_Get_Put_ref symPI_Remote_GetX_ref symPI_Local_GetX_GetX_ref symPI_Local_GetX_PutX_ref symPI_Remote_PutX_ref symPI_Local_PutX_ref symPI_Remote_Replace_ref symPI_Local_Replace_ref symNI_Nak_ref symNI_Nak_Home_ref symNI_Nak_Clear_ref symNI_Local_Get_Nak_ref symNI_Local_Get_Get_ref symNI_Local_Get_Put_ref symNI_Remote_Get_Nak_ref symNI_Remote_Get_Nak_Home_ref symNI_Remote_Get_Put_ref symNI_Remote_Get_Put_Home_ref symNI_Local_GetX_Nak_ref symNI_Local_GetX_GetX_ref symNI_Local_GetX_PutX1_ref symNI_Local_GetX_PutX2_ref symNI_Local_GetX_PutX3_ref symNI_Remote_GetX_Nak_ref symNI_Remote_GetX_Nak_Home_ref symNI_Remote_GetX_PutX_ref symNI_Remote_GetX_PutX_Home_ref symNI_Local_Put_ref symNI_Remote_Put_ref symNI_Local_PutXAcksDone_ref symNI_Remote_PutX_ref symNI_Inv_ref symNI_InvAck1_ref symNI_InvAck2_ref symNI_Wb_ref symNI_FAck_ref symNI_ShWb_ref symNI_Replace_ref )    
 
done

lemma SafeAndderiveAll : 
                  "[|M < N;M = 1;l <= M;k <= M;pinvL : set (InvS' N);pf : set pinvL|] 
                 ==> safeForm (env N) M (pf k l) & deriveForm (env N) (pf k l)"
                 unfolding InvS'_def lemmasFor_PI_Remote_Get'_def lemmasFor_PI_Local_Get_Get'_def lemmasFor_PI_Local_Get_Put'_def lemmasFor_PI_Remote_GetX'_def lemmasFor_PI_Local_GetX_GetX'_def lemmasFor_PI_Local_GetX_PutX'_def lemmasFor_PI_Remote_PutX'_def lemmasFor_PI_Local_PutX'_def lemmasFor_PI_Remote_Replace'_def lemmasFor_PI_Local_Replace'_def lemmasFor_NI_Nak'_def lemmasFor_NI_Nak_Home'_def lemmasFor_NI_Nak_Clear'_def lemmasFor_NI_Local_Get_Nak'_def lemmasFor_NI_Local_Get_Get'_def lemmasFor_NI_Local_Get_Put'_def lemmasFor_NI_Remote_Get_Nak'_def lemmasFor_NI_Remote_Get_Nak_Home'_def lemmasFor_NI_Remote_Get_Put'_def lemmasFor_NI_Remote_Get_Put_Home'_def lemmasFor_NI_Local_GetX_Nak'_def lemmasFor_NI_Local_GetX_GetX'_def lemmasFor_NI_Local_GetX_PutX1'_def lemmasFor_NI_Local_GetX_PutX2'_def lemmasFor_NI_Local_GetX_PutX3'_def lemmasFor_NI_Remote_GetX_Nak'_def lemmasFor_NI_Remote_GetX_Nak_Home'_def lemmasFor_NI_Remote_GetX_PutX'_def lemmasFor_NI_Remote_GetX_PutX_Home'_def lemmasFor_NI_Local_Put'_def lemmasFor_NI_Remote_Put'_def lemmasFor_NI_Local_PutXAcksDone'_def lemmasFor_NI_Remote_PutX'_def lemmasFor_NI_Inv'_def lemmasFor_NI_InvAck1'_def lemmasFor_NI_InvAck2'_def lemmasFor_NI_Wb'_def lemmasFor_NI_FAck'_def lemmasFor_NI_ShWb'_def lemmasFor_NI_Replace'_def using SafeAndderiveFormLemma_1' SafeAndderiveFormLemma_2a' SafeAndderiveFormLemma_2b' SafeAndderiveFormLemma_3a' SafeAndderiveFormLemma_3b' SafeAndderiveFormLemma_4' apply(auto      )    
 
done

lemma rulesIsSym : 
                  " 
                  symProtRules' N (rules N)"
                 unfolding rules_def   apply(rule symProtRulesUnion, blast intro:symProtAll)+
unfolding rules_def  apply(blast intro: symProtAll     )

done

lemma rule_refsIsSym : 
                  " 
                  symProtRules' N (rule_refs N)"
                 unfolding rule_refs_def   apply(rule symProtRulesUnion, blast intro:symProtAllRef)+
unfolding rule_refs_def  apply(blast intro: symProtAllRef     )

done

lemma rule_refsWellTyped : 
                  "[|r : rule_refs N|] 
                 ==> deriveRule (env N) r"
                 unfolding rule_refs_def using deriveAllRef apply(auto      )    
 
done

lemma ReachStafitEnv : 
                  "[|reachableUpTo (allInitSpecs N) (rule_refs N) k s|] 
                 ==> fitEnv s (env N)"
                   apply(erule invIntro1)
subgoal for s0
  unfolding fitEnv_def   apply(rule allI)
     apply(rule impI)
  apply(case_tac   "v")
  
  subgoal for v x1
    apply(case_tac   "x1 = ''Sta.Dir.Pending''")
    
    apply(subgoal_tac   "formEval (initSpec0) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x1 = ''Sta.Dir.Local''")
    
    apply(subgoal_tac   "formEval (initSpec1) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x1 = ''Sta.Dir.Dirty''")
    
    apply(subgoal_tac   "formEval (initSpec2) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x1 = ''Sta.Dir.HeadVld''")
    
    apply(subgoal_tac   "formEval (initSpec3) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x1 = ''Sta.Dir.ShrVld''")
    
    apply(subgoal_tac   "formEval (initSpec4) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x1 = ''Sta.Dir.HeadPtr''")
    
    apply(subgoal_tac   "formEval (initSpec5 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x1 = ''Sta.WbMsg.Cmd''")
    
    apply(subgoal_tac   "formEval (initSpec6) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x1 = ''Sta.WbMsg.Proc''")
    
    apply(subgoal_tac   "formEval (initSpec7 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x1 = ''Sta.ShWbMsg.Cmd''")
    
    apply(subgoal_tac   "formEval (initSpec8) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x1 = ''Sta.ShWbMsg.Proc''")
    
    apply(subgoal_tac   "formEval (initSpec9 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x1 = ''Sta.NakcMsg.Cmd''")
    
    apply(subgoal_tac   "formEval (initSpec10) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x1 = ''Sta.HomeProc.ProcCmd''")
    
    apply(subgoal_tac   "formEval (initSpec21) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x1 = ''Sta.HomeProc.InvMarked''")
    
    apply(subgoal_tac   "formEval (initSpec22) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x1 = ''Sta.HomeProc.CacheState''")
    
    apply(subgoal_tac   "formEval (initSpec23) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x1 = ''Sta.HomeUniMsg.Cmd''")
    
    apply(subgoal_tac   "formEval (initSpec24) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x1 = ''Sta.HomeUniMsg.HomeProc''")
    
    apply(subgoal_tac   "formEval (initSpec25) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x1 = ''Sta.HomeUniMsg.Proc''")
    
    apply(subgoal_tac   "formEval (initSpec26 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x1 = ''Sta.HomePendReqSrc''")
    
    apply(subgoal_tac   "formEval (initSpec27) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x1 = ''Sta.Collecting''")
    
    apply(subgoal_tac   "formEval (initSpec28) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x1 = ''Sta.FwdCmd''")
    
    apply(subgoal_tac   "formEval (initSpec29) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x1 = ''Sta.PendReqSrc''")
    
    apply(subgoal_tac   "formEval (initSpec30 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
      apply(auto      )    
     done
  
  subgoal for v x21 x22
    apply(case_tac   "x21 = ''Sta.Proc.ProcCmd''")
    
    apply(subgoal_tac   "formEval (initSpec11 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x21 = ''Sta.Proc.InvMarked''")
    
    apply(subgoal_tac   "formEval (initSpec12 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x21 = ''Sta.Proc.CacheState''")
    
    apply(subgoal_tac   "formEval (initSpec13 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x21 = ''Sta.Dir.ShrSet''")
    
    apply(subgoal_tac   "formEval (initSpec14 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x21 = ''Sta.Dir.InvSet''")
    
    apply(subgoal_tac   "formEval (initSpec15 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x21 = ''Sta.InvMsg.Cmd''")
    
    apply(subgoal_tac   "formEval (initSpec16 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x21 = ''Sta.RpMsg.Cmd''")
    
    apply(subgoal_tac   "formEval (initSpec17 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x21 = ''Sta.UniMsg.Cmd''")
    
    apply(subgoal_tac   "formEval (initSpec18 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x21 = ''Sta.UniMsg.HomeProc''")
    
    apply(subgoal_tac   "formEval (initSpec19 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x21 = ''Sta.UniMsg.Proc''")
    
    apply(subgoal_tac   "formEval (initSpec20 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
      apply(auto      )    
     done
  
    apply(auto      )    
   done

subgoal for r sk
  unfolding rule_refs_def  apply(auto intro: Un_iff lemmaPI_Remote_Get_fitEnv lemmaPI_Local_Get_Get_fitEnv lemmaPI_Local_Get_Put_fitEnv lemmaPI_Remote_GetX_fitEnv lemmaPI_Local_GetX_GetX_fitEnv lemmaPI_Local_GetX_PutX_fitEnv lemmaPI_Remote_PutX_fitEnv lemmaPI_Local_PutX_fitEnv lemmaPI_Remote_Replace_fitEnv lemmaPI_Local_Replace_fitEnv lemmaNI_Nak_fitEnv lemmaNI_Nak_Home_fitEnv lemmaNI_Nak_Clear_fitEnv lemmaNI_Local_Get_Nak_fitEnv lemmaNI_Local_Get_Get_fitEnv lemmaNI_Local_Get_Put_fitEnv lemmaNI_Remote_Get_Nak_fitEnv lemmaNI_Remote_Get_Nak_Home_fitEnv lemmaNI_Remote_Get_Put_fitEnv lemmaNI_Remote_Get_Put_Home_fitEnv lemmaNI_Local_GetX_Nak_fitEnv lemmaNI_Local_GetX_GetX_fitEnv lemmaNI_Local_GetX_PutX1_fitEnv lemmaNI_Local_GetX_PutX2_fitEnv lemmaNI_Local_GetX_PutX3_fitEnv lemmaNI_Remote_GetX_Nak_fitEnv lemmaNI_Remote_GetX_Nak_Home_fitEnv lemmaNI_Remote_GetX_PutX_fitEnv lemmaNI_Remote_GetX_PutX_Home_fitEnv lemmaNI_Local_Put_fitEnv lemmaNI_Remote_Put_fitEnv lemmaNI_Local_PutXAcksDone_fitEnv lemmaNI_Remote_PutX_fitEnv lemmaNI_Inv_fitEnv lemmaNI_InvAck1_fitEnv lemmaNI_InvAck2_fitEnv lemmaNI_Wb_fitEnv lemmaNI_FAck_fitEnv lemmaNI_ShWb_fitEnv lemmaNI_Replace_fitEnv     )    
   done

done

lemma absProtSim : 
                  "[|M < N;M = 1;isProtObsInvSet (ABS_rules M) (absTransfForm (env N) M ` allInitSpecs N) (set (InvS' N)) M (env N)|] 
                 ==> isParamProtInvSet (rules N) (allInitSpecs N) (set (InvS N)) N"
                   apply(rule_tac ?rs2.0 = "rule_refs N" and env="env N" and S="set (InvS N)" and S'="set (InvS' N)" and M=M and absRules="ABS_rules M" in CMP)
subgoal for r
   using wellFormedRule_refs apply(auto      )    
   done

subgoal  unfolding InvS'_def lemmasFor_PI_Remote_Get'_def lemmasFor_PI_Local_Get_Get'_def lemmasFor_PI_Local_Get_Put'_def lemmasFor_PI_Remote_GetX'_def lemmasFor_PI_Local_GetX_GetX'_def lemmasFor_PI_Local_GetX_PutX'_def lemmasFor_PI_Remote_PutX'_def lemmasFor_PI_Local_PutX'_def lemmasFor_PI_Remote_Replace'_def lemmasFor_PI_Local_Replace'_def lemmasFor_NI_Nak'_def lemmasFor_NI_Nak_Home'_def lemmasFor_NI_Nak_Clear'_def lemmasFor_NI_Local_Get_Nak'_def lemmasFor_NI_Local_Get_Get'_def lemmasFor_NI_Local_Get_Put'_def lemmasFor_NI_Remote_Get_Nak'_def lemmasFor_NI_Remote_Get_Nak_Home'_def lemmasFor_NI_Remote_Get_Put'_def lemmasFor_NI_Remote_Get_Put_Home'_def lemmasFor_NI_Local_GetX_Nak'_def lemmasFor_NI_Local_GetX_GetX'_def lemmasFor_NI_Local_GetX_PutX1'_def lemmasFor_NI_Local_GetX_PutX2'_def lemmasFor_NI_Local_GetX_PutX3'_def lemmasFor_NI_Remote_GetX_Nak'_def lemmasFor_NI_Remote_GetX_Nak_Home'_def lemmasFor_NI_Remote_GetX_PutX'_def lemmasFor_NI_Remote_GetX_PutX_Home'_def lemmasFor_NI_Local_Put'_def lemmasFor_NI_Remote_Put'_def lemmasFor_NI_Local_PutXAcksDone'_def lemmasFor_NI_Remote_PutX'_def lemmasFor_NI_Inv'_def lemmasFor_NI_InvAck1'_def lemmasFor_NI_InvAck2'_def lemmasFor_NI_Wb'_def lemmasFor_NI_FAck'_def lemmasFor_NI_ShWb'_def lemmasFor_NI_Replace'_def using symInvs apply(auto      )    
   done

subgoal   using rulesIsSym apply(auto      )    
   done

subgoal   using symPreds apply(auto      )    
   done

subgoal    apply(auto      )    
   done

subgoal    apply(auto      )    
   done

subgoal   using SafeAndderiveAll apply(auto      )    
   done

subgoal   using StrengthRelRules2Rule_refs apply(auto      )    
   done

subgoal   using rule_refsIsSym apply(auto      )    
   done

subgoal   using rule_refsWellTyped apply(auto      )    
   done

subgoal    apply(auto      )    
   done

subgoal   using ReachStafitEnv apply(auto      )    
   done

subgoal  unfolding InvS_def InvS'_def  apply(auto      )    
   
  subgoal   using strengthenVsObsLs_lemmasFor_PI_Remote_Get apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_PI_Local_Get_Get apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_PI_Local_Get_Put apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_PI_Remote_GetX apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_PI_Local_GetX_GetX apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_PI_Local_GetX_PutX apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_PI_Remote_PutX apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_PI_Local_PutX apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_PI_Remote_Replace apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_PI_Local_Replace apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Nak apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Nak_Home apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Nak_Clear apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Local_Get_Nak apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Local_Get_Get apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Local_Get_Put apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Remote_Get_Nak apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Remote_Get_Nak_Home apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Remote_Get_Put apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Remote_Get_Put_Home apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Local_GetX_Nak apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Local_GetX_GetX apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Local_GetX_PutX1 apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Local_GetX_PutX2 apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Local_GetX_PutX3 apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Remote_GetX_Nak apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Remote_GetX_Nak_Home apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Remote_GetX_PutX apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Remote_GetX_PutX_Home apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Local_Put apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Remote_Put apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Local_PutXAcksDone apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Remote_PutX apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Inv apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_InvAck1 apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_InvAck2 apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Wb apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_FAck apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_ShWb apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_NI_Replace apply(auto      )    
     done
  done

   apply(rule equivRuleSetReflex)
 using ABS_all  apply(auto      )    
 
done

end
