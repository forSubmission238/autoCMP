
theory german
  imports ECMP
begin

definition I :: "scalrValueType" where [simp]:
 "I \<equiv> enum ''CACHE_STATE'' ''I''"

definition S :: "scalrValueType" where [simp]:
 "S \<equiv> enum ''CACHE_STATE'' ''S''"

definition E :: "scalrValueType" where [simp]:
 "E \<equiv> enum ''CACHE_STATE'' ''E''"

definition Empty :: "scalrValueType" where [simp]:
 "Empty \<equiv> enum ''MSG_CMD'' ''Empty''"

definition ReqS :: "scalrValueType" where [simp]:
 "ReqS \<equiv> enum ''MSG_CMD'' ''ReqS''"

definition ReqE :: "scalrValueType" where [simp]:
 "ReqE \<equiv> enum ''MSG_CMD'' ''ReqE''"

definition Inv :: "scalrValueType" where [simp]:
 "Inv \<equiv> enum ''MSG_CMD'' ''Inv''"

definition InvAck :: "scalrValueType" where [simp]:
 "InvAck \<equiv> enum ''MSG_CMD'' ''InvAck''"

definition GntS :: "scalrValueType" where [simp]:
 "GntS \<equiv> enum ''MSG_CMD'' ''GntS''"

definition GntE :: "scalrValueType" where [simp]:
 "GntE \<equiv> enum ''MSG_CMD'' ''GntE''"

definition true :: "scalrValueType" where [simp]:
 "true \<equiv> boolV True"

definition false :: "scalrValueType" where [simp]:
 "false \<equiv> boolV False"

primrec env :: "nat => envType" where
"env N (Ident n) = (if Ident n = Ident ''ExGntd'' then
  boolType
else
  if Ident n = Ident ''CurCmd'' then
    enumType
  else
    if Ident n = Ident ''CurPtr'' then
      indexType
    else
      anyType
    
  
)"|
"env N (Para n i) = (if Para n i = Para ''Chan1.Cmd'' i \<and> (i \<le> N) then
  enumType
else
  if Para n i = Para ''Chan2.Cmd'' i \<and> (i \<le> N) then
    enumType
  else
    if Para n i = Para ''Chan3.Cmd'' i \<and> (i \<le> N) then
      enumType
    else
      if Para n i = Para ''Cache.State'' i \<and> (i \<le> N) then
        enumType
      else
        if Para n i = Para ''InvSet'' i \<and> (i \<le> N) then
          boolType
        else
          if Para n i = Para ''ShrSet'' i \<and> (i \<le> N) then
            boolType
          else
            anyType
          
        
      
    
  
)"|
"env N dontCareVar = anyType"

lemma env_simp : 
             "[|i <= N|] 
                 ==> env N (Para ''Chan1.Cmd'' i) = enumType"
                 

"[|i <= N|] 
                 ==> env N (Para ''Chan2.Cmd'' i) = enumType"
                 

"[|i <= N|] 
                 ==> env N (Para ''Chan3.Cmd'' i) = enumType"
                 

"[|i <= N|] 
                 ==> env N (Para ''Cache.State'' i) = enumType"
                 

"[|i <= N|] 
                 ==> env N (Para ''InvSet'' i) = boolType"
                 

"[|i <= N|] 
                 ==> env N (Para ''ShrSet'' i) = boolType"
                 

" 
                  env N (Ident ''ExGntd'') = boolType"
                 

" 
                  env N (Ident ''CurCmd'') = enumType"
                 

" 
                  env N (Ident ''CurPtr'') = indexType"
                 

"[|i > N|] 
                 ==> env N (Para n i) = anyType"
                 
 
               apply(auto      )    
 
done

definition initSpec0 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec0 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const Empty) N"

lemma symPreds0 [intro]: 
                  " 
                  symPredSet' N {initSpec0 N}"
                 unfolding initSpec0_def   apply(rule symPredSetForall)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma deriveFormInitSpec0 [intro]: 
                  "[|f : {initSpec0 N}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec1 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec1 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Empty) N"

lemma symPreds1 [intro]: 
                  " 
                  symPredSet' N {initSpec1 N}"
                 unfolding initSpec1_def   apply(rule symPredSetForall)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma deriveFormInitSpec1 [intro]: 
                  "[|f : {initSpec1 N}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec2 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec2 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const Empty) N"

lemma symPreds2 [intro]: 
                  " 
                  symPredSet' N {initSpec2 N}"
                 unfolding initSpec2_def   apply(rule symPredSetForall)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma deriveFormInitSpec2 [intro]: 
                  "[|f : {initSpec2 N}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec3 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec3 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''Cache.State'' i) =\<^sub>f Const I) N"

lemma symPreds3 [intro]: 
                  " 
                  symPredSet' N {initSpec3 N}"
                 unfolding initSpec3_def   apply(rule symPredSetForall)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma deriveFormInitSpec3 [intro]: 
                  "[|f : {initSpec3 N}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec4 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec4 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''InvSet'' i) =\<^sub>f Const false) N"

lemma symPreds4 [intro]: 
                  " 
                  symPredSet' N {initSpec4 N}"
                 unfolding initSpec4_def   apply(rule symPredSetForall)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma deriveFormInitSpec4 [intro]: 
                  "[|f : {initSpec4 N}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec5 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec5 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''ShrSet'' i) =\<^sub>f Const false) N"

lemma symPreds5 [intro]: 
                  " 
                  symPredSet' N {initSpec5 N}"
                 unfolding initSpec5_def   apply(rule symPredSetForall)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma deriveFormInitSpec5 [intro]: 
                  "[|f : {initSpec5 N}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec6 :: "formula" where [simp]:
 "initSpec6 \<equiv> IVar (Ident ''ExGntd'') =\<^sub>f Const false"

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

definition initSpec7 :: "formula" where [simp]:
 "initSpec7 \<equiv> IVar (Ident ''CurCmd'') =\<^sub>f Const Empty"

lemma symPreds7 [intro]: 
                  " 
                  symPredSet' N {initSpec7}"
                   apply(auto      )    
 
done

lemma deriveFormInitSpec7 [intro]: 
                  "[|f : {initSpec7}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition initSpec8 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec8 N \<equiv> (\<exists>\<^sub>fi_0. IVar (Ident ''CurPtr'') =\<^sub>f Const (index i_0)) N"

lemma symPreds8 [intro]: 
                  " 
                  symPredSet' N {initSpec8 N}"
                 unfolding initSpec8_def   apply(rule symPredSetExist)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma deriveFormInitSpec8 [intro]: 
                  "[|f : {initSpec8 N}|] 
                 ==> deriveForm (env N) f"
                   apply(auto      )    
 
done

definition allInitSpecs :: "nat \<Rightarrow> formula set" where [simp]:
 "allInitSpecs N \<equiv> {initSpec0 N} \<union> ({initSpec1 N} \<union> ({initSpec2 N} \<union> ({initSpec3 N} \<union> ({initSpec4 N} \<union> ({initSpec5 N} \<union> ({initSpec6} \<union> ({initSpec7} \<union> {initSpec8 N})))))))"

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

  apply(blast      )

done

lemma deriveFormAllInitSpec : 
                  "[|f : allInitSpecs N|] 
                 ==> deriveForm (env N) f"
                  using deriveFormInitSpec0 deriveFormInitSpec1 deriveFormInitSpec2 deriveFormInitSpec3 deriveFormInitSpec4 deriveFormInitSpec5 deriveFormInitSpec6 deriveFormInitSpec7 deriveFormInitSpec8 apply(auto      simp del: initSpec0_def initSpec1_def initSpec2_def initSpec3_def initSpec4_def initSpec5_def initSpec6_def initSpec7_def initSpec8_def)    
 
done

definition RecvGntE :: "nat \<Rightarrow> rule" where
 "RecvGntE i \<equiv> 
   IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const GntE
  \<triangleright>
   assign (Para ''Cache.State'' i, Const E) ||
   assign (Para ''Chan2.Cmd'' i, Const Empty)"

lemma symRecvGntE : 
             " 
                  symParamRule N RecvGntE"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (RecvGntE i)"
                 
 
             unfolding RecvGntE_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition RecvGntEs :: "nat \<Rightarrow> rule set" where
 "RecvGntEs N \<equiv> oneParamCons N RecvGntE"

definition RecvGntS :: "nat \<Rightarrow> rule" where
 "RecvGntS i \<equiv> 
   IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const GntS
  \<triangleright>
   assign (Para ''Cache.State'' i, Const S) ||
   assign (Para ''Chan2.Cmd'' i, Const Empty)"

lemma symRecvGntS : 
             " 
                  symParamRule N RecvGntS"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (RecvGntS i)"
                 
 
             unfolding RecvGntS_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition RecvGntSs :: "nat \<Rightarrow> rule set" where
 "RecvGntSs N \<equiv> oneParamCons N RecvGntS"

definition SendGntE :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "SendGntE N i \<equiv> 
   IVar (Ident ''CurCmd'') =\<^sub>f Const ReqE \<and>\<^sub>f
   IVar (Ident ''CurPtr'') =\<^sub>f Const (index i) \<and>\<^sub>f
   IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
   IVar (Ident ''ExGntd'') =\<^sub>f Const false \<and>\<^sub>f
   (\<forall>\<^sub>fj. IVar (Para ''ShrSet'' j) =\<^sub>f Const false) N
  \<triangleright>
   assign (Para ''Chan2.Cmd'' i, Const GntE) ||
   assign (Para ''ShrSet'' i, Const true) ||
   assign (Ident ''ExGntd'', Const true) ||
   assign (Ident ''CurCmd'', Const Empty)"

lemma symSendGntE : 
             " 
                  symParamRule N (SendGntE N)"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (SendGntE N i)"
                 
 
             unfolding SendGntE_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition SendGntEs :: "nat \<Rightarrow> rule set" where
 "SendGntEs N \<equiv> oneParamCons N (SendGntE N)"

definition SendGntS :: "nat \<Rightarrow> rule" where
 "SendGntS i \<equiv> 
   IVar (Ident ''CurCmd'') =\<^sub>f Const ReqS \<and>\<^sub>f
   IVar (Ident ''CurPtr'') =\<^sub>f Const (index i) \<and>\<^sub>f
   IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
   IVar (Ident ''ExGntd'') =\<^sub>f Const false
  \<triangleright>
   assign (Para ''Chan2.Cmd'' i, Const GntS) ||
   assign (Para ''ShrSet'' i, Const true) ||
   assign (Ident ''CurCmd'', Const Empty)"

lemma symSendGntS : 
             " 
                  symParamRule N SendGntS"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (SendGntS i)"
                 
 
             unfolding SendGntS_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition SendGntSs :: "nat \<Rightarrow> rule set" where
 "SendGntSs N \<equiv> oneParamCons N SendGntS"

definition RecvInvAck1 :: "nat \<Rightarrow> rule" where
 "RecvInvAck1 i \<equiv> 
   IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const InvAck \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
   IVar (Ident ''ExGntd'') =\<^sub>f Const true
  \<triangleright>
   assign (Para ''Chan3.Cmd'' i, Const Empty) ||
   assign (Para ''ShrSet'' i, Const false) ||
   assign (Ident ''ExGntd'', Const false)"

lemma symRecvInvAck1 : 
             " 
                  symParamRule N RecvInvAck1"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (RecvInvAck1 i)"
                 
 
             unfolding RecvInvAck1_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition RecvInvAck1s :: "nat \<Rightarrow> rule set" where
 "RecvInvAck1s N \<equiv> oneParamCons N RecvInvAck1"

definition RecvInvAck2 :: "nat \<Rightarrow> rule" where
 "RecvInvAck2 i \<equiv> 
   IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const InvAck \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
   IVar (Ident ''ExGntd'') =\<^sub>f Const false
  \<triangleright>
   assign (Para ''Chan3.Cmd'' i, Const Empty) ||
   assign (Para ''ShrSet'' i, Const false)"

lemma symRecvInvAck2 : 
             " 
                  symParamRule N RecvInvAck2"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (RecvInvAck2 i)"
                 
 
             unfolding RecvInvAck2_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition RecvInvAck2s :: "nat \<Rightarrow> rule set" where
 "RecvInvAck2s N \<equiv> oneParamCons N RecvInvAck2"

definition SendInvAck :: "nat \<Rightarrow> rule" where
 "SendInvAck i \<equiv> 
   IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Inv \<and>\<^sub>f
   IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const Empty
  \<triangleright>
   assign (Para ''Chan2.Cmd'' i, Const Empty) ||
   assign (Para ''Chan3.Cmd'' i, Const InvAck) ||
   assign (Para ''Cache.State'' i, Const I)"

lemma symSendInvAck : 
             " 
                  symParamRule N SendInvAck"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (SendInvAck i)"
                 
 
             unfolding SendInvAck_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition SendInvAcks :: "nat \<Rightarrow> rule set" where
 "SendInvAcks N \<equiv> oneParamCons N SendInvAck"

definition SendInv :: "nat \<Rightarrow> rule" where
 "SendInv i \<equiv> 
   IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
   IVar (Para ''InvSet'' i) =\<^sub>f Const true \<and>\<^sub>f
   (IVar (Ident ''CurCmd'') =\<^sub>f Const ReqE \<or>\<^sub>f
   IVar (Ident ''CurCmd'') =\<^sub>f Const ReqS \<and>\<^sub>f
   IVar (Ident ''ExGntd'') =\<^sub>f Const true)
  \<triangleright>
   assign (Para ''Chan2.Cmd'' i, Const Inv) ||
   assign (Para ''InvSet'' i, Const false)"

lemma symSendInv : 
             " 
                  symParamRule N SendInv"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (SendInv i)"
                 
 
             unfolding SendInv_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition SendInvs :: "nat \<Rightarrow> rule set" where
 "SendInvs N \<equiv> oneParamCons N SendInv"

definition RecvReqE :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "RecvReqE N i \<equiv> 
   IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
   IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const ReqE
  \<triangleright>
   assign (Ident ''CurCmd'', Const ReqE) ||
   assign (Ident ''CurPtr'', Const (index i)) ||
   assign (Para ''Chan1.Cmd'' i, Const Empty) ||
   forallStm (\<lambda>j. assign (Para ''InvSet'' j, IVar (Para ''ShrSet'' j))) N"

lemma symRecvReqE : 
             " 
                  symParamRule N (RecvReqE N)"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (RecvReqE N i)"
                 
 
             unfolding RecvReqE_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition RecvReqEs :: "nat \<Rightarrow> rule set" where
 "RecvReqEs N \<equiv> oneParamCons N (RecvReqE N)"

definition RecvReqS :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "RecvReqS N i \<equiv> 
   IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
   IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const ReqS
  \<triangleright>
   assign (Ident ''CurCmd'', Const ReqS) ||
   assign (Ident ''CurPtr'', Const (index i)) ||
   assign (Para ''Chan1.Cmd'' i, Const Empty) ||
   forallStm (\<lambda>j. assign (Para ''InvSet'' j, IVar (Para ''ShrSet'' j))) N"

lemma symRecvReqS : 
             " 
                  symParamRule N (RecvReqS N)"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (RecvReqS N i)"
                 
 
             unfolding RecvReqS_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition RecvReqSs :: "nat \<Rightarrow> rule set" where
 "RecvReqSs N \<equiv> oneParamCons N (RecvReqS N)"

definition SendReqE :: "nat \<Rightarrow> rule" where
 "SendReqE i \<equiv> 
   IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
   (IVar (Para ''Cache.State'' i) =\<^sub>f Const I \<or>\<^sub>f
   IVar (Para ''Cache.State'' i) =\<^sub>f Const S)
  \<triangleright>
   assign (Para ''Chan1.Cmd'' i, Const ReqE)"

lemma symSendReqE : 
             " 
                  symParamRule N SendReqE"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (SendReqE i)"
                 
 
             unfolding SendReqE_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition SendReqEs :: "nat \<Rightarrow> rule set" where
 "SendReqEs N \<equiv> oneParamCons N SendReqE"

definition SendReqS :: "nat \<Rightarrow> rule" where
 "SendReqS i \<equiv> 
   IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
   IVar (Para ''Cache.State'' i) =\<^sub>f Const I
  \<triangleright>
   assign (Para ''Chan1.Cmd'' i, Const ReqS)"

lemma symSendReqS : 
             " 
                  symParamRule N SendReqS"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (SendReqS i)"
                 
 
             unfolding SendReqS_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition SendReqSs :: "nat \<Rightarrow> rule set" where
 "SendReqSs N \<equiv> oneParamCons N SendReqS"

definition CntrlProp :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "CntrlProp N i j \<equiv> \<not>\<^sub>f Const (index i) =\<^sub>f Const (index j) \<longrightarrow>\<^sub>f
  (IVar (Para ''Cache.State'' i) =\<^sub>f Const E \<longrightarrow>\<^sub>f
  IVar (Para ''Cache.State'' j) =\<^sub>f Const I) \<and>\<^sub>f
  (IVar (Para ''Cache.State'' i) =\<^sub>f Const S \<longrightarrow>\<^sub>f
  IVar (Para ''Cache.State'' j) =\<^sub>f Const I \<or>\<^sub>f
  IVar (Para ''Cache.State'' j) =\<^sub>f Const S)"

definition ABS_SendGntE :: "nat \<Rightarrow> rule" where
 "ABS_SendGntE N \<equiv> 
   IVar (Ident ''CurCmd'') =\<^sub>f Const ReqE \<and>\<^sub>f
   IVar (Ident ''CurPtr'') =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   IVar (Ident ''ExGntd'') =\<^sub>f Const false \<and>\<^sub>f
   (\<forall>\<^sub>fj. IVar (Para ''ShrSet'' j) =\<^sub>f Const false) N
  \<triangleright>
   assign (Ident ''ExGntd'', Const true) ||
   assign (Ident ''CurCmd'', Const Empty)"

definition ABS_SendGntEs :: "nat \<Rightarrow> rule set" where
 "ABS_SendGntEs N \<equiv> {ABS_SendGntE N}"

definition ABS_SendGntS :: "nat \<Rightarrow> rule" where
 "ABS_SendGntS N \<equiv> 
   IVar (Ident ''CurCmd'') =\<^sub>f Const ReqS \<and>\<^sub>f
   IVar (Ident ''CurPtr'') =\<^sub>f Const (index (N + 1)) \<and>\<^sub>f
   IVar (Ident ''ExGntd'') =\<^sub>f Const false
  \<triangleright>
   assign (Ident ''CurCmd'', Const Empty)"

definition ABS_SendGntSs :: "nat \<Rightarrow> rule set" where
 "ABS_SendGntSs N \<equiv> {ABS_SendGntS N}"

definition ABS_RecvReqE :: "nat \<Rightarrow> rule" where
 "ABS_RecvReqE N \<equiv> 
   IVar (Ident ''CurCmd'') =\<^sub>f Const Empty
  \<triangleright>
   assign (Ident ''CurCmd'', Const ReqE) ||
   assign (Ident ''CurPtr'', Const (index (N + 1))) ||
   forallStm (\<lambda>j. assign (Para ''InvSet'' j, IVar (Para ''ShrSet'' j))) N"

definition ABS_RecvReqEs :: "nat \<Rightarrow> rule set" where
 "ABS_RecvReqEs N \<equiv> {ABS_RecvReqE N}"

definition ABS_RecvReqS :: "nat \<Rightarrow> rule" where
 "ABS_RecvReqS N \<equiv> 
   IVar (Ident ''CurCmd'') =\<^sub>f Const Empty
  \<triangleright>
   assign (Ident ''CurCmd'', Const ReqS) ||
   assign (Ident ''CurPtr'', Const (index (N + 1))) ||
   forallStm (\<lambda>j. assign (Para ''InvSet'' j, IVar (Para ''ShrSet'' j))) N"

definition ABS_RecvReqSs :: "nat \<Rightarrow> rule set" where
 "ABS_RecvReqSs N \<equiv> {ABS_RecvReqS N}"

definition ABS_RecvInvAck1 :: "nat \<Rightarrow> rule" where
 "ABS_RecvInvAck1 N \<equiv> 
   \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
   IVar (Ident ''ExGntd'') =\<^sub>f Const true \<and>\<^sub>f
   (\<forall>\<^sub>fj. \<not>\<^sub>f IVar (Para ''Cache.State'' j) =\<^sub>f Const E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Chan2.Cmd'' j) =\<^sub>f Const GntE \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Chan3.Cmd'' j) =\<^sub>f Const InvAck) N
  \<triangleright>
   assign (Ident ''ExGntd'', Const false)"

definition ABS_RecvInvAck1s :: "nat \<Rightarrow> rule set" where
 "ABS_RecvInvAck1s N \<equiv> {ABS_RecvInvAck1 N}"

definition Lemma_1 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_1 N p i \<equiv> IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const InvAck \<and>\<^sub>f
  \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
  IVar (Ident ''ExGntd'') =\<^sub>f Const true \<longrightarrow>\<^sub>f
  forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''Cache.State'' j) =\<^sub>f Const E \<and>\<^sub>f
  \<not>\<^sub>f IVar (Para ''Chan2.Cmd'' j) =\<^sub>f Const GntE \<and>\<^sub>f
  \<not>\<^sub>f IVar (Para ''Chan3.Cmd'' j) =\<^sub>f Const InvAck) i N"

definition rules :: "nat \<Rightarrow> rule set" where
 "rules N = (RecvGntEs N \<union> (RecvGntSs N \<union> (SendGntEs N \<union> (SendGntSs N \<union> (RecvInvAck1s N \<union> (RecvInvAck2s N \<union> (SendInvAcks N \<union> (SendInvs N \<union> (RecvReqEs N \<union> (RecvReqSs N \<union> (SendReqEs N \<union> SendReqSs N)))))))))))"

lemma deriveAll : 
             "[|r : RecvGntEs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : RecvGntSs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : SendGntEs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : SendGntSs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : RecvInvAck1s N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : RecvInvAck2s N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : SendInvAcks N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : SendInvs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : RecvReqEs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : RecvReqSs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : SendReqEs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : SendReqSs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_SendGntEs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_SendGntSs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_RecvReqEs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_RecvReqSs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_RecvInvAck1s N|] 
                 ==> deriveRule (env N) r"
                 
 
             unfolding deriveRule_def deriveForm_def deriveStmt_def RecvGntEs_def RecvGntE_def RecvGntSs_def RecvGntS_def SendGntEs_def SendGntE_def SendGntSs_def SendGntS_def RecvInvAck1s_def RecvInvAck1_def RecvInvAck2s_def RecvInvAck2_def SendInvAcks_def SendInvAck_def SendInvs_def SendInv_def RecvReqEs_def RecvReqE_def RecvReqSs_def RecvReqS_def SendReqEs_def SendReqE_def SendReqSs_def SendReqS_def ABS_SendGntEs_def ABS_SendGntE_def ABS_SendGntSs_def ABS_SendGntS_def ABS_RecvReqEs_def ABS_RecvReqE_def ABS_RecvReqSs_def ABS_RecvReqS_def ABS_RecvInvAck1s_def ABS_RecvInvAck1_def  apply(auto      )    
 
done

lemma symProtAll : 
             " 
                  symProtRules' N (RecvGntEs N)"
                 

" 
                  symProtRules' N (RecvGntSs N)"
                 

" 
                  symProtRules' N (SendGntEs N)"
                 

" 
                  symProtRules' N (SendGntSs N)"
                 

" 
                  symProtRules' N (RecvInvAck1s N)"
                 

" 
                  symProtRules' N (RecvInvAck2s N)"
                 

" 
                  symProtRules' N (SendInvAcks N)"
                 

" 
                  symProtRules' N (SendInvs N)"
                 

" 
                  symProtRules' N (RecvReqEs N)"
                 

" 
                  symProtRules' N (RecvReqSs N)"
                 

" 
                  symProtRules' N (SendReqEs N)"
                 

" 
                  symProtRules' N (SendReqSs N)"
                 
 
              using symRecvGntE(1) RecvGntEs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symRecvGntS(1) RecvGntSs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symSendGntE(1) SendGntEs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symSendGntS(1) SendGntSs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symRecvInvAck1(1) RecvInvAck1s_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symRecvInvAck2(1) RecvInvAck2s_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symSendInvAck(1) SendInvAcks_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symSendInv(1) SendInvs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symRecvReqE(1) RecvReqEs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symRecvReqS(1) RecvReqSs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symSendReqE(1) SendReqEs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symSendReqS(1) SendReqSs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
done

lemma symCntrlProp : 
                  " 
                  symParamForm2 N (CntrlProp N)"
                 unfolding CntrlProp_def  apply(auto      )    
 
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

definition lemmasFor_RecvGntE :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_RecvGntE N = []"

definition RecvGntE_ref :: "nat \<Rightarrow> rule" where
 "RecvGntE_ref i \<equiv> 
   IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const GntE
  \<triangleright>
   assign (Para ''Cache.State'' i, Const E) ||
   assign (Para ''Chan2.Cmd'' i, Const Empty)"

lemma symRecvGntE_ref : 
             " 
                  symParamRule N RecvGntE_ref"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (RecvGntE_ref i)"
                 
 
             unfolding RecvGntE_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition RecvGntE_refs :: "nat \<Rightarrow> rule set" where
 "RecvGntE_refs N \<equiv> oneParamCons N RecvGntE_ref"

lemma RecvGntE_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_RecvGntE N) j i) (RecvGntE i) = RecvGntE_ref i"
                 unfolding lemmasFor_RecvGntE_def  RecvGntE_def RecvGntE_ref_def  apply(auto      )    
 
done

lemma abs_RecvGntE_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (RecvGntE_ref i) = RecvGntE_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (RecvGntE_ref i) = skipRule"
                 
 
             unfolding RecvGntE_ref_def RecvGntE_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_RecvGntS :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_RecvGntS N = []"

definition RecvGntS_ref :: "nat \<Rightarrow> rule" where
 "RecvGntS_ref i \<equiv> 
   IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const GntS
  \<triangleright>
   assign (Para ''Cache.State'' i, Const S) ||
   assign (Para ''Chan2.Cmd'' i, Const Empty)"

lemma symRecvGntS_ref : 
             " 
                  symParamRule N RecvGntS_ref"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (RecvGntS_ref i)"
                 
 
             unfolding RecvGntS_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition RecvGntS_refs :: "nat \<Rightarrow> rule set" where
 "RecvGntS_refs N \<equiv> oneParamCons N RecvGntS_ref"

lemma RecvGntS_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_RecvGntS N) j i) (RecvGntS i) = RecvGntS_ref i"
                 unfolding lemmasFor_RecvGntS_def  RecvGntS_def RecvGntS_ref_def  apply(auto      )    
 
done

lemma abs_RecvGntS_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (RecvGntS_ref i) = RecvGntS_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (RecvGntS_ref i) = skipRule"
                 
 
             unfolding RecvGntS_ref_def RecvGntS_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_SendGntE :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_SendGntE N = []"

definition SendGntE_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "SendGntE_ref N i \<equiv> 
   IVar (Ident ''CurCmd'') =\<^sub>f Const ReqE \<and>\<^sub>f
   IVar (Ident ''CurPtr'') =\<^sub>f Const (index i) \<and>\<^sub>f
   IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
   IVar (Ident ''ExGntd'') =\<^sub>f Const false \<and>\<^sub>f
   (\<forall>\<^sub>fj. IVar (Para ''ShrSet'' j) =\<^sub>f Const false) N
  \<triangleright>
   assign (Para ''Chan2.Cmd'' i, Const GntE) ||
   assign (Para ''ShrSet'' i, Const true) ||
   assign (Ident ''ExGntd'', Const true) ||
   assign (Ident ''CurCmd'', Const Empty)"

lemma symSendGntE_ref : 
             " 
                  symParamRule N (SendGntE_ref N)"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (SendGntE_ref N i)"
                 
 
             unfolding SendGntE_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition SendGntE_refs :: "nat \<Rightarrow> rule set" where
 "SendGntE_refs N \<equiv> oneParamCons N (SendGntE_ref N)"

lemma SendGntE_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_SendGntE N) j i) (SendGntE N i) = SendGntE_ref N i"
                 unfolding lemmasFor_SendGntE_def  SendGntE_def SendGntE_ref_def  apply(auto      )    
 
done

lemma abs_SendGntE_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (SendGntE_ref N i) = SendGntE_ref M i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (SendGntE_ref N i) = ABS_SendGntE M"
                 
 
             unfolding SendGntE_ref_def SendGntE_ref_def ABS_SendGntE_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_SendGntS :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_SendGntS N = []"

definition SendGntS_ref :: "nat \<Rightarrow> rule" where
 "SendGntS_ref i \<equiv> 
   IVar (Ident ''CurCmd'') =\<^sub>f Const ReqS \<and>\<^sub>f
   IVar (Ident ''CurPtr'') =\<^sub>f Const (index i) \<and>\<^sub>f
   IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
   IVar (Ident ''ExGntd'') =\<^sub>f Const false
  \<triangleright>
   assign (Para ''Chan2.Cmd'' i, Const GntS) ||
   assign (Para ''ShrSet'' i, Const true) ||
   assign (Ident ''CurCmd'', Const Empty)"

lemma symSendGntS_ref : 
             " 
                  symParamRule N SendGntS_ref"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (SendGntS_ref i)"
                 
 
             unfolding SendGntS_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition SendGntS_refs :: "nat \<Rightarrow> rule set" where
 "SendGntS_refs N \<equiv> oneParamCons N SendGntS_ref"

lemma SendGntS_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_SendGntS N) j i) (SendGntS i) = SendGntS_ref i"
                 unfolding lemmasFor_SendGntS_def  SendGntS_def SendGntS_ref_def  apply(auto      )    
 
done

lemma abs_SendGntS_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (SendGntS_ref i) = SendGntS_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (SendGntS_ref i) = ABS_SendGntS M"
                 
 
             unfolding SendGntS_ref_def SendGntS_ref_def ABS_SendGntS_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_RecvInvAck1 :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_RecvInvAck1 N = [Lemma_1 N]"

definition RecvInvAck1_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "RecvInvAck1_ref N i \<equiv> 
   IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const InvAck \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
   IVar (Ident ''ExGntd'') =\<^sub>f Const true \<and>\<^sub>f
   forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''Cache.State'' j) =\<^sub>f Const E \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Chan2.Cmd'' j) =\<^sub>f Const GntE \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''Chan3.Cmd'' j) =\<^sub>f Const InvAck) i N
  \<triangleright>
   assign (Para ''Chan3.Cmd'' i, Const Empty) ||
   assign (Para ''ShrSet'' i, Const false) ||
   assign (Ident ''ExGntd'', Const false)"

lemma symRecvInvAck1_ref : 
             " 
                  symParamRule N (RecvInvAck1_ref N)"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (RecvInvAck1_ref N i)"
                 
 
             unfolding RecvInvAck1_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition RecvInvAck1_refs :: "nat \<Rightarrow> rule set" where
 "RecvInvAck1_refs N \<equiv> oneParamCons N (RecvInvAck1_ref N)"

lemma RecvInvAck1_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_RecvInvAck1 N) j i) (RecvInvAck1 i) = RecvInvAck1_ref N i"
                 unfolding lemmasFor_RecvInvAck1_def Lemma_1_def RecvInvAck1_def RecvInvAck1_ref_def  apply(auto      )    
 
done

lemma abs_RecvInvAck1_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (RecvInvAck1_ref N i) = RecvInvAck1_ref M i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (RecvInvAck1_ref N i) = ABS_RecvInvAck1 M"
                 
 
             unfolding RecvInvAck1_ref_def RecvInvAck1_ref_def ABS_RecvInvAck1_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_RecvInvAck2 :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_RecvInvAck2 N = []"

definition RecvInvAck2_ref :: "nat \<Rightarrow> rule" where
 "RecvInvAck2_ref i \<equiv> 
   IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const InvAck \<and>\<^sub>f
   \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
   IVar (Ident ''ExGntd'') =\<^sub>f Const false
  \<triangleright>
   assign (Para ''Chan3.Cmd'' i, Const Empty) ||
   assign (Para ''ShrSet'' i, Const false)"

lemma symRecvInvAck2_ref : 
             " 
                  symParamRule N RecvInvAck2_ref"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (RecvInvAck2_ref i)"
                 
 
             unfolding RecvInvAck2_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition RecvInvAck2_refs :: "nat \<Rightarrow> rule set" where
 "RecvInvAck2_refs N \<equiv> oneParamCons N RecvInvAck2_ref"

lemma RecvInvAck2_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_RecvInvAck2 N) j i) (RecvInvAck2 i) = RecvInvAck2_ref i"
                 unfolding lemmasFor_RecvInvAck2_def  RecvInvAck2_def RecvInvAck2_ref_def  apply(auto      )    
 
done

lemma abs_RecvInvAck2_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (RecvInvAck2_ref i) = RecvInvAck2_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (RecvInvAck2_ref i) = skipRule"
                 
 
             unfolding RecvInvAck2_ref_def RecvInvAck2_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_SendInvAck :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_SendInvAck N = []"

definition SendInvAck_ref :: "nat \<Rightarrow> rule" where
 "SendInvAck_ref i \<equiv> 
   IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Inv \<and>\<^sub>f
   IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const Empty
  \<triangleright>
   assign (Para ''Chan2.Cmd'' i, Const Empty) ||
   assign (Para ''Chan3.Cmd'' i, Const InvAck) ||
   assign (Para ''Cache.State'' i, Const I)"

lemma symSendInvAck_ref : 
             " 
                  symParamRule N SendInvAck_ref"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (SendInvAck_ref i)"
                 
 
             unfolding SendInvAck_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition SendInvAck_refs :: "nat \<Rightarrow> rule set" where
 "SendInvAck_refs N \<equiv> oneParamCons N SendInvAck_ref"

lemma SendInvAck_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_SendInvAck N) j i) (SendInvAck i) = SendInvAck_ref i"
                 unfolding lemmasFor_SendInvAck_def  SendInvAck_def SendInvAck_ref_def  apply(auto      )    
 
done

lemma abs_SendInvAck_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (SendInvAck_ref i) = SendInvAck_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (SendInvAck_ref i) = skipRule"
                 
 
             unfolding SendInvAck_ref_def SendInvAck_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_SendInv :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_SendInv N = []"

definition SendInv_ref :: "nat \<Rightarrow> rule" where
 "SendInv_ref i \<equiv> 
   IVar (Para ''Chan2.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
   IVar (Para ''InvSet'' i) =\<^sub>f Const true \<and>\<^sub>f
   (IVar (Ident ''CurCmd'') =\<^sub>f Const ReqE \<or>\<^sub>f
   IVar (Ident ''CurCmd'') =\<^sub>f Const ReqS \<and>\<^sub>f
   IVar (Ident ''ExGntd'') =\<^sub>f Const true)
  \<triangleright>
   assign (Para ''Chan2.Cmd'' i, Const Inv) ||
   assign (Para ''InvSet'' i, Const false)"

lemma symSendInv_ref : 
             " 
                  symParamRule N SendInv_ref"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (SendInv_ref i)"
                 
 
             unfolding SendInv_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition SendInv_refs :: "nat \<Rightarrow> rule set" where
 "SendInv_refs N \<equiv> oneParamCons N SendInv_ref"

lemma SendInv_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_SendInv N) j i) (SendInv i) = SendInv_ref i"
                 unfolding lemmasFor_SendInv_def  SendInv_def SendInv_ref_def  apply(auto      )    
 
done

lemma abs_SendInv_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (SendInv_ref i) = SendInv_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (SendInv_ref i) = skipRule"
                 
 
             unfolding SendInv_ref_def SendInv_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_RecvReqE :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_RecvReqE N = []"

definition RecvReqE_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "RecvReqE_ref N i \<equiv> 
   IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
   IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const ReqE
  \<triangleright>
   assign (Ident ''CurCmd'', Const ReqE) ||
   assign (Ident ''CurPtr'', Const (index i)) ||
   assign (Para ''Chan1.Cmd'' i, Const Empty) ||
   forallStm (\<lambda>j. assign (Para ''InvSet'' j, IVar (Para ''ShrSet'' j))) N"

lemma symRecvReqE_ref : 
             " 
                  symParamRule N (RecvReqE_ref N)"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (RecvReqE_ref N i)"
                 
 
             unfolding RecvReqE_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition RecvReqE_refs :: "nat \<Rightarrow> rule set" where
 "RecvReqE_refs N \<equiv> oneParamCons N (RecvReqE_ref N)"

lemma RecvReqE_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_RecvReqE N) j i) (RecvReqE N i) = RecvReqE_ref N i"
                 unfolding lemmasFor_RecvReqE_def  RecvReqE_def RecvReqE_ref_def  apply(auto      )    
 
done

lemma abs_RecvReqE_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (RecvReqE_ref N i) = RecvReqE_ref M i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (RecvReqE_ref N i) = ABS_RecvReqE M"
                 
 
             unfolding RecvReqE_ref_def RecvReqE_ref_def ABS_RecvReqE_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_RecvReqS :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_RecvReqS N = []"

definition RecvReqS_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "RecvReqS_ref N i \<equiv> 
   IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
   IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const ReqS
  \<triangleright>
   assign (Ident ''CurCmd'', Const ReqS) ||
   assign (Ident ''CurPtr'', Const (index i)) ||
   assign (Para ''Chan1.Cmd'' i, Const Empty) ||
   forallStm (\<lambda>j. assign (Para ''InvSet'' j, IVar (Para ''ShrSet'' j))) N"

lemma symRecvReqS_ref : 
             " 
                  symParamRule N (RecvReqS_ref N)"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (RecvReqS_ref N i)"
                 
 
             unfolding RecvReqS_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition RecvReqS_refs :: "nat \<Rightarrow> rule set" where
 "RecvReqS_refs N \<equiv> oneParamCons N (RecvReqS_ref N)"

lemma RecvReqS_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_RecvReqS N) j i) (RecvReqS N i) = RecvReqS_ref N i"
                 unfolding lemmasFor_RecvReqS_def  RecvReqS_def RecvReqS_ref_def  apply(auto      )    
 
done

lemma abs_RecvReqS_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (RecvReqS_ref N i) = RecvReqS_ref M i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (RecvReqS_ref N i) = ABS_RecvReqS M"
                 
 
             unfolding RecvReqS_ref_def RecvReqS_ref_def ABS_RecvReqS_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_SendReqE :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_SendReqE N = []"

definition SendReqE_ref :: "nat \<Rightarrow> rule" where
 "SendReqE_ref i \<equiv> 
   IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
   (IVar (Para ''Cache.State'' i) =\<^sub>f Const I \<or>\<^sub>f
   IVar (Para ''Cache.State'' i) =\<^sub>f Const S)
  \<triangleright>
   assign (Para ''Chan1.Cmd'' i, Const ReqE)"

lemma symSendReqE_ref : 
             " 
                  symParamRule N SendReqE_ref"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (SendReqE_ref i)"
                 
 
             unfolding SendReqE_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition SendReqE_refs :: "nat \<Rightarrow> rule set" where
 "SendReqE_refs N \<equiv> oneParamCons N SendReqE_ref"

lemma SendReqE_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_SendReqE N) j i) (SendReqE i) = SendReqE_ref i"
                 unfolding lemmasFor_SendReqE_def  SendReqE_def SendReqE_ref_def  apply(auto      )    
 
done

lemma abs_SendReqE_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (SendReqE_ref i) = SendReqE_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (SendReqE_ref i) = skipRule"
                 
 
             unfolding SendReqE_ref_def SendReqE_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_SendReqS :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_SendReqS N = []"

definition SendReqS_ref :: "nat \<Rightarrow> rule" where
 "SendReqS_ref i \<equiv> 
   IVar (Para ''Chan1.Cmd'' i) =\<^sub>f Const Empty \<and>\<^sub>f
   IVar (Para ''Cache.State'' i) =\<^sub>f Const I
  \<triangleright>
   assign (Para ''Chan1.Cmd'' i, Const ReqS)"

lemma symSendReqS_ref : 
             " 
                  symParamRule N SendReqS_ref"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (SendReqS_ref i)"
                 
 
             unfolding SendReqS_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition SendReqS_refs :: "nat \<Rightarrow> rule set" where
 "SendReqS_refs N \<equiv> oneParamCons N SendReqS_ref"

lemma SendReqS_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_SendReqS N) j i) (SendReqS i) = SendReqS_ref i"
                 unfolding lemmasFor_SendReqS_def  SendReqS_def SendReqS_ref_def  apply(auto      )    
 
done

lemma abs_SendReqS_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (SendReqS_ref i) = SendReqS_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (SendReqS_ref i) = skipRule"
                 
 
             unfolding SendReqS_ref_def SendReqS_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition InvS :: "nat \<Rightarrow> (((nat \<Rightarrow> nat \<Rightarrow> formula) list) list)" where
 "InvS N = [lemmasFor_RecvGntE N, lemmasFor_RecvGntS N, lemmasFor_SendGntE N, lemmasFor_SendGntS N, lemmasFor_RecvInvAck1 N, lemmasFor_RecvInvAck2 N, lemmasFor_SendInvAck N, lemmasFor_SendInv N, lemmasFor_RecvReqE N, lemmasFor_RecvReqS N, lemmasFor_SendReqE N, lemmasFor_SendReqS N]"

definition rule_refs :: "nat \<Rightarrow> rule set" where
 "rule_refs N = (RecvGntE_refs N \<union> (RecvGntS_refs N \<union> (SendGntE_refs N \<union> (SendGntS_refs N \<union> (RecvInvAck1_refs N \<union> (RecvInvAck2_refs N \<union> (SendInvAck_refs N \<union> (SendInv_refs N \<union> (RecvReqE_refs N \<union> (RecvReqS_refs N \<union> (SendReqE_refs N \<union> SendReqS_refs N)))))))))))"

lemma RecvGntEStrengthRel : 
                  " 
                  strengthenRel (RecvGntEs N) (set (InvS N)) (RecvGntE_refs N) N"
                 unfolding RecvGntEs_def RecvGntE_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_RecvGntE" in strengthenExt1)
 using RecvGntE_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma RecvGntSStrengthRel : 
                  " 
                  strengthenRel (RecvGntSs N) (set (InvS N)) (RecvGntS_refs N) N"
                 unfolding RecvGntSs_def RecvGntS_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_RecvGntS" in strengthenExt1)
 using RecvGntS_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma SendGntEStrengthRel : 
                  " 
                  strengthenRel (SendGntEs N) (set (InvS N)) (SendGntE_refs N) N"
                 unfolding SendGntEs_def SendGntE_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_SendGntE" in strengthenExt1)
 using SendGntE_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma SendGntSStrengthRel : 
                  " 
                  strengthenRel (SendGntSs N) (set (InvS N)) (SendGntS_refs N) N"
                 unfolding SendGntSs_def SendGntS_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_SendGntS" in strengthenExt1)
 using SendGntS_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma RecvInvAck1StrengthRel : 
                  " 
                  strengthenRel (RecvInvAck1s N) (set (InvS N)) (RecvInvAck1_refs N) N"
                 unfolding RecvInvAck1s_def RecvInvAck1_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_RecvInvAck1" in strengthenExt1)
 using RecvInvAck1_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma RecvInvAck2StrengthRel : 
                  " 
                  strengthenRel (RecvInvAck2s N) (set (InvS N)) (RecvInvAck2_refs N) N"
                 unfolding RecvInvAck2s_def RecvInvAck2_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_RecvInvAck2" in strengthenExt1)
 using RecvInvAck2_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma SendInvAckStrengthRel : 
                  " 
                  strengthenRel (SendInvAcks N) (set (InvS N)) (SendInvAck_refs N) N"
                 unfolding SendInvAcks_def SendInvAck_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_SendInvAck" in strengthenExt1)
 using SendInvAck_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma SendInvStrengthRel : 
                  " 
                  strengthenRel (SendInvs N) (set (InvS N)) (SendInv_refs N) N"
                 unfolding SendInvs_def SendInv_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_SendInv" in strengthenExt1)
 using SendInv_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma RecvReqEStrengthRel : 
                  " 
                  strengthenRel (RecvReqEs N) (set (InvS N)) (RecvReqE_refs N) N"
                 unfolding RecvReqEs_def RecvReqE_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_RecvReqE" in strengthenExt1)
 using RecvReqE_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma RecvReqSStrengthRel : 
                  " 
                  strengthenRel (RecvReqSs N) (set (InvS N)) (RecvReqS_refs N) N"
                 unfolding RecvReqSs_def RecvReqS_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_RecvReqS" in strengthenExt1)
 using RecvReqS_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma SendReqEStrengthRel : 
                  " 
                  strengthenRel (SendReqEs N) (set (InvS N)) (SendReqE_refs N) N"
                 unfolding SendReqEs_def SendReqE_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_SendReqE" in strengthenExt1)
 using SendReqE_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma SendReqSStrengthRel : 
                  " 
                  strengthenRel (SendReqSs N) (set (InvS N)) (SendReqS_refs N) N"
                 unfolding SendReqSs_def SendReqS_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_SendReqS" in strengthenExt1)
 using SendReqS_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma deriveAllRef : 
             "[|r : RecvGntE_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : RecvGntS_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : SendGntE_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : SendGntS_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : RecvInvAck1_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : RecvInvAck2_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : SendInvAck_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : SendInv_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : RecvReqE_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : RecvReqS_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : SendReqE_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : SendReqS_refs N|] 
                 ==> deriveRule (env N) r"
                 
 
             unfolding deriveRule_def deriveForm_def deriveStmt_def RecvGntE_refs_def RecvGntE_ref_def RecvGntS_refs_def RecvGntS_ref_def SendGntE_refs_def SendGntE_ref_def SendGntS_refs_def SendGntS_ref_def RecvInvAck1_refs_def RecvInvAck1_ref_def RecvInvAck2_refs_def RecvInvAck2_ref_def SendInvAck_refs_def SendInvAck_ref_def SendInv_refs_def SendInv_ref_def RecvReqE_refs_def RecvReqE_ref_def RecvReqS_refs_def RecvReqS_ref_def SendReqE_refs_def SendReqE_ref_def SendReqS_refs_def SendReqS_ref_def  apply(auto      )    
 
done

lemma symProtAllRef : 
             " 
                  symProtRules' N (RecvGntE_refs N)"
                 

" 
                  symProtRules' N (RecvGntS_refs N)"
                 

" 
                  symProtRules' N (SendGntE_refs N)"
                 

" 
                  symProtRules' N (SendGntS_refs N)"
                 

" 
                  symProtRules' N (RecvInvAck1_refs N)"
                 

" 
                  symProtRules' N (RecvInvAck2_refs N)"
                 

" 
                  symProtRules' N (SendInvAck_refs N)"
                 

" 
                  symProtRules' N (SendInv_refs N)"
                 

" 
                  symProtRules' N (RecvReqE_refs N)"
                 

" 
                  symProtRules' N (RecvReqS_refs N)"
                 

" 
                  symProtRules' N (SendReqE_refs N)"
                 

" 
                  symProtRules' N (SendReqS_refs N)"
                 
 
              using symRecvGntE_ref(1) RecvGntE_refs_def symRecvGntS_ref(1) RecvGntS_refs_def symSendGntE_ref(1) SendGntE_refs_def symSendGntS_ref(1) SendGntS_refs_def symRecvInvAck1_ref(1) RecvInvAck1_refs_def symRecvInvAck2_ref(1) RecvInvAck2_refs_def symSendInvAck_ref(1) SendInvAck_refs_def symSendInv_ref(1) SendInv_refs_def symRecvReqE_ref(1) RecvReqE_refs_def symRecvReqS_ref(1) RecvReqS_refs_def symSendReqE_ref(1) SendReqE_refs_def symSendReqS_ref(1) SendReqS_refs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )    
 
done

lemma StrengthRelRules2Rule_refs : 
                  " 
                  strengthenRel (rules N) (set (InvS N)) (rule_refs N) N"
                 unfolding rules_def rule_refs_def   apply(rule strenRelUnion)
  apply(blast intro: RecvGntEStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: RecvGntSStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: SendGntEStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: SendGntSStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: RecvInvAck1StrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: RecvInvAck2StrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: SendInvAckStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: SendInvStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: RecvReqEStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: RecvReqSStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: SendReqEStrengthRel     )

  apply(blast intro: SendReqSStrengthRel     )

done

lemma Abs_RecvGntE_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` RecvGntE_refs N) = (RecvGntE_refs M Un {skipRule})"
                 unfolding RecvGntE_refs_def   apply(rule absGen)
 using abs_RecvGntE_ref apply(auto      )    
 
done

lemma Abs_RecvGntS_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` RecvGntS_refs N) = (RecvGntS_refs M Un {skipRule})"
                 unfolding RecvGntS_refs_def   apply(rule absGen)
 using abs_RecvGntS_ref apply(auto      )    
 
done

lemma Abs_SendGntE_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` SendGntE_refs N) = (SendGntE_refs M Un ABS_SendGntEs M)"
                 unfolding SendGntE_refs_def ABS_SendGntEs_def   apply(rule absGen)
 using abs_SendGntE_ref apply(auto      )    
 
done

lemma Abs_SendGntS_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` SendGntS_refs N) = (SendGntS_refs M Un ABS_SendGntSs M)"
                 unfolding SendGntS_refs_def ABS_SendGntSs_def   apply(rule absGen)
 using abs_SendGntS_ref apply(auto      )    
 
done

lemma Abs_RecvInvAck1_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` RecvInvAck1_refs N) = (RecvInvAck1_refs M Un ABS_RecvInvAck1s M)"
                 unfolding RecvInvAck1_refs_def ABS_RecvInvAck1s_def   apply(rule absGen)
 using abs_RecvInvAck1_ref apply(auto      )    
 
done

lemma Abs_RecvInvAck2_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` RecvInvAck2_refs N) = (RecvInvAck2_refs M Un {skipRule})"
                 unfolding RecvInvAck2_refs_def   apply(rule absGen)
 using abs_RecvInvAck2_ref apply(auto      )    
 
done

lemma Abs_SendInvAck_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` SendInvAck_refs N) = (SendInvAck_refs M Un {skipRule})"
                 unfolding SendInvAck_refs_def   apply(rule absGen)
 using abs_SendInvAck_ref apply(auto      )    
 
done

lemma Abs_SendInv_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` SendInv_refs N) = (SendInv_refs M Un {skipRule})"
                 unfolding SendInv_refs_def   apply(rule absGen)
 using abs_SendInv_ref apply(auto      )    
 
done

lemma Abs_RecvReqE_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` RecvReqE_refs N) = (RecvReqE_refs M Un ABS_RecvReqEs M)"
                 unfolding RecvReqE_refs_def ABS_RecvReqEs_def   apply(rule absGen)
 using abs_RecvReqE_ref apply(auto      )    
 
done

lemma Abs_RecvReqS_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` RecvReqS_refs N) = (RecvReqS_refs M Un ABS_RecvReqSs M)"
                 unfolding RecvReqS_refs_def ABS_RecvReqSs_def   apply(rule absGen)
 using abs_RecvReqS_ref apply(auto      )    
 
done

lemma Abs_SendReqE_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` SendReqE_refs N) = (SendReqE_refs M Un {skipRule})"
                 unfolding SendReqE_refs_def   apply(rule absGen)
 using abs_SendReqE_ref apply(auto      )    
 
done

lemma Abs_SendReqS_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` SendReqS_refs N) = (SendReqS_refs M Un {skipRule})"
                 unfolding SendReqS_refs_def   apply(rule absGen)
 using abs_SendReqS_ref apply(auto      )    
 
done

definition ABS_rules :: "nat \<Rightarrow> rule set" where [simp]:
 "ABS_rules N = (RecvGntE_refs N \<union> (RecvGntS_refs N \<union> (SendGntE_refs N \<union> (ABS_SendGntEs N \<union> (SendGntS_refs N \<union> (ABS_SendGntSs N \<union> (RecvInvAck1_refs N \<union> (ABS_RecvInvAck1s N \<union> (RecvInvAck2_refs N \<union> (SendInvAck_refs N \<union> (SendInv_refs N \<union> (RecvReqE_refs N \<union> (ABS_RecvReqEs N \<union> (RecvReqS_refs N \<union> (ABS_RecvReqSs N \<union> (SendReqE_refs N \<union> (SendReqS_refs N \<union> {skipRule})))))))))))))))))"

definition ABS_rules' :: "nat \<Rightarrow> rule set" where [simp]:
 "ABS_rules' N = ((RecvGntE_refs N \<union> {skipRule}) \<union> ((RecvGntS_refs N \<union> {skipRule}) \<union> ((SendGntE_refs N \<union> ABS_SendGntEs N) \<union> ((SendGntS_refs N \<union> ABS_SendGntSs N) \<union> ((RecvInvAck1_refs N \<union> ABS_RecvInvAck1s N) \<union> ((RecvInvAck2_refs N \<union> {skipRule}) \<union> ((SendInvAck_refs N \<union> {skipRule}) \<union> ((SendInv_refs N \<union> {skipRule}) \<union> ((RecvReqE_refs N \<union> ABS_RecvReqEs N) \<union> ((RecvReqS_refs N \<union> ABS_RecvReqSs N) \<union> ((SendReqE_refs N \<union> {skipRule}) \<union> (SendReqS_refs N \<union> {skipRule}))))))))))))"

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

  apply(auto     simp add: Abs_RecvGntE_refs Abs_RecvGntS_refs Abs_SendGntE_refs Abs_SendGntS_refs Abs_RecvInvAck1_refs Abs_RecvInvAck2_refs Abs_SendInvAck_refs Abs_SendInv_refs Abs_RecvReqE_refs Abs_RecvReqS_refs Abs_SendReqE_refs Abs_SendReqS_refs )    
 
done

definition Lemma_1' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_1' N i j \<equiv> \<not>\<^sub>f Const (index i) =\<^sub>f Const (index j) \<and>\<^sub>f
  IVar (Para ''Chan3.Cmd'' i) =\<^sub>f Const InvAck \<and>\<^sub>f
  \<not>\<^sub>f IVar (Ident ''CurCmd'') =\<^sub>f Const Empty \<and>\<^sub>f
  IVar (Ident ''ExGntd'') =\<^sub>f Const true \<longrightarrow>\<^sub>f
  \<not>\<^sub>f IVar (Para ''Cache.State'' j) =\<^sub>f Const E \<and>\<^sub>f
  \<not>\<^sub>f IVar (Para ''Chan2.Cmd'' j) =\<^sub>f Const GntE \<and>\<^sub>f
  \<not>\<^sub>f IVar (Para ''Chan3.Cmd'' j) =\<^sub>f Const InvAck"

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

lemma symInvs : 
             " 
                  symParamForm2 N (Lemma_1' N)"
                 
 
             unfolding Lemma_1'_def  apply(auto      )    
 
subgoal    apply(intro  symParamForm2Imply symParamFormForallExcl2 )
  
  unfolding symParamForm2_def  apply(auto      )    
   done

done

definition lemmasFor_RecvGntE' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_RecvGntE' N = []"

lemma strengthenVsObsLs_lemmasFor_RecvGntE : 
                  " 
                  strengthenVsObsLs (lemmasFor_RecvGntE N) (lemmasFor_RecvGntE' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_RecvGntE_def lemmasFor_RecvGntE'_def  apply(auto      )    
 
done

lemma lemmaRecvGntE_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : RecvGntE_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding RecvGntE_refs_def RecvGntE_ref_def  apply(auto      )    
 
done

definition lemmasFor_RecvGntS' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_RecvGntS' N = []"

lemma strengthenVsObsLs_lemmasFor_RecvGntS : 
                  " 
                  strengthenVsObsLs (lemmasFor_RecvGntS N) (lemmasFor_RecvGntS' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_RecvGntS_def lemmasFor_RecvGntS'_def  apply(auto      )    
 
done

lemma lemmaRecvGntS_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : RecvGntS_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding RecvGntS_refs_def RecvGntS_ref_def  apply(auto      )    
 
done

definition lemmasFor_SendGntE' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_SendGntE' N = []"

lemma strengthenVsObsLs_lemmasFor_SendGntE : 
                  " 
                  strengthenVsObsLs (lemmasFor_SendGntE N) (lemmasFor_SendGntE' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_SendGntE_def lemmasFor_SendGntE'_def  apply(auto      )    
 
done

lemma lemmaSendGntE_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : SendGntE_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding SendGntE_refs_def SendGntE_ref_def  apply(auto      )    
 
done

definition lemmasFor_SendGntS' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_SendGntS' N = []"

lemma strengthenVsObsLs_lemmasFor_SendGntS : 
                  " 
                  strengthenVsObsLs (lemmasFor_SendGntS N) (lemmasFor_SendGntS' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_SendGntS_def lemmasFor_SendGntS'_def  apply(auto      )    
 
done

lemma lemmaSendGntS_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : SendGntS_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding SendGntS_refs_def SendGntS_ref_def  apply(auto      )    
 
done

definition lemmasFor_RecvInvAck1' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_RecvInvAck1' N = [Lemma_1' N]"

lemma strengthenVsObsLs_lemmasFor_RecvInvAck1 : 
                  " 
                  strengthenVsObsLs (lemmasFor_RecvInvAck1 N) (lemmasFor_RecvInvAck1' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_RecvInvAck1_def lemmasFor_RecvInvAck1'_def  apply(auto intro: strengthenVsObsLemma_1     )    
 
done

lemma lemmaRecvInvAck1_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : RecvInvAck1_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding RecvInvAck1_refs_def RecvInvAck1_ref_def  apply(auto      )    
 
done

definition lemmasFor_RecvInvAck2' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_RecvInvAck2' N = []"

lemma strengthenVsObsLs_lemmasFor_RecvInvAck2 : 
                  " 
                  strengthenVsObsLs (lemmasFor_RecvInvAck2 N) (lemmasFor_RecvInvAck2' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_RecvInvAck2_def lemmasFor_RecvInvAck2'_def  apply(auto      )    
 
done

lemma lemmaRecvInvAck2_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : RecvInvAck2_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding RecvInvAck2_refs_def RecvInvAck2_ref_def  apply(auto      )    
 
done

definition lemmasFor_SendInvAck' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_SendInvAck' N = []"

lemma strengthenVsObsLs_lemmasFor_SendInvAck : 
                  " 
                  strengthenVsObsLs (lemmasFor_SendInvAck N) (lemmasFor_SendInvAck' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_SendInvAck_def lemmasFor_SendInvAck'_def  apply(auto      )    
 
done

lemma lemmaSendInvAck_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : SendInvAck_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding SendInvAck_refs_def SendInvAck_ref_def  apply(auto      )    
 
done

definition lemmasFor_SendInv' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_SendInv' N = []"

lemma strengthenVsObsLs_lemmasFor_SendInv : 
                  " 
                  strengthenVsObsLs (lemmasFor_SendInv N) (lemmasFor_SendInv' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_SendInv_def lemmasFor_SendInv'_def  apply(auto      )    
 
done

lemma lemmaSendInv_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : SendInv_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding SendInv_refs_def SendInv_ref_def  apply(auto      )    
 
done

definition lemmasFor_RecvReqE' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_RecvReqE' N = []"

lemma strengthenVsObsLs_lemmasFor_RecvReqE : 
                  " 
                  strengthenVsObsLs (lemmasFor_RecvReqE N) (lemmasFor_RecvReqE' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_RecvReqE_def lemmasFor_RecvReqE'_def  apply(auto      )    
 
done

lemma lemmaRecvReqE_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : RecvReqE_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding RecvReqE_refs_def RecvReqE_ref_def  apply(auto      )    
 
done

definition lemmasFor_RecvReqS' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_RecvReqS' N = []"

lemma strengthenVsObsLs_lemmasFor_RecvReqS : 
                  " 
                  strengthenVsObsLs (lemmasFor_RecvReqS N) (lemmasFor_RecvReqS' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_RecvReqS_def lemmasFor_RecvReqS'_def  apply(auto      )    
 
done

lemma lemmaRecvReqS_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : RecvReqS_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding RecvReqS_refs_def RecvReqS_ref_def  apply(auto      )    
 
done

definition lemmasFor_SendReqE' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_SendReqE' N = []"

lemma strengthenVsObsLs_lemmasFor_SendReqE : 
                  " 
                  strengthenVsObsLs (lemmasFor_SendReqE N) (lemmasFor_SendReqE' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_SendReqE_def lemmasFor_SendReqE'_def  apply(auto      )    
 
done

lemma lemmaSendReqE_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : SendReqE_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding SendReqE_refs_def SendReqE_ref_def  apply(auto      )    
 
done

definition lemmasFor_SendReqS' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_SendReqS' N = []"

lemma strengthenVsObsLs_lemmasFor_SendReqS : 
                  " 
                  strengthenVsObsLs (lemmasFor_SendReqS N) (lemmasFor_SendReqS' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_SendReqS_def lemmasFor_SendReqS'_def  apply(auto      )    
 
done

lemma lemmaSendReqS_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : SendReqS_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding SendReqS_refs_def SendReqS_ref_def  apply(auto      )    
 
done

definition InvS' :: "nat \<Rightarrow> (((nat \<Rightarrow> nat \<Rightarrow> formula) list) list)" where
 "InvS' N = [lemmasFor_RecvGntE' N, lemmasFor_RecvGntS' N, lemmasFor_SendGntE' N, lemmasFor_SendGntS' N, lemmasFor_RecvInvAck1' N, lemmasFor_RecvInvAck2' N, lemmasFor_SendInvAck' N, lemmasFor_SendInv' N, lemmasFor_RecvReqE' N, lemmasFor_RecvReqS' N, lemmasFor_SendReqE' N, lemmasFor_SendReqS' N]"

lemma wellFormedRule_refs : 
                  "[|r : rule_refs N|] 
                 ==> wellFormedRule (env N) N r"
                   apply(auto     simp add: rule_refs_def   RecvGntE_refs_def RecvGntS_refs_def SendGntE_refs_def SendGntS_refs_def RecvInvAck1_refs_def RecvInvAck2_refs_def SendInvAck_refs_def SendInv_refs_def RecvReqE_refs_def RecvReqS_refs_def SendReqE_refs_def SendReqS_refs_def symRecvGntE_ref symRecvGntS_ref symSendGntE_ref symSendGntS_ref symRecvInvAck1_ref symRecvInvAck2_ref symSendInvAck_ref symSendInv_ref symRecvReqE_ref symRecvReqS_ref symSendReqE_ref symSendReqS_ref )    
 
done

lemma SafeAndderiveAll : 
                  "[|M < N;M = 1;l <= M;k <= M;pinvL : set (InvS' N);pf : set pinvL|] 
                 ==> safeForm (env N) M (pf k l) & deriveForm (env N) (pf k l)"
                 unfolding InvS'_def lemmasFor_RecvGntE'_def lemmasFor_RecvGntS'_def lemmasFor_SendGntE'_def lemmasFor_SendGntS'_def lemmasFor_RecvInvAck1'_def lemmasFor_RecvInvAck2'_def lemmasFor_SendInvAck'_def lemmasFor_SendInv'_def lemmasFor_RecvReqE'_def lemmasFor_RecvReqS'_def lemmasFor_SendReqE'_def lemmasFor_SendReqS'_def using SafeAndderiveFormLemma_1' apply(auto      )    
 
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
    apply(case_tac   "x1 = ''ExGntd''")
    
    apply(subgoal_tac   "formEval (initSpec6) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x1 = ''CurCmd''")
    
    apply(subgoal_tac   "formEval (initSpec7) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x1 = ''CurPtr''")
    
    apply(subgoal_tac   "formEval (initSpec8 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
      apply(auto      )    
     done
  
  subgoal for v x21 x22
    apply(case_tac   "x21 = ''Chan1.Cmd''")
    
    apply(subgoal_tac   "formEval (initSpec0 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x21 = ''Chan2.Cmd''")
    
    apply(subgoal_tac   "formEval (initSpec1 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x21 = ''Chan3.Cmd''")
    
    apply(subgoal_tac   "formEval (initSpec2 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x21 = ''Cache.State''")
    
    apply(subgoal_tac   "formEval (initSpec3 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x21 = ''InvSet''")
    
    apply(subgoal_tac   "formEval (initSpec4 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
    apply(case_tac   "x21 = ''ShrSet''")
    
    apply(subgoal_tac   "formEval (initSpec5 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
      apply(auto      )    
     done
  
    apply(auto      )    
   done

subgoal for r sk
  unfolding rule_refs_def  apply(auto intro: Un_iff lemmaRecvGntE_fitEnv lemmaRecvGntS_fitEnv lemmaSendGntE_fitEnv lemmaSendGntS_fitEnv lemmaRecvInvAck1_fitEnv lemmaRecvInvAck2_fitEnv lemmaSendInvAck_fitEnv lemmaSendInv_fitEnv lemmaRecvReqE_fitEnv lemmaRecvReqS_fitEnv lemmaSendReqE_fitEnv lemmaSendReqS_fitEnv     )    
   done

done

lemma absProtSim : 
                  "[|M < N;M = 1;isProtObsInvSet (ABS_rules M) (absTransfForm (env N) M ` allInitSpecs N) (set (InvS' N)) M (env N)|] 
                 ==> isParamProtInvSet (rules N) (allInitSpecs N) (set (InvS N)) N"
                   apply(rule_tac ?rs2.0 = "rule_refs N" and env="env N" and S="set (InvS N)" and S'="set (InvS' N)" and M=M and absRules="ABS_rules M" in CMP)
subgoal for r
   using wellFormedRule_refs apply(auto      )    
   done

subgoal  unfolding InvS'_def lemmasFor_RecvGntE'_def lemmasFor_RecvGntS'_def lemmasFor_SendGntE'_def lemmasFor_SendGntS'_def lemmasFor_RecvInvAck1'_def lemmasFor_RecvInvAck2'_def lemmasFor_SendInvAck'_def lemmasFor_SendInv'_def lemmasFor_RecvReqE'_def lemmasFor_RecvReqS'_def lemmasFor_SendReqE'_def lemmasFor_SendReqS'_def using symInvs apply(auto      )    
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
   
  subgoal   using strengthenVsObsLs_lemmasFor_RecvGntE apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_RecvGntS apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_SendGntE apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_SendGntS apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_RecvInvAck1 apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_RecvInvAck2 apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_SendInvAck apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_SendInv apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_RecvReqE apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_RecvReqS apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_SendReqE apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_SendReqS apply(auto      )    
     done
  done

   apply(rule equivRuleSetReflex)
 using ABS_all  apply(auto      )    
 
done

end
