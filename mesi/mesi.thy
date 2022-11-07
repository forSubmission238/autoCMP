
theory mesi
  imports ECMP
begin

definition MM :: "scalrValueType" where [simp]:
 "MM \<equiv> enum ''LOCATION'' ''MM''"

definition E :: "scalrValueType" where [simp]:
 "E \<equiv> enum ''LOCATION'' ''E''"

definition S :: "scalrValueType" where [simp]:
 "S \<equiv> enum ''LOCATION'' ''S''"

definition I :: "scalrValueType" where [simp]:
 "I \<equiv> enum ''LOCATION'' ''I''"

definition true :: "scalrValueType" where [simp]:
 "true \<equiv> boolV True"

definition false :: "scalrValueType" where [simp]:
 "false \<equiv> boolV False"

primrec env :: "nat => envType" where
"env N (Ident n) = anyType"|
"env N (Para n i) = (if Para n i = Para ''state'' i \<and> (i \<le> N) then
  enumType
else
  anyType
)"|
"env N dontCareVar = anyType"

lemma env_simp : 
 "[|i <= N|] ==> env N (Para ''state'' i) = enumType"
 

"[|i > N|] ==> env N (Para n i) = anyType"
 
 
   apply(auto      )    
 
done

definition initSpec0 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec0 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''state'' i) =\<^sub>f Const I) N"

lemma symPreds0 [intro]: 
 "  symPredSet' N {initSpec0 N}"
 unfolding initSpec0_def   apply(rule symPredSetForall)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma deriveFormInitSpec0 [intro]: 
 "[|f : {initSpec0 N}|] ==> deriveForm (env N) f"
   apply(auto      )    
 
done

definition allInitSpecs :: "nat \<Rightarrow> formula set" where [simp]:
 "allInitSpecs N \<equiv> {initSpec0 N}"

lemma symPreds [intro]: 
 "  symPredSet' N (allInitSpecs N)"
 unfolding allInitSpecs_def  apply(blast      )

done

lemma deriveFormAllInitSpec : 
 "[|f : allInitSpecs N|] ==> deriveForm (env N) f"
  using deriveFormInitSpec0 apply(auto      simp del: initSpec0_def)    
 
done

definition t1 :: "nat \<Rightarrow> rule" where
 "t1 i \<equiv> 
   IVar (Para ''state'' i) =\<^sub>f Const E
  \<triangleright>
   assign (Para ''state'' i, Const MM)"

lemma symt1 : 
 "  symParamRule N t1"
 

"[|i <= N|] ==> wellFormedRule (env N) N (t1 i)"
 
 
 unfolding t1_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition t1s :: "nat \<Rightarrow> rule set" where
 "t1s N \<equiv> oneParamCons N t1"

definition t2 :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "t2 N i \<equiv> 
   IVar (Para ''state'' i) =\<^sub>f Const I
  \<triangleright>
   assign (Para ''state'' i, Const S) ||
   forallStmExcl (\<lambda>j. assign (Para ''state'' j, iteForm (IVar (Para ''state'' j) =\<^sub>f Const I) (Const I) (Const S))) i N"

lemma symt2 : 
 "  symParamRule N (t2 N)"
 

"[|i <= N|] ==> wellFormedRule (env N) N (t2 N i)"
 
 
 unfolding t2_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition t2s :: "nat \<Rightarrow> rule set" where
 "t2s N \<equiv> oneParamCons N (t2 N)"

definition t3 :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "t3 N i \<equiv> 
   IVar (Para ''state'' i) =\<^sub>f Const S
  \<triangleright>
   assign (Para ''state'' i, Const E) ||
   forallStmExcl (\<lambda>j. assign (Para ''state'' j, Const I)) i N"

lemma symt3 : 
 "  symParamRule N (t3 N)"
 

"[|i <= N|] ==> wellFormedRule (env N) N (t3 N i)"
 
 
 unfolding t3_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition t3s :: "nat \<Rightarrow> rule set" where
 "t3s N \<equiv> oneParamCons N (t3 N)"

definition t4 :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "t4 N i \<equiv> 
   IVar (Para ''state'' i) =\<^sub>f Const MM
  \<triangleright>
   assign (Para ''state'' i, Const E) ||
   forallStmExcl (\<lambda>j. assign (Para ''state'' j, Const I)) i N"

lemma symt4 : 
 "  symParamRule N (t4 N)"
 

"[|i <= N|] ==> wellFormedRule (env N) N (t4 N i)"
 
 
 unfolding t4_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition t4s :: "nat \<Rightarrow> rule set" where
 "t4s N \<equiv> oneParamCons N (t4 N)"

definition Mesi :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Mesi N i j \<equiv> \<not>\<^sub>f Const (index i) =\<^sub>f Const (index j) \<longrightarrow>\<^sub>f
  IVar (Para ''state'' i) =\<^sub>f Const MM \<longrightarrow>\<^sub>f
  \<not>\<^sub>f IVar (Para ''state'' j) =\<^sub>f Const MM"

definition ABS_t2 :: "nat \<Rightarrow> rule" where
 "ABS_t2 N \<equiv> 
   chaos
  \<triangleright>
   forallStm (\<lambda>j. assign (Para ''state'' j, iteForm (IVar (Para ''state'' j) =\<^sub>f Const I) (Const I) (Const S))) N"

definition ABS_t2s :: "nat \<Rightarrow> rule set" where
 "ABS_t2s N \<equiv> {ABS_t2 N}"

definition ABS_t3 :: "nat \<Rightarrow> rule" where
 "ABS_t3 N \<equiv> 
   (\<forall>\<^sub>fj. \<not>\<^sub>f IVar (Para ''state'' j) =\<^sub>f Const E) N \<and>\<^sub>f
   (\<forall>\<^sub>fj. \<not>\<^sub>f IVar (Para ''state'' j) =\<^sub>f Const MM) N
  \<triangleright>
   forallStm (\<lambda>j. assign (Para ''state'' j, Const I)) N"

definition ABS_t3s :: "nat \<Rightarrow> rule set" where
 "ABS_t3s N \<equiv> {ABS_t3 N}"

definition ABS_t4 :: "nat \<Rightarrow> rule" where
 "ABS_t4 N \<equiv> 
   (\<forall>\<^sub>fj. \<not>\<^sub>f IVar (Para ''state'' j) =\<^sub>f Const S) N \<and>\<^sub>f
   (\<forall>\<^sub>fj. \<not>\<^sub>f IVar (Para ''state'' j) =\<^sub>f Const E) N \<and>\<^sub>f
   (\<forall>\<^sub>fj. IVar (Para ''state'' j) =\<^sub>f Const I) N \<and>\<^sub>f
   (\<forall>\<^sub>fj. \<not>\<^sub>f IVar (Para ''state'' j) =\<^sub>f Const MM) N
  \<triangleright>
   forallStm (\<lambda>j. assign (Para ''state'' j, Const I)) N"

definition ABS_t4s :: "nat \<Rightarrow> rule set" where
 "ABS_t4s N \<equiv> {ABS_t4 N}"

definition Lemma_4 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_4 N p i \<equiv> IVar (Para ''state'' i) =\<^sub>f Const S \<longrightarrow>\<^sub>f
  forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''state'' j) =\<^sub>f Const MM) i N"

definition Lemma_6 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_6 N p i \<equiv> IVar (Para ''state'' i) =\<^sub>f Const MM \<longrightarrow>\<^sub>f
  forallFormExcl (\<lambda>j. IVar (Para ''state'' j) =\<^sub>f Const I) i N"

definition Lemma_0 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_0 N p i \<equiv> IVar (Para ''state'' i) =\<^sub>f Const MM \<longrightarrow>\<^sub>f
  forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''state'' j) =\<^sub>f Const MM) i N"

definition Lemma_3 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_3 N p i \<equiv> IVar (Para ''state'' i) =\<^sub>f Const MM \<longrightarrow>\<^sub>f
  forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''state'' j) =\<^sub>f Const E) i N"

definition Lemma_5 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_5 N p i \<equiv> IVar (Para ''state'' i) =\<^sub>f Const S \<longrightarrow>\<^sub>f
  forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''state'' j) =\<^sub>f Const E) i N"

definition Lemma_9 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_9 N p i \<equiv> IVar (Para ''state'' i) =\<^sub>f Const MM \<longrightarrow>\<^sub>f
  forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''state'' j) =\<^sub>f Const S) i N"

definition rules :: "nat \<Rightarrow> rule set" where
 "rules N = (t1s N \<union> (t2s N \<union> (t3s N \<union> t4s N)))"

lemma deriveAll : 
 "[|r : t1s N|] ==> deriveRule (env N) r"
 

"[|r : t2s N|] ==> deriveRule (env N) r"
 

"[|r : t3s N|] ==> deriveRule (env N) r"
 

"[|r : t4s N|] ==> deriveRule (env N) r"
 

"[|r : ABS_t2s N|] ==> deriveRule (env N) r"
 

"[|r : ABS_t3s N|] ==> deriveRule (env N) r"
 

"[|r : ABS_t4s N|] ==> deriveRule (env N) r"
 
 
 unfolding deriveRule_def deriveForm_def deriveStmt_def t1s_def t1_def t2s_def t2_def t3s_def t3_def t4s_def t4_def ABS_t2s_def ABS_t2_def ABS_t3s_def ABS_t3_def ABS_t4s_def ABS_t4_def  apply(auto      )    
 
done

lemma symProtAll : 
 "  symProtRules' N (t1s N)"
 

"  symProtRules' N (t2s N)"
 

"  symProtRules' N (t3s N)"
 

"  symProtRules' N (t4s N)"
 
 
  using symt1(1) t1s_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symt2(1) t2s_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symt3(1) t3s_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symt4(1) t4s_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
done

lemma symMesi : 
 "  symParamForm2 N (Mesi N)"
 unfolding Mesi_def  apply(auto      )    
 
  apply(intro  symParamForm2Imply symParamFormForallExcl2 )

unfolding symParamForm2_def  apply(auto      )    
 
done

lemma symLemma_4 : 
 "  symParamForm2 N (Lemma_4 N)"
 unfolding Lemma_4_def  apply(auto      )    
 
  apply(intro  symParamForm2Imply symParamFormForallExcl2 )

unfolding symParamForm2_def  apply(auto      )    
 
done

lemma symLemma_6 : 
 "  symParamForm2 N (Lemma_6 N)"
 unfolding Lemma_6_def  apply(auto      )    
 
  apply(intro  symParamForm2Imply symParamFormForallExcl2 )

unfolding symParamForm2_def  apply(auto      )    
 
done

lemma symLemma_0 : 
 "  symParamForm2 N (Lemma_0 N)"
 unfolding Lemma_0_def  apply(auto      )    
 
  apply(intro  symParamForm2Imply symParamFormForallExcl2 )

unfolding symParamForm2_def  apply(auto      )    
 
done

lemma symLemma_3 : 
 "  symParamForm2 N (Lemma_3 N)"
 unfolding Lemma_3_def  apply(auto      )    
 
  apply(intro  symParamForm2Imply symParamFormForallExcl2 )

unfolding symParamForm2_def  apply(auto      )    
 
done

lemma symLemma_5 : 
 "  symParamForm2 N (Lemma_5 N)"
 unfolding Lemma_5_def  apply(auto      )    
 
  apply(intro  symParamForm2Imply symParamFormForallExcl2 )

unfolding symParamForm2_def  apply(auto      )    
 
done

lemma symLemma_9 : 
 "  symParamForm2 N (Lemma_9 N)"
 unfolding Lemma_9_def  apply(auto      )    
 
  apply(intro  symParamForm2Imply symParamFormForallExcl2 )

unfolding symParamForm2_def  apply(auto      )    
 
done

definition lemmasFor_t1 :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_t1 N = []"

definition t1_ref :: "nat \<Rightarrow> rule" where
 "t1_ref i \<equiv> 
   IVar (Para ''state'' i) =\<^sub>f Const E
  \<triangleright>
   assign (Para ''state'' i, Const MM)"

lemma symt1_ref : 
 "  symParamRule N t1_ref"
 

"[|i <= N|] ==> wellFormedRule (env N) N (t1_ref i)"
 
 
 unfolding t1_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition t1_refs :: "nat \<Rightarrow> rule set" where
 "t1_refs N \<equiv> oneParamCons N t1_ref"

lemma t1_strengthen : 
 "  strengthenRuleByFrmL2 (map2' (lemmasFor_t1 N) j i) (t1 i) = t1_ref i"
 unfolding lemmasFor_t1_def  t1_def t1_ref_def  apply(auto      )    
 
done

lemma abs_t1_ref : 
 "[|M <= N;i <= M|] ==> absTransfRule (env N) M (t1_ref i) = t1_ref i"
 

"[|M <= N;i > M|] ==> absTransfRule (env N) M (t1_ref i) = skipRule"
 
 
 unfolding t1_ref_def t1_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_t2 :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_t2 N = []"

definition t2_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "t2_ref N i \<equiv> 
   IVar (Para ''state'' i) =\<^sub>f Const I
  \<triangleright>
   assign (Para ''state'' i, Const S) ||
   forallStmExcl (\<lambda>j. assign (Para ''state'' j, iteForm (IVar (Para ''state'' j) =\<^sub>f Const I) (Const I) (Const S))) i N"

lemma symt2_ref : 
 "  symParamRule N (t2_ref N)"
 

"[|i <= N|] ==> wellFormedRule (env N) N (t2_ref N i)"
 
 
 unfolding t2_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition t2_refs :: "nat \<Rightarrow> rule set" where
 "t2_refs N \<equiv> oneParamCons N (t2_ref N)"

lemma t2_strengthen : 
 "  strengthenRuleByFrmL2 (map2' (lemmasFor_t2 N) j i) (t2 N i) = t2_ref N i"
 unfolding lemmasFor_t2_def  t2_def t2_ref_def  apply(auto      )    
 
done

lemma abs_t2_ref : 
 "[|M <= N;i <= M|] ==> absTransfRule (env N) M (t2_ref N i) = t2_ref M i"
 

"[|M <= N;i > M|] ==> absTransfRule (env N) M (t2_ref N i) = ABS_t2 M"
 
 
 unfolding t2_ref_def t2_ref_def ABS_t2_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_t3 :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_t3 N = [Lemma_4 N, Lemma_5 N]"

definition t3_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "t3_ref N i \<equiv> 
   IVar (Para ''state'' i) =\<^sub>f Const S \<and>\<^sub>f
   forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''state'' j) =\<^sub>f Const E) i N \<and>\<^sub>f
   forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''state'' j) =\<^sub>f Const MM) i N
  \<triangleright>
   assign (Para ''state'' i, Const E) ||
   forallStmExcl (\<lambda>j. assign (Para ''state'' j, Const I)) i N"

lemma symt3_ref : 
 "  symParamRule N (t3_ref N)"
 

"[|i <= N|] ==> wellFormedRule (env N) N (t3_ref N i)"
 
 
 unfolding t3_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition t3_refs :: "nat \<Rightarrow> rule set" where
 "t3_refs N \<equiv> oneParamCons N (t3_ref N)"

lemma t3_strengthen : 
 "  strengthenRuleByFrmL2 (map2' (lemmasFor_t3 N) j i) (t3 N i) = t3_ref N i"
 unfolding lemmasFor_t3_def Lemma_4_def Lemma_5_def t3_def t3_ref_def  apply(auto      )    
 
done

lemma abs_t3_ref : 
 "[|M <= N;i <= M|] ==> absTransfRule (env N) M (t3_ref N i) = t3_ref M i"
 

"[|M <= N;i > M|] ==> absTransfRule (env N) M (t3_ref N i) = ABS_t3 M"
 
 
 unfolding t3_ref_def t3_ref_def ABS_t3_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_t4 :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_t4 N = [Lemma_0 N, Lemma_6 N, Lemma_3 N, Lemma_9 N]"

definition t4_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "t4_ref N i \<equiv> 
   IVar (Para ''state'' i) =\<^sub>f Const MM \<and>\<^sub>f
   forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''state'' j) =\<^sub>f Const S) i N \<and>\<^sub>f
   forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''state'' j) =\<^sub>f Const E) i N \<and>\<^sub>f
   forallFormExcl (\<lambda>j. IVar (Para ''state'' j) =\<^sub>f Const I) i N \<and>\<^sub>f
   forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''state'' j) =\<^sub>f Const MM) i N
  \<triangleright>
   assign (Para ''state'' i, Const E) ||
   forallStmExcl (\<lambda>j. assign (Para ''state'' j, Const I)) i N"

lemma symt4_ref : 
 "  symParamRule N (t4_ref N)"
 

"[|i <= N|] ==> wellFormedRule (env N) N (t4_ref N i)"
 
 
 unfolding t4_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition t4_refs :: "nat \<Rightarrow> rule set" where
 "t4_refs N \<equiv> oneParamCons N (t4_ref N)"

lemma t4_strengthen : 
 "  strengthenRuleByFrmL2 (map2' (lemmasFor_t4 N) j i) (t4 N i) = t4_ref N i"
 unfolding lemmasFor_t4_def Lemma_0_def Lemma_6_def Lemma_3_def Lemma_9_def t4_def t4_ref_def  apply(auto      )    
 
done

lemma abs_t4_ref : 
 "[|M <= N;i <= M|] ==> absTransfRule (env N) M (t4_ref N i) = t4_ref M i"
 

"[|M <= N;i > M|] ==> absTransfRule (env N) M (t4_ref N i) = ABS_t4 M"
 
 
 unfolding t4_ref_def t4_ref_def ABS_t4_def  apply(auto     simp add: Let_def )    
 
done

definition InvS :: "nat \<Rightarrow> (((nat \<Rightarrow> nat \<Rightarrow> formula) list) list)" where
 "InvS N = [lemmasFor_t1 N, lemmasFor_t2 N, lemmasFor_t3 N, lemmasFor_t4 N]"

definition rule_refs :: "nat \<Rightarrow> rule set" where
 "rule_refs N = (t1_refs N \<union> (t2_refs N \<union> (t3_refs N \<union> t4_refs N)))"

lemma t1StrengthRel : 
 "  strengthenRel (t1s N) (set (InvS N)) (t1_refs N) N"
 unfolding t1s_def t1_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_t1" in strengthenExt1)
 using t1_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma t2StrengthRel : 
 "  strengthenRel (t2s N) (set (InvS N)) (t2_refs N) N"
 unfolding t2s_def t2_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_t2" in strengthenExt1)
 using t2_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma t3StrengthRel : 
 "  strengthenRel (t3s N) (set (InvS N)) (t3_refs N) N"
 unfolding t3s_def t3_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_t3" in strengthenExt1)
 using t3_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma t4StrengthRel : 
 "  strengthenRel (t4s N) (set (InvS N)) (t4_refs N) N"
 unfolding t4s_def t4_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_t4" in strengthenExt1)
 using t4_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma deriveAllRef : 
 "[|r : t1_refs N|] ==> deriveRule (env N) r"
 

"[|r : t2_refs N|] ==> deriveRule (env N) r"
 

"[|r : t3_refs N|] ==> deriveRule (env N) r"
 

"[|r : t4_refs N|] ==> deriveRule (env N) r"
 
 
 unfolding deriveRule_def deriveForm_def deriveStmt_def t1_refs_def t1_ref_def t2_refs_def t2_ref_def t3_refs_def t3_ref_def t4_refs_def t4_ref_def  apply(auto      )    
 
done

lemma symProtAllRef : 
 "  symProtRules' N (t1_refs N)"
 

"  symProtRules' N (t2_refs N)"
 

"  symProtRules' N (t3_refs N)"
 

"  symProtRules' N (t4_refs N)"
 
 
  using symt1_ref(1) t1_refs_def symt2_ref(1) t2_refs_def symt3_ref(1) t3_refs_def symt4_ref(1) t4_refs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )    
 
done

lemma StrengthRelRules2Rule_refs : 
 "  strengthenRel (rules N) (set (InvS N)) (rule_refs N) N"
 unfolding rules_def rule_refs_def   apply(rule strenRelUnion)
  apply(blast intro: t1StrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: t2StrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: t3StrengthRel     )

  apply(blast intro: t4StrengthRel     )

done

lemma Abs_t1_refs : 
 "[|M < N|] ==> (absTransfRule (env N) M ` t1_refs N) = (t1_refs M Un {skipRule})"
 unfolding t1_refs_def   apply(rule absGen)
 using abs_t1_ref apply(auto      )    
 
done

lemma Abs_t2_refs : 
 "[|M < N|] ==> (absTransfRule (env N) M ` t2_refs N) = (t2_refs M Un ABS_t2s M)"
 unfolding t2_refs_def ABS_t2s_def   apply(rule absGen)
 using abs_t2_ref apply(auto      )    
 
done

lemma Abs_t3_refs : 
 "[|M < N|] ==> (absTransfRule (env N) M ` t3_refs N) = (t3_refs M Un ABS_t3s M)"
 unfolding t3_refs_def ABS_t3s_def   apply(rule absGen)
 using abs_t3_ref apply(auto      )    
 
done

lemma Abs_t4_refs : 
 "[|M < N|] ==> (absTransfRule (env N) M ` t4_refs N) = (t4_refs M Un ABS_t4s M)"
 unfolding t4_refs_def ABS_t4s_def   apply(rule absGen)
 using abs_t4_ref apply(auto      )    
 
done

definition ABS_rules :: "nat \<Rightarrow> rule set" where [simp]:
 "ABS_rules N = (t1_refs N \<union> (t2_refs N \<union> (ABS_t2s N \<union> (t3_refs N \<union> (ABS_t3s N \<union> (t4_refs N \<union> (ABS_t4s N \<union> {skipRule})))))))"

definition ABS_rules' :: "nat \<Rightarrow> rule set" where [simp]:
 "ABS_rules' N = ((t1_refs N \<union> {skipRule}) \<union> ((t2_refs N \<union> ABS_t2s N) \<union> ((t3_refs N \<union> ABS_t3s N) \<union> (t4_refs N \<union> ABS_t4s N))))"

lemma ABS_rules_eq_rules' : 
 "  ABS_rules M = ABS_rules' M"
   apply(auto      )    
 
done

lemma ABS_all : 
 "[|M < N|] ==> (absTransfRule (env N) M ` rule_refs N) = ABS_rules M"
   apply(subst ABS_rules_eq_rules'       )

unfolding rule_refs_def ABS_rules'_def  apply(intro  image_UnI )

  apply(auto     simp add: Abs_t1_refs Abs_t2_refs Abs_t3_refs Abs_t4_refs )    
 
done

definition Lemma_4' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_4' N i j \<equiv> \<not>\<^sub>f Const (index i) =\<^sub>f Const (index j) \<and>\<^sub>f
  IVar (Para ''state'' i) =\<^sub>f Const S \<longrightarrow>\<^sub>f
  \<not>\<^sub>f IVar (Para ''state'' j) =\<^sub>f Const MM"

lemma absTransfLemma_4' : 
 "[|M < N;M = 1;l <= 1|] ==> absTransfForm (env N) M (Lemma_4' N 0 l) = Lemma_4' N 0 l"
 unfolding Lemma_4'_def  apply(auto      )    
 
done

lemma strengthenVsObsLemma_4 : 
 "  strengthenVsObs (Lemma_4 N) (Lemma_4' N) N"
 unfolding Lemma_4_def Lemma_4'_def   apply(rule strengthenVsObsDiff)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma SafeAndderiveFormLemma_4' : 
 "[|M < N;M = 1;l <= M;k <= M|] ==> safeForm (env N) M (Lemma_4' N k l) & deriveForm (env N) (Lemma_4' N k l)"
 unfolding Lemma_4'_def  apply(auto      )    
 
done

definition Lemma_6' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_6' N i j \<equiv> \<not>\<^sub>f Const (index i) =\<^sub>f Const (index j) \<and>\<^sub>f
  IVar (Para ''state'' i) =\<^sub>f Const MM \<longrightarrow>\<^sub>f
  IVar (Para ''state'' j) =\<^sub>f Const I"

lemma absTransfLemma_6' : 
 "[|M < N;M = 1;l <= 1|] ==> absTransfForm (env N) M (Lemma_6' N 0 l) = Lemma_6' N 0 l"
 unfolding Lemma_6'_def  apply(auto      )    
 
done

lemma strengthenVsObsLemma_6 : 
 "  strengthenVsObs (Lemma_6 N) (Lemma_6' N) N"
 unfolding Lemma_6_def Lemma_6'_def   apply(rule strengthenVsObsDiff)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma SafeAndderiveFormLemma_6' : 
 "[|M < N;M = 1;l <= M;k <= M|] ==> safeForm (env N) M (Lemma_6' N k l) & deriveForm (env N) (Lemma_6' N k l)"
 unfolding Lemma_6'_def  apply(auto      )    
 
done

definition Lemma_0' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_0' N i j \<equiv> \<not>\<^sub>f Const (index i) =\<^sub>f Const (index j) \<and>\<^sub>f
  IVar (Para ''state'' i) =\<^sub>f Const MM \<longrightarrow>\<^sub>f
  \<not>\<^sub>f IVar (Para ''state'' j) =\<^sub>f Const MM"

lemma absTransfLemma_0' : 
 "[|M < N;M = 1;l <= 1|] ==> absTransfForm (env N) M (Lemma_0' N 0 l) = Lemma_0' N 0 l"
 unfolding Lemma_0'_def  apply(auto      )    
 
done

lemma strengthenVsObsLemma_0 : 
 "  strengthenVsObs (Lemma_0 N) (Lemma_0' N) N"
 unfolding Lemma_0_def Lemma_0'_def   apply(rule strengthenVsObsDiff)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma SafeAndderiveFormLemma_0' : 
 "[|M < N;M = 1;l <= M;k <= M|] ==> safeForm (env N) M (Lemma_0' N k l) & deriveForm (env N) (Lemma_0' N k l)"
 unfolding Lemma_0'_def  apply(auto      )    
 
done

definition Lemma_3' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_3' N i j \<equiv> \<not>\<^sub>f Const (index i) =\<^sub>f Const (index j) \<and>\<^sub>f
  IVar (Para ''state'' i) =\<^sub>f Const MM \<longrightarrow>\<^sub>f
  \<not>\<^sub>f IVar (Para ''state'' j) =\<^sub>f Const E"

lemma absTransfLemma_3' : 
 "[|M < N;M = 1;l <= 1|] ==> absTransfForm (env N) M (Lemma_3' N 0 l) = Lemma_3' N 0 l"
 unfolding Lemma_3'_def  apply(auto      )    
 
done

lemma strengthenVsObsLemma_3 : 
 "  strengthenVsObs (Lemma_3 N) (Lemma_3' N) N"
 unfolding Lemma_3_def Lemma_3'_def   apply(rule strengthenVsObsDiff)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma SafeAndderiveFormLemma_3' : 
 "[|M < N;M = 1;l <= M;k <= M|] ==> safeForm (env N) M (Lemma_3' N k l) & deriveForm (env N) (Lemma_3' N k l)"
 unfolding Lemma_3'_def  apply(auto      )    
 
done

definition Lemma_5' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_5' N i j \<equiv> \<not>\<^sub>f Const (index i) =\<^sub>f Const (index j) \<and>\<^sub>f
  IVar (Para ''state'' i) =\<^sub>f Const S \<longrightarrow>\<^sub>f
  \<not>\<^sub>f IVar (Para ''state'' j) =\<^sub>f Const E"

lemma absTransfLemma_5' : 
 "[|M < N;M = 1;l <= 1|] ==> absTransfForm (env N) M (Lemma_5' N 0 l) = Lemma_5' N 0 l"
 unfolding Lemma_5'_def  apply(auto      )    
 
done

lemma strengthenVsObsLemma_5 : 
 "  strengthenVsObs (Lemma_5 N) (Lemma_5' N) N"
 unfolding Lemma_5_def Lemma_5'_def   apply(rule strengthenVsObsDiff)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma SafeAndderiveFormLemma_5' : 
 "[|M < N;M = 1;l <= M;k <= M|] ==> safeForm (env N) M (Lemma_5' N k l) & deriveForm (env N) (Lemma_5' N k l)"
 unfolding Lemma_5'_def  apply(auto      )    
 
done

definition Lemma_9' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_9' N i j \<equiv> \<not>\<^sub>f Const (index i) =\<^sub>f Const (index j) \<and>\<^sub>f
  IVar (Para ''state'' i) =\<^sub>f Const MM \<longrightarrow>\<^sub>f
  \<not>\<^sub>f IVar (Para ''state'' j) =\<^sub>f Const S"

lemma absTransfLemma_9' : 
 "[|M < N;M = 1;l <= 1|] ==> absTransfForm (env N) M (Lemma_9' N 0 l) = Lemma_9' N 0 l"
 unfolding Lemma_9'_def  apply(auto      )    
 
done

lemma strengthenVsObsLemma_9 : 
 "  strengthenVsObs (Lemma_9 N) (Lemma_9' N) N"
 unfolding Lemma_9_def Lemma_9'_def   apply(rule strengthenVsObsDiff)
unfolding symParamForm_def  apply(auto      )    
 
done

lemma SafeAndderiveFormLemma_9' : 
 "[|M < N;M = 1;l <= M;k <= M|] ==> safeForm (env N) M (Lemma_9' N k l) & deriveForm (env N) (Lemma_9' N k l)"
 unfolding Lemma_9'_def  apply(auto      )    
 
done

lemma symInvs : 
 "  symParamForm2 N (Lemma_4' N)"
 

"  symParamForm2 N (Lemma_6' N)"
 

"  symParamForm2 N (Lemma_0' N)"
 

"  symParamForm2 N (Lemma_3' N)"
 

"  symParamForm2 N (Lemma_5' N)"
 

"  symParamForm2 N (Lemma_9' N)"
 
 
 unfolding Lemma_4'_def Lemma_6'_def Lemma_0'_def Lemma_3'_def Lemma_5'_def Lemma_9'_def  apply(auto      )    
 
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

definition lemmasFor_t1' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_t1' N = []"

lemma strengthenVsObsLs_lemmasFor_t1 : 
 "  strengthenVsObsLs (lemmasFor_t1 N) (lemmasFor_t1' N) N"
 unfolding strengthenVsObsLs_def lemmasFor_t1_def lemmasFor_t1'_def  apply(auto      )    
 
done

lemma lemmat1_fitEnv : 
 "[|formEval (pre r) s;fitEnv s (env N);r : t1_refs N|] ==> fitEnv (trans1 (act r) s) (env N)"
 unfolding t1_refs_def t1_ref_def  apply(auto      )    
 
done

definition lemmasFor_t2' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_t2' N = []"

lemma strengthenVsObsLs_lemmasFor_t2 : 
 "  strengthenVsObsLs (lemmasFor_t2 N) (lemmasFor_t2' N) N"
 unfolding strengthenVsObsLs_def lemmasFor_t2_def lemmasFor_t2'_def  apply(auto      )    
 
done

lemma lemmat2_fitEnv : 
 "[|formEval (pre r) s;fitEnv s (env N);r : t2_refs N|] ==> fitEnv (trans1 (act r) s) (env N)"
 unfolding t2_refs_def t2_ref_def  apply(auto      )    
 
done

definition lemmasFor_t3' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_t3' N = [Lemma_4' N, Lemma_5' N]"

lemma strengthenVsObsLs_lemmasFor_t3 : 
 "  strengthenVsObsLs (lemmasFor_t3 N) (lemmasFor_t3' N) N"
 unfolding strengthenVsObsLs_def lemmasFor_t3_def lemmasFor_t3'_def  apply(auto intro: strengthenVsObsLemma_4 strengthenVsObsLemma_5     )    
 
done

lemma lemmat3_fitEnv : 
 "[|formEval (pre r) s;fitEnv s (env N);r : t3_refs N|] ==> fitEnv (trans1 (act r) s) (env N)"
 unfolding t3_refs_def t3_ref_def  apply(auto      )    
 
done

definition lemmasFor_t4' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_t4' N = [Lemma_0' N, Lemma_6' N, Lemma_3' N, Lemma_9' N]"

lemma strengthenVsObsLs_lemmasFor_t4 : 
 "  strengthenVsObsLs (lemmasFor_t4 N) (lemmasFor_t4' N) N"
 unfolding strengthenVsObsLs_def lemmasFor_t4_def lemmasFor_t4'_def  apply(auto intro: strengthenVsObsLemma_0 strengthenVsObsLemma_6 strengthenVsObsLemma_3 strengthenVsObsLemma_9     )    
 
done

lemma lemmat4_fitEnv : 
 "[|formEval (pre r) s;fitEnv s (env N);r : t4_refs N|] ==> fitEnv (trans1 (act r) s) (env N)"
 unfolding t4_refs_def t4_ref_def  apply(auto      )    
 
done

definition InvS' :: "nat \<Rightarrow> (((nat \<Rightarrow> nat \<Rightarrow> formula) list) list)" where
 "InvS' N = [lemmasFor_t1' N, lemmasFor_t2' N, lemmasFor_t3' N, lemmasFor_t4' N]"

lemma wellFormedRule_refs : 
 "[|r : rule_refs N|] ==> wellFormedRule (env N) N r"
   apply(auto     simp add: rule_refs_def   t1_refs_def t2_refs_def t3_refs_def t4_refs_def symt1_ref symt2_ref symt3_ref symt4_ref )    
 
done

lemma SafeAndderiveAll : 
 "[|M < N;M = 1;l <= M;k <= M;pinvL : set (InvS' N);pf : set pinvL|] ==> safeForm (env N) M (pf k l) & deriveForm (env N) (pf k l)"
 unfolding InvS'_def lemmasFor_t1'_def lemmasFor_t2'_def lemmasFor_t3'_def lemmasFor_t4'_def using SafeAndderiveFormLemma_4' SafeAndderiveFormLemma_6' SafeAndderiveFormLemma_0' SafeAndderiveFormLemma_3' SafeAndderiveFormLemma_5' SafeAndderiveFormLemma_9' apply(auto      )    
 
done

lemma rulesIsSym : 
 "  symProtRules' N (rules N)"
 unfolding rules_def   apply(rule symProtRulesUnion, blast intro:symProtAll)+
unfolding rules_def  apply(blast intro: symProtAll     )

done

lemma rule_refsIsSym : 
 "  symProtRules' N (rule_refs N)"
 unfolding rule_refs_def   apply(rule symProtRulesUnion, blast intro:symProtAllRef)+
unfolding rule_refs_def  apply(blast intro: symProtAllRef     )

done

lemma rule_refsWellTyped : 
 "[|r : rule_refs N|] ==> deriveRule (env N) r"
 unfolding rule_refs_def using deriveAllRef apply(auto      )    
 
done

lemma ReachStafitEnv : 
 "[|reachableUpTo (allInitSpecs N) (rule_refs N) k s|] ==> fitEnv s (env N)"
   apply(erule invIntro1)
subgoal for s0
  unfolding fitEnv_def   apply(rule allI)
     apply(rule impI)
  apply(case_tac   "v")
  
  subgoal for v x1
      apply(auto      )    
     done
  
  subgoal for v x21 x22
    apply(case_tac   "x21 = ''state''")
    
    apply(subgoal_tac   "formEval (initSpec0 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
      apply(auto      )    
     done
  
    apply(auto      )    
   done

subgoal for r sk
  unfolding rule_refs_def  apply(auto intro: Un_iff lemmat1_fitEnv lemmat2_fitEnv lemmat3_fitEnv lemmat4_fitEnv     )    
   done

done

lemma absProtSim : 
 "[|M < N;M = 1;isProtObsInvSet (ABS_rules M) (absTransfForm (env N) M ` allInitSpecs N) (set (InvS' N)) M (env N)|] ==> isParamProtInvSet (rules N) (allInitSpecs N) (set (InvS N)) N"
   apply(rule_tac ?rs2.0 = "rule_refs N" and env="env N" and S="set (InvS N)" and S'="set (InvS' N)" and M=M and absRules="ABS_rules M" in CMP)
subgoal for r
   using wellFormedRule_refs apply(auto      )    
   done

subgoal  unfolding InvS'_def lemmasFor_t1'_def lemmasFor_t2'_def lemmasFor_t3'_def lemmasFor_t4'_def using symInvs apply(auto      )    
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
   
  subgoal   using strengthenVsObsLs_lemmasFor_t1 apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_t2 apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_t3 apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_t4 apply(auto      )    
     done
  done

   apply(rule equivRuleSetReflex)
 using ABS_all  apply(auto      )    
 
done

end
