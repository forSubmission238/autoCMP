
theory mutualEx
  imports ECMP
begin

definition I :: "scalrValueType" where [simp]:
 "I \<equiv> enum ''state'' ''I''"

definition T :: "scalrValueType" where [simp]:
 "T \<equiv> enum ''state'' ''T''"

definition C :: "scalrValueType" where [simp]:
 "C \<equiv> enum ''state'' ''C''"

definition E :: "scalrValueType" where [simp]:
 "E \<equiv> enum ''state'' ''E''"

definition true :: "scalrValueType" where [simp]:
 "true \<equiv> boolV True"

definition false :: "scalrValueType" where [simp]:
 "false \<equiv> boolV False"

primrec env :: "nat => envType" where
"env N (Ident n) = (if Ident n = Ident ''x'' then
  boolType
else
  anyType
)"|
"env N (Para n i) = (if Para n i = Para ''n'' i \<and> (i \<le> N) then
  enumType
else
  anyType
)"|
"env N dontCareVar = anyType"

lemma env_simp : 
             "[|i <= N|] 
                 ==> env N (Para ''n'' i) = enumType"
                 

" 
                  env N (Ident ''x'') = boolType"
                 

"[|i > N|] 
                 ==> env N (Para n i) = anyType"
                 
 
               apply(auto      )    
 
done

definition initSpec0 :: "nat \<Rightarrow> formula" where [simp]:
 "initSpec0 N \<equiv> (\<forall>\<^sub>fi. IVar (Para ''n'' i) =\<^sub>f Const I) N"

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

definition initSpec1 :: "formula" where [simp]:
 "initSpec1 \<equiv> IVar (Ident ''x'') =\<^sub>f Const true"

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

definition allInitSpecs :: "nat \<Rightarrow> formula set" where [simp]:
 "allInitSpecs N \<equiv> {initSpec0 N} \<union> {initSpec1}"

lemma symPreds [intro]: 
                  " 
                  symPredSet' N (allInitSpecs N)"
                 unfolding allInitSpecs_def   apply(rule symPredsUnion)
  apply(blast      )

  apply(blast      )

done

lemma deriveFormAllInitSpec : 
                  "[|f : allInitSpecs N|] 
                 ==> deriveForm (env N) f"
                  using deriveFormInitSpec0 deriveFormInitSpec1 apply(auto      simp del: initSpec0_def initSpec1_def)    
 
done

definition Try :: "nat \<Rightarrow> rule" where
 "Try i \<equiv> 
   IVar (Para ''n'' i) =\<^sub>f Const I
  \<triangleright>
   assign (Para ''n'' i, Const T)"

lemma symTry : 
             " 
                  symParamRule N Try"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (Try i)"
                 
 
             unfolding Try_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition Trys :: "nat \<Rightarrow> rule set" where
 "Trys N \<equiv> oneParamCons N Try"

definition Crit :: "nat \<Rightarrow> rule" where
 "Crit i \<equiv> 
   IVar (Para ''n'' i) =\<^sub>f Const T \<and>\<^sub>f
   IVar (Ident ''x'') =\<^sub>f Const true
  \<triangleright>
   assign (Para ''n'' i, Const C) ||
   assign (Ident ''x'', Const false)"

lemma symCrit : 
             " 
                  symParamRule N Crit"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (Crit i)"
                 
 
             unfolding Crit_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition Crits :: "nat \<Rightarrow> rule set" where
 "Crits N \<equiv> oneParamCons N Crit"

definition Exit :: "nat \<Rightarrow> rule" where
 "Exit i \<equiv> 
   IVar (Para ''n'' i) =\<^sub>f Const C
  \<triangleright>
   assign (Para ''n'' i, Const E)"

lemma symExit : 
             " 
                  symParamRule N Exit"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (Exit i)"
                 
 
             unfolding Exit_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition Exits :: "nat \<Rightarrow> rule set" where
 "Exits N \<equiv> oneParamCons N Exit"

definition Idle :: "nat \<Rightarrow> rule" where
 "Idle i \<equiv> 
   IVar (Para ''n'' i) =\<^sub>f Const E
  \<triangleright>
   assign (Para ''n'' i, Const I) ||
   assign (Ident ''x'', Const true)"

lemma symIdle : 
             " 
                  symParamRule N Idle"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (Idle i)"
                 
 
             unfolding Idle_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition Idles :: "nat \<Rightarrow> rule set" where
 "Idles N \<equiv> oneParamCons N Idle"

definition mutualEx :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "mutualEx N i j \<equiv> \<not>\<^sub>f Const (index i) =\<^sub>f Const (index j) \<longrightarrow>\<^sub>f
  IVar (Para ''n'' i) =\<^sub>f Const C \<longrightarrow>\<^sub>f
  \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const C"

definition ABS_Crit :: "rule" where
 "ABS_Crit \<equiv> 
   IVar (Ident ''x'') =\<^sub>f Const true
  \<triangleright>
   assign (Ident ''x'', Const false)"

definition ABS_Crits :: "rule set" where
 "ABS_Crits \<equiv> {ABS_Crit}"

definition ABS_Idle :: "nat \<Rightarrow> rule" where
 "ABS_Idle N \<equiv> 
   (\<forall>\<^sub>fj. \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const C \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const E) N
  \<triangleright>
   assign (Ident ''x'', Const true)"

definition ABS_Idles :: "nat \<Rightarrow> rule set" where
 "ABS_Idles N \<equiv> {ABS_Idle N}"

definition Lemma_1 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_1 N p i \<equiv> IVar (Para ''n'' i) =\<^sub>f Const E \<longrightarrow>\<^sub>f
  forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const C \<and>\<^sub>f
  \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const E) i N"

definition rules :: "nat \<Rightarrow> rule set" where
 "rules N = (Trys N \<union> (Crits N \<union> (Exits N \<union> Idles N)))"

lemma deriveAll : 
             "[|r : Trys N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : Crits N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : Exits N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : Idles N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_Crits|] 
                 ==> deriveRule (env N) r"
                 

"[|r : ABS_Idles N|] 
                 ==> deriveRule (env N) r"
                 
 
             unfolding deriveRule_def deriveForm_def deriveStmt_def Trys_def Try_def Crits_def Crit_def Exits_def Exit_def Idles_def Idle_def ABS_Crits_def ABS_Crit_def ABS_Idles_def ABS_Idle_def  apply(auto      )    
 
done

lemma symProtAll : 
             " 
                  symProtRules' N (Trys N)"
                 

" 
                  symProtRules' N (Crits N)"
                 

" 
                  symProtRules' N (Exits N)"
                 

" 
                  symProtRules' N (Idles N)"
                 
 
              using symTry(1) Trys_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symCrit(1) Crits_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symExit(1) Exits_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
 using symIdle(1) Idles_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )[1]    
 
done

lemma symmutualEx : 
                  " 
                  symParamForm2 N (mutualEx N)"
                 unfolding mutualEx_def  apply(auto      )    
 
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

definition lemmasFor_Try :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_Try N = []"

definition Try_ref :: "nat \<Rightarrow> rule" where
 "Try_ref i \<equiv> 
   IVar (Para ''n'' i) =\<^sub>f Const I
  \<triangleright>
   assign (Para ''n'' i, Const T)"

lemma symTry_ref : 
             " 
                  symParamRule N Try_ref"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (Try_ref i)"
                 
 
             unfolding Try_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition Try_refs :: "nat \<Rightarrow> rule set" where
 "Try_refs N \<equiv> oneParamCons N Try_ref"

lemma Try_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_Try N) j i) (Try i) = Try_ref i"
                 unfolding lemmasFor_Try_def  Try_def Try_ref_def  apply(auto      )    
 
done

lemma abs_Try_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (Try_ref i) = Try_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (Try_ref i) = skipRule"
                 
 
             unfolding Try_ref_def Try_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_Crit :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_Crit N = []"

definition Crit_ref :: "nat \<Rightarrow> rule" where
 "Crit_ref i \<equiv> 
   IVar (Para ''n'' i) =\<^sub>f Const T \<and>\<^sub>f
   IVar (Ident ''x'') =\<^sub>f Const true
  \<triangleright>
   assign (Para ''n'' i, Const C) ||
   assign (Ident ''x'', Const false)"

lemma symCrit_ref : 
             " 
                  symParamRule N Crit_ref"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (Crit_ref i)"
                 
 
             unfolding Crit_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition Crit_refs :: "nat \<Rightarrow> rule set" where
 "Crit_refs N \<equiv> oneParamCons N Crit_ref"

lemma Crit_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_Crit N) j i) (Crit i) = Crit_ref i"
                 unfolding lemmasFor_Crit_def  Crit_def Crit_ref_def  apply(auto      )    
 
done

lemma abs_Crit_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (Crit_ref i) = Crit_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (Crit_ref i) = ABS_Crit"
                 
 
             unfolding Crit_ref_def Crit_ref_def ABS_Crit_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_Exit :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_Exit N = []"

definition Exit_ref :: "nat \<Rightarrow> rule" where
 "Exit_ref i \<equiv> 
   IVar (Para ''n'' i) =\<^sub>f Const C
  \<triangleright>
   assign (Para ''n'' i, Const E)"

lemma symExit_ref : 
             " 
                  symParamRule N Exit_ref"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (Exit_ref i)"
                 
 
             unfolding Exit_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition Exit_refs :: "nat \<Rightarrow> rule set" where
 "Exit_refs N \<equiv> oneParamCons N Exit_ref"

lemma Exit_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_Exit N) j i) (Exit i) = Exit_ref i"
                 unfolding lemmasFor_Exit_def  Exit_def Exit_ref_def  apply(auto      )    
 
done

lemma abs_Exit_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (Exit_ref i) = Exit_ref i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (Exit_ref i) = skipRule"
                 
 
             unfolding Exit_ref_def Exit_ref_def skipRule_def  apply(auto     simp add: Let_def )    
 
done

definition lemmasFor_Idle :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_Idle N = [Lemma_1 N]"

definition Idle_ref :: "nat \<Rightarrow> nat \<Rightarrow> rule" where
 "Idle_ref N i \<equiv> 
   IVar (Para ''n'' i) =\<^sub>f Const E \<and>\<^sub>f
   forallFormExcl (\<lambda>j. \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const C \<and>\<^sub>f
   \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const E) i N
  \<triangleright>
   assign (Para ''n'' i, Const I) ||
   assign (Ident ''x'', Const true)"

lemma symIdle_ref : 
             " 
                  symParamRule N (Idle_ref N)"
                 

"[|i <= N|] 
                 ==> wellFormedRule (env N) N (Idle_ref N i)"
                 
 
             unfolding Idle_ref_def  apply(auto intro!: symParamRuleI2 symParamRuleI symParamFormAnd symParamFormForall symParamFormForallExcl symParamFormImply symParamStatementParallel symParamStatementForall symParamStatementForallExcl symParamStatementIte     )    
 
unfolding symParamForm_def  symParamStatement_def     symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def  apply(auto      )    
 
done

definition Idle_refs :: "nat \<Rightarrow> rule set" where
 "Idle_refs N \<equiv> oneParamCons N (Idle_ref N)"

lemma Idle_strengthen : 
                  " 
                  strengthenRuleByFrmL2 (map2' (lemmasFor_Idle N) j i) (Idle i) = Idle_ref N i"
                 unfolding lemmasFor_Idle_def Lemma_1_def Idle_def Idle_ref_def  apply(auto      )    
 
done

lemma abs_Idle_ref : 
             "[|M <= N;i <= M|] 
                 ==> absTransfRule (env N) M (Idle_ref N i) = Idle_ref M i"
                 

"[|M <= N;i > M|] 
                 ==> absTransfRule (env N) M (Idle_ref N i) = ABS_Idle M"
                 
 
             unfolding Idle_ref_def Idle_ref_def ABS_Idle_def  apply(auto     simp add: Let_def )    
 
done

definition InvS :: "nat \<Rightarrow> (((nat \<Rightarrow> nat \<Rightarrow> formula) list) list)" where
 "InvS N = [lemmasFor_Try N, lemmasFor_Crit N, lemmasFor_Exit N, lemmasFor_Idle N]"

definition rule_refs :: "nat \<Rightarrow> rule set" where
 "rule_refs N = (Try_refs N \<union> (Crit_refs N \<union> (Exit_refs N \<union> Idle_refs N)))"

lemma TryStrengthRel : 
                  " 
                  strengthenRel (Trys N) (set (InvS N)) (Try_refs N) N"
                 unfolding Trys_def Try_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_Try" in strengthenExt1)
 using Try_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma CritStrengthRel : 
                  " 
                  strengthenRel (Crits N) (set (InvS N)) (Crit_refs N) N"
                 unfolding Crits_def Crit_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_Crit" in strengthenExt1)
 using Crit_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma ExitStrengthRel : 
                  " 
                  strengthenRel (Exits N) (set (InvS N)) (Exit_refs N) N"
                 unfolding Exits_def Exit_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_Exit" in strengthenExt1)
 using Exit_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma IdleStrengthRel : 
                  " 
                  strengthenRel (Idles N) (set (InvS N)) (Idle_refs N) N"
                 unfolding Idles_def Idle_refs_def  apply(rule_tac ?lemmasFor_r="lemmasFor_Idle" in strengthenExt1)
 using Idle_strengthen apply(presburger      )

unfolding InvS_def  apply(auto      )    
 
done

lemma deriveAllRef : 
             "[|r : Try_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : Crit_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : Exit_refs N|] 
                 ==> deriveRule (env N) r"
                 

"[|r : Idle_refs N|] 
                 ==> deriveRule (env N) r"
                 
 
             unfolding deriveRule_def deriveForm_def deriveStmt_def Try_refs_def Try_ref_def Crit_refs_def Crit_ref_def Exit_refs_def Exit_ref_def Idle_refs_def Idle_ref_def  apply(auto      )    
 
done

lemma symProtAllRef : 
             " 
                  symProtRules' N (Try_refs N)"
                 

" 
                  symProtRules' N (Crit_refs N)"
                 

" 
                  symProtRules' N (Exit_refs N)"
                 

" 
                  symProtRules' N (Idle_refs N)"
                 
 
              using symTry_ref(1) Try_refs_def symCrit_ref(1) Crit_refs_def symExit_ref(1) Exit_refs_def symIdle_ref(1) Idle_refs_def symParaRuleInfSymRuleSet symParaRuleInfSymRuleSet2 apply(auto      )    
 
done

lemma StrengthRelRules2Rule_refs : 
                  " 
                  strengthenRel (rules N) (set (InvS N)) (rule_refs N) N"
                 unfolding rules_def rule_refs_def   apply(rule strenRelUnion)
  apply(blast intro: TryStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: CritStrengthRel     )

   apply(rule strenRelUnion)
  apply(blast intro: ExitStrengthRel     )

  apply(blast intro: IdleStrengthRel     )

done

lemma Abs_Try_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` Try_refs N) = (Try_refs M Un {skipRule})"
                 unfolding Try_refs_def   apply(rule absGen)
 using abs_Try_ref apply(auto      )    
 
done

lemma Abs_Crit_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` Crit_refs N) = (Crit_refs M Un ABS_Crits)"
                 unfolding Crit_refs_def ABS_Crits_def   apply(rule absGen)
 using abs_Crit_ref apply(auto      )    
 
done

lemma Abs_Exit_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` Exit_refs N) = (Exit_refs M Un {skipRule})"
                 unfolding Exit_refs_def   apply(rule absGen)
 using abs_Exit_ref apply(auto      )    
 
done

lemma Abs_Idle_refs : 
                  "[|M < N|] 
                 ==> (absTransfRule (env N) M ` Idle_refs N) = (Idle_refs M Un ABS_Idles M)"
                 unfolding Idle_refs_def ABS_Idles_def   apply(rule absGen)
 using abs_Idle_ref apply(auto      )    
 
done

definition ABS_rules :: "nat \<Rightarrow> rule set" where [simp]:
 "ABS_rules N = (Try_refs N \<union> (Crit_refs N \<union> (ABS_Crits \<union> (Exit_refs N \<union> (Idle_refs N \<union> (ABS_Idles N \<union> {skipRule}))))))"

definition ABS_rules' :: "nat \<Rightarrow> rule set" where [simp]:
 "ABS_rules' N = ((Try_refs N \<union> {skipRule}) \<union> ((Crit_refs N \<union> ABS_Crits) \<union> ((Exit_refs N \<union> {skipRule}) \<union> (Idle_refs N \<union> ABS_Idles N))))"

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

  apply(auto     simp add: Abs_Try_refs Abs_Crit_refs Abs_Exit_refs Abs_Idle_refs )    
 
done

definition Lemma_1' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
 "Lemma_1' N i j \<equiv> \<not>\<^sub>f Const (index i) =\<^sub>f Const (index j) \<and>\<^sub>f
  IVar (Para ''n'' i) =\<^sub>f Const E \<longrightarrow>\<^sub>f
  \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const C \<and>\<^sub>f
  \<not>\<^sub>f IVar (Para ''n'' j) =\<^sub>f Const E"

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

definition lemmasFor_Try' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_Try' N = []"

lemma strengthenVsObsLs_lemmasFor_Try : 
                  " 
                  strengthenVsObsLs (lemmasFor_Try N) (lemmasFor_Try' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_Try_def lemmasFor_Try'_def  apply(auto      )    
 
done

lemma lemmaTry_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : Try_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding Try_refs_def Try_ref_def  apply(auto      )    
 
done

definition lemmasFor_Crit' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_Crit' N = []"

lemma strengthenVsObsLs_lemmasFor_Crit : 
                  " 
                  strengthenVsObsLs (lemmasFor_Crit N) (lemmasFor_Crit' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_Crit_def lemmasFor_Crit'_def  apply(auto      )    
 
done

lemma lemmaCrit_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : Crit_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding Crit_refs_def Crit_ref_def  apply(auto      )    
 
done

definition lemmasFor_Exit' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_Exit' N = []"

lemma strengthenVsObsLs_lemmasFor_Exit : 
                  " 
                  strengthenVsObsLs (lemmasFor_Exit N) (lemmasFor_Exit' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_Exit_def lemmasFor_Exit'_def  apply(auto      )    
 
done

lemma lemmaExit_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : Exit_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding Exit_refs_def Exit_ref_def  apply(auto      )    
 
done

definition lemmasFor_Idle' :: "nat \<Rightarrow> ((nat \<Rightarrow> nat \<Rightarrow> formula) list)" where
 "lemmasFor_Idle' N = [Lemma_1' N]"

lemma strengthenVsObsLs_lemmasFor_Idle : 
                  " 
                  strengthenVsObsLs (lemmasFor_Idle N) (lemmasFor_Idle' N) N"
                 unfolding strengthenVsObsLs_def lemmasFor_Idle_def lemmasFor_Idle'_def  apply(auto intro: strengthenVsObsLemma_1     )    
 
done

lemma lemmaIdle_fitEnv : 
                  "[|formEval (pre r) s;fitEnv s (env N);r : Idle_refs N|] 
                 ==> fitEnv (trans1 (act r) s) (env N)"
                 unfolding Idle_refs_def Idle_ref_def  apply(auto      )    
 
done

definition InvS' :: "nat \<Rightarrow> (((nat \<Rightarrow> nat \<Rightarrow> formula) list) list)" where
 "InvS' N = [lemmasFor_Try' N, lemmasFor_Crit' N, lemmasFor_Exit' N, lemmasFor_Idle' N]"

lemma wellFormedRule_refs : 
                  "[|r : rule_refs N|] 
                 ==> wellFormedRule (env N) N r"
                   apply(auto     simp add: rule_refs_def   Try_refs_def Crit_refs_def Exit_refs_def Idle_refs_def symTry_ref symCrit_ref symExit_ref symIdle_ref )    
 
done

lemma SafeAndderiveAll : 
                  "[|M < N;M = 1;l <= M;k <= M;pinvL : set (InvS' N);pf : set pinvL|] 
                 ==> safeForm (env N) M (pf k l) & deriveForm (env N) (pf k l)"
                 unfolding InvS'_def lemmasFor_Try'_def lemmasFor_Crit'_def lemmasFor_Exit'_def lemmasFor_Idle'_def using SafeAndderiveFormLemma_1' apply(auto      )    
 
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
    apply(case_tac   "x1 = ''x''")
    
    apply(subgoal_tac   "formEval (initSpec1) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
      apply(auto      )    
     done
  
  subgoal for v x21 x22
    apply(case_tac   "x21 = ''n''")
    
    apply(subgoal_tac   "formEval (initSpec0 N) s0")
    
      apply(auto      )[1]    
     
      apply(auto      )[1]    
     
      apply(auto      )    
     done
  
    apply(auto      )    
   done

subgoal for r sk
  unfolding rule_refs_def  apply(auto intro: Un_iff lemmaTry_fitEnv lemmaCrit_fitEnv lemmaExit_fitEnv lemmaIdle_fitEnv     )    
   done

done

lemma absProtSim : 
                  "[|M < N;M = 1;isProtObsInvSet (ABS_rules M) (absTransfForm (env N) M ` allInitSpecs N) (set (InvS' N)) M (env N)|] 
                 ==> isParamProtInvSet (rules N) (allInitSpecs N) (set (InvS N)) N"
                   apply(rule_tac ?rs2.0 = "rule_refs N" and env="env N" and S="set (InvS N)" and S'="set (InvS' N)" and M=M and absRules="ABS_rules M" in CMP)
subgoal for r
   using wellFormedRule_refs apply(auto      )    
   done

subgoal  unfolding InvS'_def lemmasFor_Try'_def lemmasFor_Crit'_def lemmasFor_Exit'_def lemmasFor_Idle'_def using symInvs apply(auto      )    
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
   
  subgoal   using strengthenVsObsLs_lemmasFor_Try apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_Crit apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_Exit apply(auto      )    
     done
  
  subgoal   using strengthenVsObsLs_lemmasFor_Idle apply(auto      )    
     done
  done

   apply(rule equivRuleSetReflex)
 using ABS_all  apply(auto      )    
 
done

end
