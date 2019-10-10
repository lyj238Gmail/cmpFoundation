(*  Title:      HOL/Auth/n_mutualExAbs1_base.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_mutualExAbs1 Protocol Case Study*} 

theory n_mutualExAbs1_base imports paraTheory
begin

section{*Main definitions*}

subsection{* Definitions of Constants*}
definition I::"scalrValueType" where [simp]: "I\<equiv> enum ''control'' ''I''"
definition T::"scalrValueType" where [simp]: "T\<equiv> enum ''control'' ''T''"
definition C::"scalrValueType" where [simp]: "C\<equiv> enum ''control'' ''C''"
definition E::"scalrValueType" where [simp]: "E\<equiv> enum ''control'' ''E''"
definition true::"scalrValueType" where [simp]: "true\<equiv> boolV True"
definition false::"scalrValueType" where [simp]: "false\<equiv> boolV False"



subsection{*  Definitions of Parameterized Rules *}

definition n_Try::"nat \<Rightarrow> rule" where [simp]:
"n_Try  i\<equiv>
let g = (eqn (IVar (Field (Para (Ident ''n'') i) ''st'')) (Const I)) in
let s = (parallelList [(assign ((Field (Para (Ident ''n'') i) ''st''), (Const T)))]) in
guard g s"

definition n_Crit::"nat \<Rightarrow> rule" where [simp]:
"n_Crit  i\<equiv>
let g = (andForm (eqn (IVar (Field (Para (Ident ''n'') i) ''st'')) (Const T)) (eqn (IVar (Ident ''x'')) (Const true))) in
let s = (parallelList [(assign ((Field (Para (Ident ''n'') i) ''st''), (Const C))), (assign ((Ident ''x''), (Const false))), (assign ((Field (Para (Ident ''n'') i) ''data''), (IVar (Ident ''memDATA''))))]) in
guard g s"

definition n_Exit::"nat \<Rightarrow> rule" where [simp]:
"n_Exit  i\<equiv>
let g = (eqn (IVar (Field (Para (Ident ''n'') i) ''st'')) (Const C)) in
let s = (parallelList [(assign ((Field (Para (Ident ''n'') i) ''st''), (Const E)))]) in
guard g s"

definition n_Idle::"nat \<Rightarrow> rule" where [simp]:
"n_Idle  i\<equiv>
let g = (eqn (IVar (Field (Para (Ident ''n'') i) ''st'')) (Const E)) in
let s = (parallelList [(assign ((Field (Para (Ident ''n'') i) ''st''), (Const I))), (assign ((Ident ''x''), (Const true))), (assign ((Ident ''memDATA''), (IVar (Field (Para (Ident ''n'') i) ''data''))))]) in
guard g s"

definition n_Store::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_Store  i data\<equiv>
let g = (eqn (IVar (Field (Para (Ident ''n'') i) ''st'')) (Const C)) in
let s = (parallelList [(assign ((Field (Para (Ident ''n'') i) ''st''), (Const C))), (assign ((Ident ''x''), (Const false))), (assign ((Ident ''auxDATA''), (Const (index data)))), (assign ((Field (Para (Ident ''n'') i) ''data''), (Const (index data))))]) in
guard g s"

definition n_ABS_Store::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_ABS_Store N data\<equiv>
let g = (forallForm (down N) (\<lambda>j. (andForm (neg (eqn (IVar (Field (Para (Ident ''n'') j) ''st'')) (Const C))) (neg (eqn (IVar (Field (Para (Ident ''n'') j) ''st'')) (Const E)))))) in
let s = (parallelList [(assign ((Ident ''x''), (Const false))), (assign ((Ident ''auxDATA''), (Const (index data))))]) in
guard g s"

definition n_ABS_Crit::"rule" where [simp]:
"n_ABS_Crit  \<equiv>
let g = (eqn (IVar (Ident ''x'')) (Const true)) in
let s = (parallelList [(assign ((Ident ''x''), (Const false)))]) in
guard g s"

definition n_ABS_Idle::"nat \<Rightarrow> rule" where [simp]:
"n_ABS_Idle N \<equiv>
let g = (forallForm (down N) (\<lambda>j. (andForm (neg (eqn (IVar (Field (Para (Ident ''n'') j) ''st'')) (Const C))) (neg (eqn (IVar (Field (Para (Ident ''n'') j) ''st'')) (Const E)))))) in
let s = (parallelList [(assign ((Ident ''x''), (Const true))), (assign ((Ident ''memDATA''), (IVar (Ident ''auxDATA''))))]) in
guard g s"





subsection{*The set of All actual Rules w.r.t. a Protocol Instance with Size $N$*}
definition rules::"nat \<Rightarrow> rule set" where [simp]:
"rules N \<equiv> {r.
(\<exists> i. i\<le>N\<and>r=n_Try  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Crit  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Exit  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_Idle  i)
}"

definition  NC::"nat " where [simp]: "NC==1" 

definition rulesAbs::"nat \<Rightarrow> rule set" where [simp]:
"rulesAbs  N\<equiv> {r.
(\<exists> i. i\<le>NC\<and>r=n_Crit  i) \<or>
(\<exists> i. i\<le>NC\<and>r=n_Exit  i) \<or>
(\<exists> i. i\<le>NC\<and>r=n_Idle  i) \<or>
(\<exists> i data. i\<le>NC\<and>data\<le>N\<and>r=n_Store  i data) \<or>
(\<exists> data. data\<le>N\<and>r=n_ABS_Store NC data) \<or>
(r=n_ABS_Crit  ) \<or>
(r=n_ABS_Idle NC )
}"



subsection{*Definitions of a Formally Parameterized Invariant Formulas*}



subsection{*Definitions of  the Set of Invariant Formula Instances in a $N$-protocol Instance*}
definition inv__1::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__1 p__Inv0 p__Inv1 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''n'') p__Inv0) ''st'')) (Const C)) (eqn (IVar (Field (Para (Ident ''n'') p__Inv1) ''st'')) (Const C))))"

definition inv__2::"nat \<Rightarrow> formula" where [simp]:
"inv__2 p__Inv0 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''n'') p__Inv0) ''st'')) (Const C)) (neg (eqn (IVar (Field (Para (Ident ''n'') p__Inv0) ''data'')) (IVar (Ident ''auxDATA''))))))"

definition inv__3::"nat \<Rightarrow> formula" where [simp]:
"inv__3 p__Inv0 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''n'') p__Inv0) ''st'')) (Const E)) (neg (eqn (IVar (Field (Para (Ident ''n'') p__Inv0) ''data'')) (IVar (Ident ''auxDATA''))))))"

definition inv__4::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__4 p__Inv0 p__Inv1 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''n'') p__Inv0) ''st'')) (Const C)) (eqn (IVar (Field (Para (Ident ''n'') p__Inv1) ''st'')) (Const E))))"

definition inv__5::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__5 p__Inv0 p__Inv1 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''n'') p__Inv0) ''st'')) (Const E)) (eqn (IVar (Field (Para (Ident ''n'') p__Inv1) ''st'')) (Const E))))"

definition inv__6::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv__6 p__Inv0 p__Inv1 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''n'') p__Inv0) ''st'')) (Const E)) (eqn (IVar (Field (Para (Ident ''n'') p__Inv1) ''st'')) (Const C))))"

definition inv__7::"formula" where [simp]:
"inv__7  \<equiv>
(neg (andForm (eqn (IVar (Ident ''x'')) (Const true)) (neg (eqn (IVar (Ident ''memDATA'')) (IVar (Ident ''auxDATA''))))))"

definition inv__8::"nat \<Rightarrow> formula" where [simp]:
"inv__8 p__Inv0 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''n'') p__Inv0) ''st'')) (Const C)) (eqn (IVar (Ident ''x'')) (Const true))))"

definition inv__9::"nat \<Rightarrow> formula" where [simp]:
"inv__9 p__Inv0 \<equiv>
(neg (andForm (eqn (IVar (Field (Para (Ident ''n'') p__Inv0) ''st'')) (Const E)) (eqn (IVar (Ident ''x'')) (Const true))))"

subsection{*Definitions of  the Set of Invariant Formula Instances in a $N$-protocol Instance*}
definition invariants::"nat \<Rightarrow> formula set" where [simp]:
"invariants N \<equiv> {f.
(\<exists> p__Inv0 p__Inv1. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv0~=p__Inv1\<and>f=inv__1  p__Inv0 p__Inv1) \<or>
(\<exists> p__Inv0. p__Inv0\<le>N\<and>f=inv__2  p__Inv0) \<or>
(\<exists> p__Inv0. p__Inv0\<le>N\<and>f=inv__3  p__Inv0) \<or>
(\<exists> p__Inv0 p__Inv1. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv0~=p__Inv1\<and>f=inv__4  p__Inv0 p__Inv1) \<or>
(\<exists> p__Inv0 p__Inv1. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv0~=p__Inv1\<and>f=inv__5  p__Inv0 p__Inv1) \<or>
(\<exists> p__Inv0 p__Inv1. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv0~=p__Inv1\<and>f=inv__6  p__Inv0 p__Inv1) \<or>
(f=inv__7  ) \<or>
(\<exists> p__Inv0. p__Inv0\<le>N\<and>f=inv__8  p__Inv0) \<or>
(\<exists> p__Inv0. p__Inv0\<le>N\<and>f=inv__9  p__Inv0)
}"

definition invariantsAbs::" formula list" where [simp]:
"invariantsAbs  \<equiv> [
(inv__1  0 1) ,
(inv__2  0),
(inv__3 0),
(inv__4  0 1),
(inv__5  0 1),
(inv__6  0 1) ,
(inv__7  ) ,
(inv__8  0) ,
(inv__9  0)
]"

subsection{*Definitions of initial states*}

definition initSpec0::"nat \<Rightarrow> formula" where [simp]:
"initSpec0 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Field (Para (Ident ''n'') i) ''st'')) (Const I))))"

definition initSpec1::"nat \<Rightarrow> formula" where [simp]:
"initSpec1 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Field (Para (Ident ''n'') i) ''data'')) (Const (index 1)))))"

definition initSpec2::"formula" where [simp]:
"initSpec2  \<equiv> (eqn (IVar (Ident ''x'')) (Const true))"

definition initSpec3::"formula" where [simp]:
"initSpec3  \<equiv> (eqn (IVar (Ident ''auxDATA'')) (Const (index 1)))"

definition initSpec4::"formula" where [simp]:
"initSpec4  \<equiv> (eqn (IVar (Ident ''memDATA'')) (Const (index 1)))"

definition allInitSpecs::"nat \<Rightarrow> formula list" where [simp]:
"allInitSpecs N \<equiv> [
(initSpec0 N),
(initSpec1 N),
(initSpec2 ),
(initSpec3 ),
(initSpec4 )
]"

definition allInitSpecsAbs::" formula list" where [simp]:
"allInitSpecsAbs  \<equiv> [
(initSpec0 NC), 
(initSpec1 NC),
(initSpec2  ),
(initSpec3 ),
(initSpec4 )
]"

axiomatization  where axiomOnf2 [simp,intro]:
   "s \<in> reachableSet (set (allInitSpecs N )) (rules N) \<Longrightarrow>  1 < N \<Longrightarrow> 1 < i \<Longrightarrow> j<2 \<Longrightarrow>  formEval (f 0 1) s \<Longrightarrow> formEval (f i j) s"

axiomatization  where axiomOnf1 [simp,intro]:
   "s \<in> reachableSet (set (allInitSpecs N )) (rules N) \<Longrightarrow> 1 < N \<Longrightarrow> 1 < i \<Longrightarrow>formEval (f 0 ) s \<Longrightarrow> formEval (f i) s"

lemma ruleSimId: 
  assumes  a3:"\<forall>v. v\<in>varOfForm (pre r) \<longrightarrow> (\<exists>f. f \<in>F \<and>v \<in> varOfForm f)" and  
  (*a5:"\<forall>f v va. v \<in> varOfForm f \<longrightarrow> f \<in>F \<longrightarrow>va\<in>varOfExp ( substExpByStatement (IVar v)  (act r))\<longrightarrow> (\<exists>f. f \<in> F \<and> va \<in> varOfForm f)" *)
  a5:"\<forall>v a. a \<in> set (statement2Assigns (act r)) \<longrightarrow> v\<in>varOfExp ( substExpByStatement (IVar (fst a))  (act r))\<longrightarrow> (\<exists>f. f \<in> F \<and> v \<in> varOfForm f)"
shows
"trans_sim_on1 r r F"
proof(unfold trans_sim_on1_def,(rule allI)+,(rule impI)+ ) 
  fix s1 s2
  assume b1:"formEval (pre r) s1 \<and> (\<forall> f. f \<in>F \<longrightarrow> formEval f s1 )" and b2:"state_sim_on1 s1 s2 F"
  show "((state_sim_on1 (trans (act r) s1) (trans (act r) s2) F \<and> (formEval (pre r) s2 ))
           \<or> state_sim_on1 (trans (act r) s1) s2 F)"
  proof(rule disjI1,rule conjI)
    show "state_sim_on1 (trans (act r) s1) (trans (act r) s2) F"
    proof(unfold state_sim_on1_def,(rule allI)+,(rule impI)+)
      fix f v
      assume c1:"f \<in>F"  and c2:"v \<in>varOfForm f"
      have c20:"expEval  (substExpByStatement (IVar v) (act r)) s1 = expEval (IVar v) (trans (act r) s1)" 
        using preCondOnExp by blast
     have c3:"expEval  (substExpByStatement (IVar v) (act r)) s2 = expEval (IVar v) (trans (act r) s2)"
       using preCondOnExp by blast

     have c4:"\<forall>v a. a \<in> set (statement2Assigns (act r)) \<longrightarrow> v\<in>varOfExp ( substExpByStatement (IVar (fst a))  (act r)) \<longrightarrow> s1(v) = s2 v"
       using a5 b2 c1 c2 state_sim_on1_def by blast
 
     have c5:"expEval (substExpByStatement (IVar v)  (act r)) s1 = expEval (substExpByStatement (IVar v)  (act r)) s2"
     proof(case_tac "\<exists>a. a \<in> set (statement2Assigns (act r)) \<and> (fst a) =v")
       assume d1:"\<exists>a. a \<in> set (statement2Assigns (act r)) \<and> (fst a) =v"
       from d1 obtain as where d2:"as \<in> set (statement2Assigns (act r)) \<and> (fst as) =v" by blast
         have d3:"\<forall>v.  v\<in>varOfExp ( substExpByStatement (IVar (fst as))  (act r)) \<longrightarrow> s1(v) = s2 v"
           using c4 d2 by blast
         then show "expEval (substExpByStatement (IVar v)  (act r)) s1 = expEval (substExpByStatement (IVar v)  (act r)) s2"
           using agreeOnVarsOfExp d2 by blast
       next
         assume d1:"\<not>(\<exists>a. a \<in> set (statement2Assigns (act r)) \<and> (fst a) =v )"
         have d1:"(substExpByStatement (IVar v)  (act r)) =   (IVar v)"  sorry
         then show "expEval (substExpByStatement (IVar v)  (act r)) s1 = expEval (substExpByStatement (IVar v)  (act r)) s2"
           using b2 c1 c2 by auto
     qed     
     show " trans (act r) s1 v =   trans (act r) s2 v"
       using  c1 c2 c5 lemmaOnValOf by auto
   qed
 next
   have "formEval (pre r) s1"
     by (simp add: b1 )
  have c4:"\<forall>va. va \<in> varOfForm  (pre r)\<longrightarrow> s1(va) = s2 va"
    using  a3 b2 by auto 
   show "formEval (pre r) s2"
     using \<open>formEval (pre r) s1\<close> agreeOnVars c4 by blast 
    
 qed
qed

lemma setOfList[simp]: " {v. \<exists>f. f \<in> set flist \<and> v \<in> varOfForm f} = varOfFormList flist"
proof(induct_tac flist,auto) qed

lemma onF[simp,intro]: 
  " varOfFormList invariantsAbs = 
  { (Field (Para (Ident ''n'') 0) ''data''),varType.Field (Para (Ident ''n'') 0) ''st'' , varType.Field (Para (Ident ''n'') 1) ''st'',
   (Ident ''x''),(Ident ''memDATA''),(Ident ''auxDATA'')  }"    
(*{v. \<exists>f. f \<in> invariantsAbs \<and> v \<in> varOfForm f})*)
  by auto
 (* apply(simp)
  apply(erule disjE)
  apply(rule_tac x="inv__1 0 1" in exI,simp)
  apply(erule disjE)
  apply(rule_tac x="inv__1 0 1" in exI,simp)
  apply(rule_tac x="inv__9 0 " in exI,simp)
  done*)

lemma lemmaOnTryLeNc:
  assumes a1:"i\<le>NC" 
  shows "trans_sim_on1 (n_Try  i) (n_Try  i) (set invariantsAbs)" (is "trans_sim_on1 ?r ?r ?F")
proof(rule ruleSimId)
  have "\<forall>v. v\<in>varOfForm (pre ?r) \<longrightarrow>  v \<in>(varOfFormList invariantsAbs)"
    by(cut_tac a1, auto)
  then show "\<forall>v. v\<in>varOfForm (pre ?r) \<longrightarrow>  v \<in>(varOfFormList invariantsAbs)"
    sorry
next
  have  b1: "\<forall>v a. a \<in> set (statement2Assigns (act ?r)) \<longrightarrow> v\<in>varOfExp ( substExpByStatement (IVar (fst a))  (act ?r))\<longrightarrow>v \<in>varOfFormList invariantsAbs "
   proof((rule allI)+,(rule impI)+,auto)
  show "\<forall>v a. a \<in> set (statement2Assigns (act ?r)) \<longrightarrow> v\<in>varOfExp ( substExpByStatement (IVar (fst a))  (act ?r))\<longrightarrow> (\<exists>f. f \<in> ?F \<and> v \<in> varOfForm f)"
  proof((rule allI)+,(rule impI)+)
    fix v a
    assume b1:"a \<in> set (statement2Assigns (act ?r)) " and b2:" v\<in>varOfExp ( substExpByStatement (IVar (fst a))  (act ?r))"
    have "v=  (Para (Ident ''n'') i) \<or> v=(Ident ''x'')" by(cut_tac b1 b2,auto)
    then have "v \<in> { (Para (Ident ''n'') 1) , (Para (Ident ''n'') 0), (Ident ''x'')}" 
      apply (cut_tac a1, auto) done
    then show "(\<exists>f. f \<in> ?F \<and> v \<in> varOfForm f)"
      using onF by blast 
      
      apply(cut_tac a1,auto )
    
end
