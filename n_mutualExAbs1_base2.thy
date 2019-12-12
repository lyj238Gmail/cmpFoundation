(*  Title:      HOL/Auth/n_mutualExAbs1_base.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)
 
theory n_mutualExAbs1_base2 imports paraTheory
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

definition invariantsAbs::" formula list" where 
"invariantsAbs  \<equiv>[
(inv__1  0 1) ,(inv__1   1 0),
(inv__2  0),(inv__2  1),
(inv__3 0),(inv__3 1),
(inv__4  0 1),(inv__4   1 0),
(inv__5  0 1),(inv__5   1 0),
(inv__6  0 1) ,(inv__6   1 0),
(inv__7  ) ,
(inv__8  0) ,(inv__8  1),
(inv__9  0),(inv__9  1)
]" (*[
(inv__1  0 1) ,
(inv__2  0),
(inv__3 0),
(inv__4  0 1),
(inv__5  0 1),
(inv__6  0 1) ,
(inv__7  ) ,
(inv__8  0) ,
(inv__9  0)
]"*)

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


 (* apply(simp)
  apply(erule disjE)
  apply(rule_tac x="inv__1 0 1" in exI,simp)
  apply(erule disjE)
  apply(rule_tac x="inv__1 0 1" in exI,simp)
  apply(rule_tac x="inv__9 0 " in exI,simp)
  done*)

lemma lemmaOnTryLeNc:
  assumes a1:"i\<le>NC" 
  shows "trans_sim_on1 (n_Try  i) (n_Try  i) (set invariantsAbs) s" (is "trans_sim_on1 ?r ?r ?F s")
proof(rule ruleSimId)
  show  "\<forall>v. v\<in>varOfForm (pre ?r) \<longrightarrow>  v \<in>(varOfFormList invariantsAbs) "
    by(cut_tac a1,  auto simp add :invariantsAbs_def) 
    
next
  show  b1: "\<forall>v a. a \<in> set (statement2Assigns (act ?r)) \<longrightarrow> v\<in>varOfExp ( substExpByStatement (IVar (fst a))  (act ?r))\<longrightarrow>v \<in>varOfFormList invariantsAbs "
   proof((rule allI)+,(rule impI)+,auto) qed
    
qed

lemma lemmaOnTryGtNc:
  assumes a1:"i>NC" and a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)" and a3:"1<N" and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s"
  shows "trans_sim_on1 (n_Idle  i) (n_ABS_Idle  NC) (set invariantsAbs) s" (is "trans_sim_on1 ?r ?r' ?F s")
proof(rule ruleSimCond)
  show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")
  proof(rule impI)+
    assume b1:"?A"  
    from a4  have b4:"formEval (inv__5 0 1 ) s"  by  (force simp add :invariantsAbs_def) 
    have b5:"formEval (inv__5 i 0 ) s" 
    proof(cut_tac a1 a2 a3 b4,rule axiomOnf2,force+)qed
    with b1  have b6:"formEval (neg (eqn (IVar (Field (Para (Ident ''n'') 0) ''st'')) (Const E))) s" by auto
     have b7:"formEval (inv__5 i 1 ) s" 
     proof(cut_tac a1 a2 a3 b4,rule axiomOnf2,force+)qed
     with b1 have b7:"formEval (neg (eqn (IVar (Field (Para (Ident ''n'') 1) ''st'')) (Const E))) s" by auto

     from a4 have b8:"formEval (inv__6 0 1 ) s"  by auto
     have b9:"formEval (inv__6 i 0 ) s" 
    proof(cut_tac a1 a2 a3 b8,rule axiomOnf2,force+)qed
    with b1 have b9:"formEval (neg (eqn (IVar (Field (Para (Ident ''n'') 0) ''st'')) (Const C))) s" by auto
     have b10:"formEval (inv__6 i 1 ) s" 
     proof(cut_tac a1 a2 a3 b8,rule axiomOnf2,force+)qed
     with b1 have b11:"formEval (neg (eqn (IVar (Field (Para (Ident ''n'') 1) ''st'')) (Const C))) s" by auto
    
     from b1 b6 b7 b9 b11 show "formEval (pre ?r') s" 
       by auto
   qed
 next
    
   show "\<forall>v. v\<in>varOfForm (pre ?r') \<longrightarrow> v \<in>(varOfFormList invariantsAbs)"
      by auto
 next
   
   show "
  (\<forall>v.   v \<in> (varOfFormList invariantsAbs) \<longrightarrow>formEval (pre ?r) s\<longrightarrow> expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"  
   proof((rule allI)+,(rule impI)+)
     fix  v
     assume b1:"v\<in> (varOfFormList invariantsAbs)"  and b2:"formEval (pre ?r) s"
    
     from a4 have b30:"formEval (inv__3 0 ) s"   by auto

     have b3:"formEval (inv__3 i ) s"  proof(cut_tac a1 a2 a3 b30,rule axiomOnf1,force+)qed

     show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 b1 b2 b3,auto) done
   qed
  (* have "\<forall>f v va. v \<in> varOfForm f \<longrightarrow> f \<in>?F \<longrightarrow>va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r'))\<longrightarrow> va \<in>(varOfFormList invariantsAbs)"   by auto*)
     then show "\<forall> v va. v \<in> varOfFormList invariantsAbs \<longrightarrow>va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r'))\<longrightarrow> va \<in> varOfFormList invariantsAbs"
      by auto  
 qed
(*
lemma lemmaOnTryGtNc:
  assumes a1:"i>NC" and a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)" and a3:"1<N"
  shows "trans_sim_on1 (n_Idle  i) (n_ABS_Idle  NC) (set invariantsAbs) s" (is "trans_sim_on1 ?r ?r' ?F s")
proof(rule ruleSimCond)
  show " (\<forall> f. f \<in>?F \<longrightarrow> formEval f s ) \<longrightarrow> formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B\<longrightarrow>?C")
  proof(rule impI)+
    assume b1:"?A" and b2:"?B" 
    from b1 have b4:"formEval (inv__5 0 1 ) s"  by auto
    have b5:"formEval (inv__5 i 0 ) s" 
    proof(cut_tac a1 a2 a3 b4,rule axiomOnf2,force+)qed
    with b2 have b6:"formEval (neg (eqn (IVar (Field (Para (Ident ''n'') 0) ''st'')) (Const E))) s" by auto
     have b7:"formEval (inv__5 i 1 ) s" 
     proof(cut_tac a1 a2 a3 b4,rule axiomOnf2,force+)qed
     with b2 have b7:"formEval (neg (eqn (IVar (Field (Para (Ident ''n'') 1) ''st'')) (Const E))) s" by auto

     from b1 have b8:"formEval (inv__6 0 1 ) s"  by auto
     have b9:"formEval (inv__6 i 0 ) s" 
    proof(cut_tac a1 a2 a3 b8,rule axiomOnf2,force+)qed
    with b2 have b9:"formEval (neg (eqn (IVar (Field (Para (Ident ''n'') 0) ''st'')) (Const C))) s" by auto
     have b10:"formEval (inv__6 i 1 ) s" 
     proof(cut_tac a1 a2 a3 b8,rule axiomOnf2,force+)qed
     with b2 have b11:"formEval (neg (eqn (IVar (Field (Para (Ident ''n'') 1) ''st'')) (Const C))) s" by auto
    
     from b2 b6 b7 b9 b11 show "formEval (pre ?r') s" 
       by auto
   qed
 next
   have "\<forall>v. v\<in>varOfForm (pre ?r') \<longrightarrow> v \<in>(varOfFormList invariantsAbs)"
     by simp
   then show "\<forall>v. v\<in>varOfForm (pre ?r') \<longrightarrow>(\<exists>f. f \<in>?F \<and>v \<in> varOfForm f)"
     using mem_Collect_eq setOfList by auto
 next
   
   show " (\<forall> f. f \<in>?F \<longrightarrow> formEval f s ) \<longrightarrow>
  (\<forall>f  v. f\<in> ?F \<longrightarrow>  v \<in> varOfForm f \<longrightarrow>formEval (pre ?r) s\<longrightarrow> expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)" (is "?A \<longrightarrow>?B")
   proof(rule impI)+
     assume b1:"?A" 
    
     from b1 have b2:"formEval (inv__3 0 ) s"   by auto

     have b2:"formEval (inv__3 i ) s"  proof(cut_tac a1 a2 a3 b2,rule axiomOnf1,force+)qed
     show "?B"  by (cut_tac a1 b2,auto)
   qed
   have "\<forall>f v va. v \<in> varOfForm f \<longrightarrow> f \<in>?F \<longrightarrow>va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r'))\<longrightarrow> va \<in>(varOfFormList invariantsAbs)"   by auto
     then show "\<forall>f v va. v \<in> varOfForm f \<longrightarrow> f \<in>?F \<longrightarrow>va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r'))\<longrightarrow> (\<exists>f. f \<in>?F \<and>va \<in> varOfForm f)"
     using mem_Collect_eq setOfList by auto  
 qed

end
and
  a5:"\<forall>f v va. v \<in> varOfForm f \<longrightarrow> f \<in>F \<longrightarrow>va\<in>varOfExp ( substExpByStatement (IVar v)  (act r2))\<longrightarrow> (varOfFormList invariantsAbs)"  
*)