(*  Title:      HOL/Auth/n_german_base.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

(*header{*The n_german Protocol Case Study*} *)

theory n_german_baseQues imports paraTheory
begin

section{*Main definitions*}

subsection{* Definitions of Constants*}
definition I::"scalrValueType" where [simp]: "I\<equiv> enum ''control'' ''I''"
definition S::"scalrValueType" where [simp]: "S\<equiv> enum ''control'' ''S''"
definition E::"scalrValueType" where [simp]: "E\<equiv> enum ''control'' ''E''"
definition Empty::"scalrValueType" where [simp]: "Empty\<equiv> enum ''control'' ''Empty''"
definition ReqS::"scalrValueType" where [simp]: "ReqS\<equiv> enum ''control'' ''ReqS''"
definition ReqE::"scalrValueType" where [simp]: "ReqE\<equiv> enum ''control'' ''ReqE''"
definition Inv::"scalrValueType" where [simp]: "Inv\<equiv> enum ''control'' ''Inv''"
definition InvAck::"scalrValueType" where [simp]: "InvAck\<equiv> enum ''control'' ''InvAck''"
definition GntS::"scalrValueType" where [simp]: "GntS\<equiv> enum ''control'' ''GntS''"
definition GntE::"scalrValueType" where [simp]: "GntE\<equiv> enum ''control'' ''GntE''"
definition true::"scalrValueType" where [simp]: "true\<equiv> boolV True"
definition false::"scalrValueType" where [simp]: "false\<equiv> boolV False"



subsection{*  Definitions of Parameterized Rules *}

definition  NC::"nat " where [simp]: "NC==1"

 definition VF::"varType set" where [simp]: 
"VF \<equiv>{(Ident ''AuxData''),(Field (Para (Ident ''Cache'') 0) ''Data''),(Field (Para (Ident ''Cache'') 0) ''State''),(Field (Para (Ident ''Cache'') 1) ''Data''),(Field (Para (Ident ''Cache'') 1) ''State''),(Field (Para (Ident ''Chan1'') 0) ''Cmd''),(Field (Para (Ident ''Chan1'') 1) ''Cmd''),(Field (Para (Ident ''Chan2'') 0) ''Cmd''),(Field (Para (Ident ''Chan2'') 0) ''Data''),(Field (Para (Ident ''Chan2'') 1) ''Cmd''),(Field (Para (Ident ''Chan2'') 1) ''Data''),(Field (Para (Ident ''Chan3'') 0) ''Cmd''),(Field (Para (Ident ''Chan3'') 0) ''Data''),(Field (Para (Ident ''Chan3'') 1) ''Cmd''),(Field (Para (Ident ''Chan3'') 1) ''Data''),(Ident ''CurCmd''),(Ident ''CurPtr''),(Ident ''ExGntd''),(Para (Ident ''InvSet'') 0),(Para (Ident ''InvSet'') 1),(Ident ''MemData''),(Para (Ident ''ShrSet'') 0),(Para (Ident ''ShrSet'') 1)}"
definition n_RecvGntE1::"nat \<Rightarrow> rule" where [simp]:
"n_RecvGntE1  i\<equiv>
let g = (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const GntE)) in
let s = (parallelList [(assign ((Field (Para (Ident ''Cache'') i) ''State''), (Const E))), (assign ((Field (Para (Ident ''Cache'') i) ''Data''), (IVar (Field (Para (Ident ''Chan2'') i) ''Data'')))), (assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const Empty)))]) in
guard g s"

definition n_RecvGntS2::"nat \<Rightarrow> rule" where [simp]:
"n_RecvGntS2  i\<equiv>
let g = (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const GntS)) in
let s = (parallelList [(assign ((Field (Para (Ident ''Cache'') i) ''State''), (Const S))), (assign ((Field (Para (Ident ''Cache'') i) ''Data''), (IVar (Field (Para (Ident ''Chan2'') i) ''Data'')))), (assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const Empty)))]) in
guard g s"

definition n_SendGntE3::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_SendGntE3 N i\<equiv>
let g = (andForm (andForm (andForm (andForm (eqn (IVar (Ident ''CurCmd'')) (Const ReqE)) (eqn (IVar (Ident ''CurPtr'')) (Const (index i)))) (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Empty))) (eqn (IVar (Ident ''ExGntd'')) (Const false))) (forallForm (down N) (\<lambda>j. (eqn (IVar (Para (Ident ''ShrSet'') j)) (Const false))))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const GntE))), (assign ((Field (Para (Ident ''Chan2'') i) ''Data''), (IVar (Ident ''MemData'')))), (assign ((Para (Ident ''ShrSet'') i), (Const true))), (assign ((Ident ''ExGntd''), (Const true))), (assign ((Ident ''CurCmd''), (Const Empty)))]) in
guard g s"

definition n_SendGntS4::"nat \<Rightarrow> rule" where [simp]:
"n_SendGntS4  i\<equiv>
let g = (andForm (andForm (andForm (eqn (IVar (Ident ''CurCmd'')) (Const ReqS)) (eqn (IVar (Ident ''CurPtr'')) (Const (index i)))) (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Empty))) (eqn (IVar (Ident ''ExGntd'')) (Const false))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const GntS))), (assign ((Field (Para (Ident ''Chan2'') i) ''Data''), (IVar (Ident ''MemData'')))), (assign ((Para (Ident ''ShrSet'') i), (Const true))), (assign ((Ident ''CurCmd''), (Const Empty)))]) in
guard g s"

definition n_RecvInvAck5::"nat \<Rightarrow> rule" where [simp]:
"n_RecvInvAck5  i\<equiv>
let g = (andForm (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck)) (eqn (IVar (Ident ''ExGntd'')) (Const true))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan3'') i) ''Cmd''), (Const Empty))), (assign ((Para (Ident ''ShrSet'') i), (Const false))), (assign ((Ident ''ExGntd''), (Const false))), (assign ((Ident ''MemData''), (IVar (Field (Para (Ident ''Chan3'') i) ''Data''))))]) in
guard g s"

definition n_RecvInvAck6::"nat \<Rightarrow> rule" where [simp]:
"n_RecvInvAck6  i\<equiv>
let g = (andForm (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck)) (neg (eqn (IVar (Ident ''ExGntd'')) (Const true)))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan3'') i) ''Cmd''), (Const Empty))), (assign ((Para (Ident ''ShrSet'') i), (Const false)))]) in
guard g s"

definition n_SendInvAck7::"nat \<Rightarrow> rule" where [simp]:
"n_SendInvAck7  i\<equiv>
let g = (andForm (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Inv)) (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const Empty))) (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const E))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const Empty))), (assign ((Field (Para (Ident ''Chan3'') i) ''Cmd''), (Const InvAck))), (assign ((Field (Para (Ident ''Chan3'') i) ''Data''), (IVar (Field (Para (Ident ''Cache'') i) ''Data'')))), (assign ((Field (Para (Ident ''Cache'') i) ''State''), (Const I)))]) in
guard g s"

definition n_SendInvAck8::"nat \<Rightarrow> rule" where [simp]:
"n_SendInvAck8  i\<equiv>
let g = (andForm (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Inv)) (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const Empty))) (neg (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const E)))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const Empty))), (assign ((Field (Para (Ident ''Chan3'') i) ''Cmd''), (Const InvAck))), (assign ((Field (Para (Ident ''Cache'') i) ''State''), (Const I)))]) in
guard g s"

definition n_SendInv9::"nat \<Rightarrow> rule" where [simp]:
"n_SendInv9  i\<equiv>
let g = (andForm (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Empty)) (eqn (IVar (Para (Ident ''InvSet'') i)) (Const true))) (eqn (IVar (Ident ''CurCmd'')) (Const ReqE))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const Inv))), (assign ((Para (Ident ''InvSet'') i), (Const false)))]) in
guard g s"

definition n_SendInv10::"nat \<Rightarrow> rule" where [simp]:
"n_SendInv10  i\<equiv>
let g = (andForm (andForm (andForm (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Empty)) (eqn (IVar (Para (Ident ''InvSet'') i)) (Const true))) (eqn (IVar (Ident ''CurCmd'')) (Const ReqS))) (eqn (IVar (Ident ''ExGntd'')) (Const true))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan2'') i) ''Cmd''), (Const Inv))), (assign ((Para (Ident ''InvSet'') i), (Const false)))]) in
guard g s"

definition n_RecvReqE11::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_RecvReqE11 N i\<equiv>
let g = (andForm (eqn (IVar (Ident ''CurCmd'')) (Const Empty)) (eqn (IVar (Field (Para (Ident ''Chan1'') i) ''Cmd'')) (Const ReqE))) in
let s = (parallelList [(assign ((Ident ''CurCmd''), (Const ReqE))), (assign ((Ident ''CurPtr''), (Const (index i)))), (assign ((Field (Para (Ident ''Chan1'') i) ''Cmd''), (Const Empty))), (forallSent (down N) (\<lambda>j. (assign ((Para (Ident ''InvSet'') j), (IVar (Para (Ident ''ShrSet'') j))))))]) in
guard g s"

definition n_RecvReqS12::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_RecvReqS12 N i\<equiv>
let g = (andForm (eqn (IVar (Ident ''CurCmd'')) (Const Empty)) (eqn (IVar (Field (Para (Ident ''Chan1'') i) ''Cmd'')) (Const ReqS))) in
let s = (parallelList [(assign ((Ident ''CurCmd''), (Const ReqS))), (assign ((Ident ''CurPtr''), (Const (index i)))), (assign ((Field (Para (Ident ''Chan1'') i) ''Cmd''), (Const Empty))), (forallSent (down N) (\<lambda>j. (assign ((Para (Ident ''InvSet'') j), (IVar (Para (Ident ''ShrSet'') j))))))]) in
guard g s"

definition n_SendReqE13::"nat \<Rightarrow> rule" where [simp]:
"n_SendReqE13  i\<equiv>
let g = (andForm (eqn (IVar (Field (Para (Ident ''Chan1'') i) ''Cmd'')) (Const Empty)) (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const I))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan1'') i) ''Cmd''), (Const ReqE)))]) in
guard g s"

definition n_SendReqE14::"nat \<Rightarrow> rule" where [simp]:
"n_SendReqE14  i\<equiv>
let g = (andForm (eqn (IVar (Field (Para (Ident ''Chan1'') i) ''Cmd'')) (Const Empty)) (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const S))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan1'') i) ''Cmd''), (Const ReqE)))]) in
guard g s"

definition n_SendReqS15::"nat \<Rightarrow> rule" where [simp]:
"n_SendReqS15  i\<equiv>
let g = (andForm (eqn (IVar (Field (Para (Ident ''Chan1'') i) ''Cmd'')) (Const Empty)) (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const I))) in
let s = (parallelList [(assign ((Field (Para (Ident ''Chan1'') i) ''Cmd''), (Const ReqS)))]) in
guard g s"

definition n_Store::"nat \<Rightarrow> nat \<Rightarrow> rule" where [simp]:
"n_Store  i d\<equiv>
let g = (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const E)) in
let s = (parallelList [(assign ((Field (Para (Ident ''Cache'') i) ''Data''), (Const (index d)))), (assign ((Ident ''AuxData''), (Const (index d))))]) in
guard g s"

definition n_SendGntE3_i_3::"rule" where [simp]:
"n_SendGntE3_i_3  \<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Ident ''CurCmd'')) (Const ReqE)) (eqn (IVar (Ident ''ExGntd'')) (Const false))) (forallForm (down NC) (\<lambda>j. (eqn (IVar (Para (Ident ''ShrSet'') j)) (Const false))))) (eqn (IVar (Ident ''MemData'')) (IVar (Ident ''AuxData'')))) (forallForm (down NC) (\<lambda>i. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const GntE)))))) (forallForm (down NC) (\<lambda>j. (neg (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const E)))))) in
let s = (parallelList [(assign ((Ident ''ExGntd''), (Const true))), (assign ((Ident ''CurCmd''), (Const Empty)))]) in
guard g s"

definition n_SendGntS4_i_3::"rule" where [simp]:
"n_SendGntS4_i_3  \<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Ident ''CurCmd'')) (Const ReqS)) (eqn (IVar (Ident ''ExGntd'')) (Const false))) (eqn (IVar (Ident ''MemData'')) (IVar (Ident ''AuxData'')))) (forallForm (down NC) (\<lambda>i. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const GntE)))))) (forallForm (down NC) (\<lambda>j. (neg (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const E)))))) (forallForm (down NC) (\<lambda>j. (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const Empty))))) (forallForm (down NC) (\<lambda>i. (neg (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck)))))) (forallForm (down NC) (\<lambda>i. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Inv)))))) in
let s = (parallelList [(assign ((Ident ''CurCmd''), (Const Empty)))]) in
guard g s"

definition n_RecvInvAck5_i_3::"rule" where [simp]:
"n_RecvInvAck5_i_3  \<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (forallForm (down NC) (\<lambda>i. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const GntS)))))) (forallForm (down NC) (\<lambda>j. (neg (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const S)))))) (neg (eqn (IVar (Ident ''CurCmd'')) (Const Empty)))) (forallForm (down NC) (\<lambda>j. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') j) ''Cmd'')) (Const GntE)))))) (forallForm (down NC) (\<lambda>j. (neg (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const E)))))) (forallForm (down NC) (\<lambda>j. (eqn (IVar (Para (Ident ''ShrSet'') j)) (Const false))))) (forallForm (down NC) (\<lambda>j. (eqn (IVar (Para (Ident ''InvSet'') j)) (Const false))))) (forallForm (down NC) (\<lambda>j. (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const Empty))))) (forallForm (down NC) (\<lambda>j. (eqn (IVar (Field (Para (Ident ''Chan2'') j) ''Cmd'')) (Const Empty))))) (forallForm (down NC) (\<lambda>j. (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const I))))) (forallForm (down NC) (\<lambda>j. (neg (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const InvAck)))))) (forallForm (down NC) (\<lambda>j. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') j) ''Cmd'')) (Const Inv)))))) (forallForm (down NC) (\<lambda>i. (eqn (IVar (Para (Ident ''ShrSet'') i)) (Const false))))) (forallForm (down NC) (\<lambda>i. (eqn (IVar (Para (Ident ''InvSet'') i)) (Const false))))) (forallForm (down NC) (\<lambda>i. (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const Empty))))) (forallForm (down NC) (\<lambda>i. (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Empty))))) (forallForm (down NC) (\<lambda>i. (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const I))))) (forallForm (down NC) (\<lambda>i. (neg (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck)))))) (forallForm (down NC) (\<lambda>i. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Inv)))))) in
let s = (parallelList [(assign ((Ident ''ExGntd''), (Const false))), (assign ((Ident ''MemData''), (IVar (Ident ''AuxData''))))]) in
guard g s"

definition n_RecvReqE11_i_3::"rule" where [simp]:
"n_RecvReqE11_i_3  \<equiv>
let g = (andForm (andForm (andForm (eqn (IVar (Ident ''CurCmd'')) (Const Empty)) (forallForm (down NC) (\<lambda>i. (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const Empty))))) (forallForm (down NC) (\<lambda>i. (neg (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck)))))) (forallForm (down NC) (\<lambda>i. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Inv)))))) in
let s = (parallelList [(assign ((Ident ''CurCmd''), (Const ReqE))), (assign ((Ident ''CurPtr''), (Const (index 3)))), (forallSent (down NC) (\<lambda>j. (assign ((Para (Ident ''InvSet'') j), (IVar (Para (Ident ''ShrSet'') j))))))]) in
guard g s"

definition n_RecvReqS12_i_3::"rule" where [simp]:
"n_RecvReqS12_i_3  \<equiv>
let g = (andForm (andForm (andForm (eqn (IVar (Ident ''CurCmd'')) (Const Empty)) (forallForm (down NC) (\<lambda>i. (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const Empty))))) (forallForm (down NC) (\<lambda>i. (neg (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck)))))) (forallForm (down NC) (\<lambda>i. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Inv)))))) in
let s = (parallelList [(assign ((Ident ''CurCmd''), (Const ReqS))), (assign ((Ident ''CurPtr''), (Const (index 3)))), (forallSent (down NC) (\<lambda>j. (assign ((Para (Ident ''InvSet'') j), (IVar (Para (Ident ''ShrSet'') j))))))]) in
guard g s"

definition n_Store_i_3::"nat \<Rightarrow> rule" where [simp]:
"n_Store_i_3  d\<equiv>
let g = (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (andForm (forallForm (down NC) (\<lambda>j. (eqn (IVar (Para (Ident ''ShrSet'') j)) (Const false)))) (forallForm (down NC) (\<lambda>i. (eqn (IVar (Para (Ident ''InvSet'') i)) (Const false))))) (eqn (IVar (Ident ''ExGntd'')) (Const true))) (forallForm (down NC) (\<lambda>j. (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const Empty))))) (forallForm (down NC) (\<lambda>j. (eqn (IVar (Field (Para (Ident ''Chan2'') j) ''Cmd'')) (Const Empty))))) (forallForm (down NC) (\<lambda>i. (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const I))))) (forallForm (down NC) (\<lambda>j. (neg (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const InvAck)))))) (forallForm (down NC) (\<lambda>j. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') j) ''Cmd'')) (Const Inv)))))) (forallForm (down NC) (\<lambda>i. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const GntS)))))) (forallForm (down NC) (\<lambda>j. (neg (eqn (IVar (Field (Para (Ident ''Chan2'') j) ''Cmd'')) (Const GntE)))))) (forallForm (down NC) (\<lambda>i. (neg (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const S)))))) (forallForm (down NC) (\<lambda>i. (neg (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const E)))))) in
let s = (parallelList [(assign ((Ident ''AuxData''), (Const (index d))))]) in
guard g s"

subsection{*The set of All actual Rules w.r.t. a Protocol Instance with Size $N$*}
definition rules::"nat \<Rightarrow> rule set" where [simp]:
"rules N \<equiv> {r.
(\<exists> i. i\<le>N\<and>r=n_RecvGntE1  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_RecvGntS2  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendGntE3 N i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendGntS4  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_RecvInvAck5  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_RecvInvAck6  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendInvAck7  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendInvAck8  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendInv9  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendInv10  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_RecvReqE11 N i) \<or>
(\<exists> i. i\<le>N\<and>r=n_RecvReqS12 N i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendReqE13  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendReqE14  i) \<or>
(\<exists> i. i\<le>N\<and>r=n_SendReqS15  i) \<or>
(\<exists> i d. i\<le>N\<and>d\<le>N\<and>r=n_Store  i d) \<or>
(r=n_SendGntE3_i_3  ) \<or>
(r=n_SendGntS4_i_3  ) \<or>
(r=n_RecvInvAck5_i_3  ) \<or>
(r=n_RecvReqE11_i_3  ) \<or>
(r=n_RecvReqS12_i_3  ) \<or>
(\<exists> d. d\<le>N\<and>r=n_Store_i_3  d)\<or> r=skipRule
}"



subsection{*Definitions of a Formally Parameterized Invariant Formulas*}

definition inv_239::"nat \<Rightarrow> formula" where [simp]:
"inv_239 j \<equiv>
(implyForm (eqn (IVar (Ident ''ExGntd'')) (Const false)) (neg (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const E))))"

definition inv_236::"nat \<Rightarrow> formula" where [simp]:
"inv_236 i \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const E)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const GntS))))"

definition inv_234::"nat \<Rightarrow> formula" where [simp]:
"inv_234 j \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const E)) (neg (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const InvAck))))"

definition inv_233::"nat \<Rightarrow> formula" where [simp]:
"inv_233 j \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const InvAck)) (neg (eqn (IVar (Ident ''CurCmd'')) (Const Empty))))"

definition inv_232::"nat \<Rightarrow> formula" where [simp]:
"inv_232 i \<equiv>
(implyForm (eqn (IVar (Ident ''ExGntd'')) (Const false)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const GntE))))"

definition inv_231::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_231 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const E)) (eqn (IVar (Para (Ident ''ShrSet'') j)) (Const false))))"

definition inv_226::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_226 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const E)) (eqn (IVar (Para (Ident ''InvSet'') i)) (Const false))))"

definition inv_224::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_224 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const E)) (neg (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const InvAck)))))"

definition inv_223::"nat \<Rightarrow> formula" where [simp]:
"inv_223 i \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck)) (eqn (IVar (Para (Ident ''InvSet'') i)) (Const false)))"

definition inv_219::"nat \<Rightarrow> formula" where [simp]:
"inv_219 j \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const InvAck)) (eqn (IVar (Field (Para (Ident ''Chan2'') j) ''Cmd'')) (Const Empty)))"

definition inv_218::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_218 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck))) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') j) ''Cmd'')) (Const Inv)))))"

definition inv_217::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_217 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const E)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') j) ''Cmd'')) (Const GntE)))))"

definition inv_214::"nat \<Rightarrow> formula" where [simp]:
"inv_214 j \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const InvAck)) (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const I)))"

definition inv_213::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_213 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck))) (neg (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const InvAck)))))"

definition inv_212::"nat \<Rightarrow> formula" where [simp]:
"inv_212 i \<equiv>
(implyForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const false)) (eqn (IVar (Ident ''CurCmd'')) (Const ReqS))) (neg (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck))))"

definition inv_211::"nat \<Rightarrow> formula" where [simp]:
"inv_211 i \<equiv>
(implyForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const false)) (eqn (IVar (Ident ''CurCmd'')) (Const ReqS))) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Inv))))"

definition inv_210::"nat \<Rightarrow> formula" where [simp]:
"inv_210 j \<equiv>
(implyForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const false)) (eqn (IVar (Ident ''CurCmd'')) (Const ReqS))) (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const Empty)))"

definition inv_209::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_209 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const E)) (eqn (IVar (Field (Para (Ident ''Chan2'') j) ''Cmd'')) (Const Empty))))"

definition inv_194::"nat \<Rightarrow> formula" where [simp]:
"inv_194 i \<equiv>
(implyForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const GntS))))"

definition inv_192::"nat \<Rightarrow> formula" where [simp]:
"inv_192 i \<equiv>
(implyForm (eqn (IVar (Ident ''CurCmd'')) (Const Empty)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Inv))))"

definition inv_191::"nat \<Rightarrow> formula" where [simp]:
"inv_191 i \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const E)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const GntE))))"

definition inv_190::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_190 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const E)) (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const I))))"

definition inv_189::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_189 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck)) (neg (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const E)))))"

definition inv_188::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_188 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck))) (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const I))))"

definition inv_186::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_186 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (andForm (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const InvAck)) (eqn (IVar (Ident ''ExGntd'')) (Const true))) (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const I))))"

definition inv_181::"nat \<Rightarrow> formula" where [simp]:
"inv_181 j \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const InvAck)) (neg (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const E))))"

definition inv_180::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_180 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const E)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') j) ''Cmd'')) (Const Inv)))))"

definition inv_176::"nat \<Rightarrow> formula" where [simp]:
"inv_176 i \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck)) (eqn (IVar (Para (Ident ''ShrSet'') i)) (Const true)))"

definition inv_172::"nat \<Rightarrow> formula" where [simp]:
"inv_172 i \<equiv>
(implyForm (eqn (IVar (Ident ''CurCmd'')) (Const Empty)) (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const Empty)))"

definition inv_166::"nat \<Rightarrow> formula" where [simp]:
"inv_166 j \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const InvAck)) (neg (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const S))))"

definition inv_165::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_165 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (andForm (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const InvAck)) (eqn (IVar (Ident ''ExGntd'')) (Const true))) (eqn (IVar (Para (Ident ''ShrSet'') i)) (Const false))))"

definition inv_164::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_164 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const E)) (neg (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const E)))))"

definition inv_161::"nat \<Rightarrow> formula" where [simp]:
"inv_161 i \<equiv>
(implyForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck))) (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Data'')) (IVar (Ident ''AuxData''))))"

definition inv_159::"nat \<Rightarrow> formula" where [simp]:
"inv_159 j \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const E)) (eqn (IVar (Para (Ident ''ShrSet'') j)) (Const true)))"

definition inv_153::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_153 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck))) (eqn (IVar (Para (Ident ''ShrSet'') j)) (Const false))))"

definition inv_143::"nat \<Rightarrow> formula" where [simp]:
"inv_143 j \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const InvAck)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') j) ''Cmd'')) (Const Inv))))"

definition inv_138::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_138 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const E)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const GntS)))))"

definition inv_136::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_136 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const E)) (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const Empty))))"

definition inv_134::"nat \<Rightarrow> formula" where [simp]:
"inv_134 i \<equiv>
(implyForm (eqn (IVar (Ident ''CurCmd'')) (Const Empty)) (neg (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck))))"

definition inv_125::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_125 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (andForm (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const InvAck)) (eqn (IVar (Ident ''ExGntd'')) (Const true))) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Inv)))))"

definition inv_113::"nat \<Rightarrow> formula" where [simp]:
"inv_113 j \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const InvAck)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') j) ''Cmd'')) (Const GntS))))"

definition inv_111::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_111 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (andForm (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const InvAck)) (eqn (IVar (Ident ''ExGntd'')) (Const true))) (neg (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck)))))"

definition inv_110::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_110 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (andForm (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const InvAck)) (eqn (IVar (Ident ''ExGntd'')) (Const true))) (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Empty))))"

definition inv_108::"nat \<Rightarrow> formula" where [simp]:
"inv_108 j \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const InvAck)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') j) ''Cmd'')) (Const GntE))))"

definition inv_106::"nat \<Rightarrow> formula" where [simp]:
"inv_106 j \<equiv>
(implyForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (neg (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const S))))"

definition inv_100::"nat \<Rightarrow> formula" where [simp]:
"inv_100 j \<equiv>
(implyForm (andForm (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const InvAck)) (eqn (IVar (Ident ''ExGntd'')) (Const true))) (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Data'')) (IVar (Ident ''AuxData''))))"

definition inv_99::"nat \<Rightarrow> formula" where [simp]:
"inv_99 j \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const E)) (eqn (IVar (Field (Para (Ident ''Cache'') j) ''Data'')) (IVar (Ident ''AuxData''))))"

definition inv_91::"formula" where [simp]:
"inv_91  \<equiv>
(implyForm (eqn (IVar (Ident ''ExGntd'')) (Const false)) (eqn (IVar (Ident ''MemData'')) (IVar (Ident ''AuxData''))))"

definition inv_89::"nat \<Rightarrow> formula" where [simp]:
"inv_89 j \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const E)) (eqn (IVar (Ident ''ExGntd'')) (Const true)))"

definition inv_66::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_66 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck)) (neg (eqn (IVar (Field (Para (Ident ''Chan2'') j) ''Cmd'')) (Const GntE)))))"

definition inv_59::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_59 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (andForm (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const InvAck)) (eqn (IVar (Ident ''ExGntd'')) (Const true))) (eqn (IVar (Para (Ident ''InvSet'') i)) (Const false))))"

definition inv_47::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_47 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck))) (eqn (IVar (Para (Ident ''InvSet'') j)) (Const false))))"

definition inv_44::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_44 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const E)) (neg (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const S)))))"

definition inv_32::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_32 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck))) (eqn (IVar (Field (Para (Ident ''Chan2'') j) ''Cmd'')) (Const Empty))))"

definition inv_17::"nat \<Rightarrow> formula" where [simp]:
"inv_17 j \<equiv>
(implyForm (eqn (IVar (Field (Para (Ident ''Cache'') j) ''State'')) (Const E)) (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const Empty)))"

definition inv_15::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_15 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (andForm (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const InvAck)) (eqn (IVar (Ident ''ExGntd'')) (Const true))) (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const Empty))))"

definition inv_2::"nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
"inv_2 i j \<equiv>
(implyForm (neg (eqn (Const (index i)) (Const (index j)))) (implyForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const InvAck))) (eqn (IVar (Field (Para (Ident ''Chan3'') j) ''Cmd'')) (Const Empty))))"

subsection{*Definitions of  the Set of Invariant Formula Instances in a $N$-protocol Instance*}
definition invariants::"nat \<Rightarrow> formula set" where [simp]:
"invariants N \<equiv> {f.
(\<exists> j. j\<le>N\<and>f=inv_239  j) \<or>
(\<exists> i. i\<le>N\<and>f=inv_236  i) \<or>
(\<exists> j. j\<le>N\<and>f=inv_234  j) \<or>
(\<exists> j. j\<le>N\<and>f=inv_233  j) \<or>
(\<exists> i. i\<le>N\<and>f=inv_232  i) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_231  i j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_226  i j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_224  i j) \<or>
(\<exists> i. i\<le>N\<and>f=inv_223  i) \<or>
(\<exists> j. j\<le>N\<and>f=inv_219  j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_218  i j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_217  i j) \<or>
(\<exists> j. j\<le>N\<and>f=inv_214  j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_213  i j) \<or>
(\<exists> i. i\<le>N\<and>f=inv_212  i) \<or>
(\<exists> i. i\<le>N\<and>f=inv_211  i) \<or>
(\<exists> j. j\<le>N\<and>f=inv_210  j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_209  i j) \<or>
(\<exists> i. i\<le>N\<and>f=inv_194  i) \<or>
(\<exists> i. i\<le>N\<and>f=inv_192  i) \<or>
(\<exists> i. i\<le>N\<and>f=inv_191  i) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_190  i j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_189  i j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_188  i j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_186  i j) \<or>
(\<exists> j. j\<le>N\<and>f=inv_181  j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_180  i j) \<or>
(\<exists> i. i\<le>N\<and>f=inv_176  i) \<or>
(\<exists> i. i\<le>N\<and>f=inv_172  i) \<or>
(\<exists> j. j\<le>N\<and>f=inv_166  j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_165  i j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_164  i j) \<or>
(\<exists> i. i\<le>N\<and>f=inv_161  i) \<or>
(\<exists> j. j\<le>N\<and>f=inv_159  j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_153  i j) \<or>
(\<exists> j. j\<le>N\<and>f=inv_143  j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_138  i j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_136  i j) \<or>
(\<exists> i. i\<le>N\<and>f=inv_134  i) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_125  i j) \<or>
(\<exists> j. j\<le>N\<and>f=inv_113  j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_111  i j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_110  i j) \<or>
(\<exists> j. j\<le>N\<and>f=inv_108  j) \<or>
(\<exists> j. j\<le>N\<and>f=inv_106  j) \<or>
(\<exists> j. j\<le>N\<and>f=inv_100  j) \<or>
(\<exists> j. j\<le>N\<and>f=inv_99  j) \<or>
(f=inv_91  ) \<or>
(\<exists> j. j\<le>N\<and>f=inv_89  j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_66  i j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_59  i j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_47  i j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_44  i j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_32  i j) \<or>
(\<exists> j. j\<le>N\<and>f=inv_17  j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_15  i j) \<or>
(\<exists> i j. i\<le>N\<and>j\<le>N\<and>i~=j\<and>f=inv_2  i j)
}" 

subsection{*Definitions of  the Set of Abs Invariant Formula Instances *}
definition invariantsAbs  ::"  formula list" where [simp]:
"invariantsAbs   \<equiv> [
inv_239 0 ,
inv_239 1 ,
inv_236 0 ,
inv_236 1 ,
inv_234 0 ,
inv_234 1 ,
inv_233 0 ,
inv_233 1 ,
inv_232 0 ,
inv_232 1 ,
inv_231 0 1 ,
inv_231 1 0 ,
inv_226 0 1 ,
inv_226 1 0 ,
inv_224 0 1 ,
inv_224 1 0 ,
inv_223 0 ,
inv_223 1 ,
inv_219 0 ,
inv_219 1 ,
inv_218 0 1 ,
inv_218 1 0 ,
inv_217 0 1 ,
inv_217 1 0 ,
inv_214 0 ,
inv_214 1 ,
inv_213 0 1 ,
inv_213 1 0 ,
inv_212 0 ,
inv_212 1 ,
inv_211 0 ,
inv_211 1 ,
inv_210 0 ,
inv_210 1 ,
inv_209 0 1 ,
inv_209 1 0 ,
inv_194 0 ,
inv_194 1 ,
inv_192 0 ,
inv_192 1 ,
inv_191 0 ,
inv_191 1 ,
inv_190 0 1 ,
inv_190 1 0 ,
inv_189 0 1 ,
inv_189 1 0 ,
inv_188 0 1 ,
inv_188 1 0 ,
inv_186 0 1 ,
inv_186 1 0 ,
inv_181 0 ,
inv_181 1 ,
inv_180 0 1 ,
inv_180 1 0 ,
inv_176 0 ,
inv_176 1 ,
inv_172 0 ,
inv_172 1 ,
inv_166 0 ,
inv_166 1 ,
inv_165 0 1 ,
inv_165 1 0 ,
inv_164 0 1 ,
inv_164 1 0 ,
inv_161 0 ,
inv_161 1 ,
inv_159 0 ,
inv_159 1 ,
inv_153 0 1 ,
inv_153 1 0 ,
inv_143 0 ,
inv_143 1 ,
inv_138 0 1 ,
inv_138 1 0 ,
inv_136 0 1 ,
inv_136 1 0 ,
inv_134 0 ,
inv_134 1 ,
inv_125 0 1 ,
inv_125 1 0 ,
inv_113 0 ,
inv_113 1 ,
inv_111 0 1 ,
inv_111 1 0 ,
inv_110 0 1 ,
inv_110 1 0 ,
inv_108 0 ,
inv_108 1 ,
inv_106 0 ,
inv_106 1 ,
inv_100 0 ,
inv_100 1 ,
inv_99 0 ,
inv_99 1 ,
inv_91 ,
inv_89 0 ,
inv_89 1 ,
inv_66 0 1 ,
inv_66 1 0 ,
inv_59 0 1 ,
inv_59 1 0 ,
inv_47 0 1 ,
inv_47 1 0 ,
inv_44 0 1 ,
inv_44 1 0 ,
inv_32 0 1 ,
inv_32 1 0 ,
inv_17 0 ,
inv_17 1 ,
inv_15 0 1 ,
inv_15 1 0 ,
inv_2 0 1 ,
inv_2 1 0
]"

definition initSpec0::"nat \<Rightarrow> formula" where [simp]:
"initSpec0 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Field (Para (Ident ''Chan1'') i) ''Cmd'')) (Const Empty))))"

definition initSpec1::"nat \<Rightarrow> formula" where [simp]:
"initSpec1 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Field (Para (Ident ''Chan2'') i) ''Cmd'')) (Const Empty))))"

definition initSpec2::"nat \<Rightarrow> formula" where [simp]:
"initSpec2 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Field (Para (Ident ''Chan3'') i) ''Cmd'')) (Const Empty))))"

definition initSpec3::"nat \<Rightarrow> formula" where [simp]:
"initSpec3 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Field (Para (Ident ''Cache'') i) ''State'')) (Const I))))"

definition initSpec4::"nat \<Rightarrow> formula" where [simp]:
"initSpec4 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Para (Ident ''InvSet'') i)) (Const false))))"

definition initSpec5::"nat \<Rightarrow> formula" where [simp]:
"initSpec5 N \<equiv> (forallForm (down N) (% i . (eqn (IVar (Para (Ident ''ShrSet'') i)) (Const false))))"

definition initSpec6::"formula" where [simp]:
"initSpec6  \<equiv> (eqn (IVar (Ident ''ExGntd'')) (Const false))"

definition initSpec7::"formula" where [simp]:
"initSpec7  \<equiv> (eqn (IVar (Ident ''CurCmd'')) (Const Empty))"

definition initSpec8::"formula" where [simp]:
"initSpec8  \<equiv> (eqn (IVar (Ident ''MemData'')) (Const (index 1)))"

definition initSpec9::"formula" where [simp]:
"initSpec9  \<equiv> (eqn (IVar (Ident ''AuxData'')) (Const (index 1)))"

definition allInitSpecs::"nat \<Rightarrow> formula list" where [simp]:
"allInitSpecs N \<equiv> [
(initSpec0 N),
(initSpec1 N),
(initSpec2 N),
(initSpec3 N),
(initSpec4 N),
(initSpec5 N),
(initSpec6 ),
(initSpec7 ),
(initSpec8 ),
(initSpec9 )
]"
axiomatization  where axiomOnf2 [simp,intro]:
   "s ∈ reachableSet (set (allInitSpecs N )) (rules N) \<Longrightarrow> i\<noteq>j  \<Longrightarrow> formEval (f 0 1) s \<Longrightarrow> formEval (f i j) s"
axiomatization  where axiomOnf1 [simp,intro]:
   "s ∈ reachableSet (set (allInitSpecs N )) (rules N)  \<Longrightarrow>formEval (f 0 ) s \<Longrightarrow> formEval (f i) s"




subsection{*Definitions of initial states*}

lemma lemmaOnn_RecvGntE1Gt_i:
  assumes a1:"NC<i" and a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
shows "trans_sim_on2 (n_RecvGntE1  i  ) skipRule VF (set invariantsAbs) s" (is "trans_sim_on2 ?r ?r' VF ?F s")
proof(unfold trans_sim_on2_def,(rule allI)+,(rule impI)+,rule disjI2)
  fix s2 
  assume b0:"state_sim_on2 s s2 VF "
  show "state_sim_on2 (trans (act (n_RecvGntE1  i)) s) s2  VF"
  proof(cut_tac a1,unfold state_sim_on2_def,
    (rule allI)+,(rule impI)+)
    fix f v
    assume b1:" v \<in>  VF"  
    
    have b5:"trans (act (n_RecvGntE1  i)) s v = s v" 
      by (cut_tac a1  b1,auto) 

    have b6:"s v =s2 v "
      using b0 b1 state_sim_on2_def by blast  
    show "trans (act (n_RecvGntE1  i)) s v= s2 v"
      using b5 b6 by auto 
  qed
qed
lemma lemmaOnn_RecvGntE1LeNc_:
  assumes a1:"i\<le>NC"  and a3:"NC\<le>N" 
  shows "trans_sim_on2 (n_RecvGntE1  i) (n_RecvGntE1  i) VF  (set invariantsAbs) s" (is "trans_sim_on2 ?r ?r' VF ?F s")
proof(rule ruleSimCond2)
     from a3 show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")  
       apply (auto simp del:evalEqn)done
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r') \<longrightarrow>  v \<in> VF \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
     assume b1:"v\<in> VF"  and b2:"formEval (pre ?r) s" and b3:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 b1 b2 b3,auto) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" by(cut_tac a1, auto)

  
 next 
   show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow>va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r'))\<longrightarrow> va \<in> VF "
     by(cut_tac a1, auto) 
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow> v \<in> VF" by(cut_tac a1, auto)
 qed
lemma lemmaOnn_RecvGntE1: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_RecvGntE1  i"  and
  a6:"NC \<le> N"
  shows "∃ r'. r' \<in> rules NC∧ trans_sim_on2 r r' VF (set invariantsAbs) s" (is "∃r'.?P1 r' ∧ ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_RecvGntE1  i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "∃r'. ?P1 r' ∧ ?P2 r'"
        proof(rule_tac x="(skipRule)" in exI,rule conjI)
          show  "?P1 (skipRule) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (skipRule) "
           using lemmaOnn_RecvGntE1Gt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "∃r'. ?P1 r' ∧ ?P2 r'"
        proof(rule_tac x="(n_RecvGntE1  i)" in exI,rule conjI)
          show  "?P1 (n_RecvGntE1  i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_RecvGntE1  i) "
           using lemmaOnn_RecvGntE1LeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "∃r'.?P1 r' ∧ ?P2 r'" 
    by satx
qed

lemma lemmaOnn_RecvGntS2Gt_i:
  assumes a1:"NC<i" and a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
shows "trans_sim_on2 (n_RecvGntS2  i  ) skipRule VF (set invariantsAbs) s" (is "trans_sim_on2 ?r ?r' VF ?F s")
proof(unfold trans_sim_on2_def,(rule allI)+,(rule impI)+,rule disjI2)
  fix s2 
  assume b0:"state_sim_on2 s s2 VF "
  show "state_sim_on2 (trans (act (n_RecvGntS2  i)) s) s2  VF"
  proof(cut_tac a1,unfold state_sim_on2_def,
    (rule allI)+,(rule impI)+)
    fix f v
    assume b1:" v \<in>  VF"  
    
    have b5:"trans (act (n_RecvGntS2  i)) s v = s v" 
      by (cut_tac a1  b1,auto) 

    have b6:"s v =s2 v "
      using b0 b1 state_sim_on2_def by blast  
    show "trans (act (n_RecvGntS2  i)) s v= s2 v"
      using b5 b6 by auto 
  qed
qed
lemma lemmaOnn_RecvGntS2LeNc_:
  assumes a1:"i\<le>NC"  and a3:"NC\<le>N" 
  shows "trans_sim_on2 (n_RecvGntS2  i) (n_RecvGntS2  i) VF  (set invariantsAbs) s" (is "trans_sim_on2 ?r ?r' VF ?F s")
proof(rule ruleSimCond2)
     from a3 show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")  
       apply (auto simp del:evalEqn)done
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r') \<longrightarrow>  v \<in> VF \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
     assume b1:"v\<in> VF"  and b2:"formEval (pre ?r) s" and b3:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 b1 b2 b3,auto) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" by(cut_tac a1, auto)

  
 next 
   show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow>va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r'))\<longrightarrow> va \<in> VF "
     by(cut_tac a1, auto) 
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow> v \<in> VF" by(cut_tac a1, auto)
 qed
lemma lemmaOnn_RecvGntS2: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_RecvGntS2  i"  and
  a6:"NC \<le> N"
  shows "∃ r'. r' \<in> rules NC∧ trans_sim_on2 r r' VF (set invariantsAbs) s" (is "∃r'.?P1 r' ∧ ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_RecvGntS2  i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "∃r'. ?P1 r' ∧ ?P2 r'"
        proof(rule_tac x="(skipRule)" in exI,rule conjI)
          show  "?P1 (skipRule) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (skipRule) "
           using lemmaOnn_RecvGntS2Gt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "∃r'. ?P1 r' ∧ ?P2 r'"
        proof(rule_tac x="(n_RecvGntS2  i)" in exI,rule conjI)
          show  "?P1 (n_RecvGntS2  i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_RecvGntS2  i) "
           using lemmaOnn_RecvGntS2LeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "∃r'.?P1 r' ∧ ?P2 r'" 
    by satx
qed

lemma lemmaOnn_SendGntE3Gt_i:
  assumes a1:"i>NC" and 
  a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and a3:"NC\<le>N" and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
  shows "trans_sim_on2 (n_SendGntE3 N i)  (n_SendGntE3_i_3 ) VF (set invariantsAbs) s" (is "trans_sim_on2 ?r ?r' VF (set ?F) s")
  proof(rule ruleSimCond2)
    show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")
    proof(rule impI)+
      assume b0:"?A"
  from a4  have tmp:"formEval (inv_239 0)  s"   
            by (force simp del:inv_239_def)
        	 with b0 a1 have c0:"formEval  (conclude (inv_239 0)) s" by auto
from a4  have tmp:"formEval (inv_239 1)  s"   
            by (force simp del:inv_239_def)
        	 with b0 a1 have c1:"formEval  (conclude (inv_239 1)) s" by auto
from a4  have tmp:"formEval (inv_232 0)  s"   
            by (force simp del:inv_232_def)
        	 with b0 a1 have c2:"formEval  (conclude (inv_232 0)) s" by auto
from a4  have tmp:"formEval (inv_232 1)  s"   
            by (force simp del:inv_232_def)
        	 with b0 a1 have c3:"formEval  (conclude (inv_232 1)) s" by auto
from a4  have tmp:"formEval (inv_91)  s"   
            by (force simp del:inv_91_def)
        	 with b0 a1 have c4:"formEval  (conclude (inv_91)) s" by auto

      from a1 a3 b0 c0 c1 c2 c3 c4 show "formEval (pre ?r') s" 
       by (auto simp del:evalEqn)
     qed
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r') \<longrightarrow>  v \<in> VF \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
     assume b1:"v\<in> VF"  and b2:"formEval (pre ?r) s" and b3:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 b1 b2 ,auto ) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" by(cut_tac a1, auto)

  
 next 
   show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow>va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r'))\<longrightarrow> va \<in> VF "
     by auto  
 next
   show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow> v \<in> VF" by auto
qed
lemma lemmaOnn_SendGntE3LeNc_:
  assumes a1:"i\<le>NC"  and a3:"NC\<le>N" 
  shows "trans_sim_on2 (n_SendGntE3 N i) (n_SendGntE3 NC i) VF  (set invariantsAbs) s" (is "trans_sim_on2 ?r ?r' VF ?F s")
proof(rule ruleSimCond2)
     from a3 show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")  
       apply (auto simp del:evalEqn)done
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r') \<longrightarrow>  v \<in> VF \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
     assume b1:"v\<in> VF"  and b2:"formEval (pre ?r) s" and b3:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 b1 b2 b3,auto) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" by(cut_tac a1, auto)

  
 next 
   show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow>va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r'))\<longrightarrow> va \<in> VF "
     by(cut_tac a1, auto) 
 next
   from a1 show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow> v \<in> VF" by(cut_tac a1, auto)
 qed
lemma lemmaOnn_SendGntE3: 
  assumes   a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" and a5:"\<exists> i. i\<le>N\<and>r=n_SendGntE3 N i"  and
  a6:"NC \<le> N"
  shows "∃ r'. r' \<in> rules NC∧ trans_sim_on2 r r' VF (set invariantsAbs) s" (is "∃r'.?P1 r' ∧ ?P2 r'")
proof -
  from a5 obtain i where d0:"i\<le>N\<and>r=n_SendGntE3 N i"  by blast
  have "i>NC|i\<le> NC" by auto
  moreover{
       assume a1:"i>NC" 
        have "∃r'. ?P1 r' ∧ ?P2 r'"
        proof(rule_tac x="(n_SendGntE3_i_3 )" in exI,rule conjI)
          show  "?P1 (n_SendGntE3_i_3 ) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_SendGntE3_i_3 ) "
           using lemmaOnn_SendGntE3Gt_i local.a1 a2 a4 a6 d0 by blast 
        qed
       }
moreover{
       assume a1:"i\<le> NC" 
        have "∃r'. ?P1 r' ∧ ?P2 r'"
        proof(rule_tac x="(n_SendGntE3 NC i)" in exI,rule conjI)
          show  "?P1 (n_SendGntE3 NC i) " 
           by(cut_tac a1, auto) 
          next
          show  "?P2 (n_SendGntE3 NC i) "
           using lemmaOnn_SendGntE3LeNc_ local.a1 a2 a4 a6 d0 by blast 
        qed
       }
  ultimately show "∃r'.?P1 r' ∧ ?P2 r'" 
    by satx
qed

lemma lemmaOnn_SendGntS4Gt_i:
  assumes a1:"i>NC" and 
  a2:"s \<in> reachableSet (set (allInitSpecs N)) (rules N)"  and a3:"NC\<le>N" and  
  a4:"\<forall>f.  f \<in>(set invariantsAbs) \<longrightarrow>  formEval f s" 
  shows "trans_sim_on2 (n_SendGntS4  i)  (n_SendGntS4_i_3 ) VF (set invariantsAbs) s" (is "trans_sim_on2 ?r ?r' VF (set ?F) s")
  proof(rule ruleSimCond2)
    show " formEval (pre ?r) s \<longrightarrow>formEval (pre ?r') s" (is "?A \<longrightarrow>?B")
    proof(rule impI)+
      assume b0:"?A"
      from a4  have tmp0:"(inv_239 0) \<in> (set invariantsAbs)" by( simp del:inv_239_def)
      then have tmp:"formEval (inv_239 0)  s"   
            by (force simp del:inv_239_def)
        	 with b0 a1 have c0:"formEval  (conclude (inv_239 0)) s" by auto
from a4  have tmp:"formEval (inv_239 1)  s"   
            by (force simp del:inv_239_def)
        	 with b0 a1 have c1:"formEval  (conclude (inv_239 1)) s" by auto
from a4  have tmp:"formEval (inv_232 0)  s"   
            by (force simp del:inv_232_def)
        	 with b0 a1 have c2:"formEval  (conclude (inv_232 0)) s" by auto
from a4  have tmp:"formEval (inv_232 1)  s"   
            by (force simp del:inv_232_def)
        	 with b0 a1 have c3:"formEval  (conclude (inv_232 1)) s" by auto
from a4  have tmp:"formEval (inv_212 0)  s"   
            by (force simp del:inv_212_def)
        	 with b0 a1 have c4:"formEval  (conclude (inv_212 0)) s" by auto
from a4  have tmp:"formEval (inv_212 1)  s"   
            by (force simp del:inv_212_def)
        	 with b0 a1 have c5:"formEval  (conclude (inv_212 1)) s" by auto
from a4  have tmp:"formEval (inv_211 0)  s"   
            by (force simp del:inv_211_def)
        	 with b0 a1 have c6:"formEval  (conclude (inv_211 0)) s" by auto
from a4  have tmp:"formEval (inv_211 1)  s"   
            by (force simp del:inv_211_def)
        	 with b0 a1 have c7:"formEval  (conclude (inv_211 1)) s" by auto
from a4  have tmp:"formEval (inv_210 0)  s"   
            by (force simp del:inv_210_def)
        	 with b0 a1 have c8:"formEval  (conclude (inv_210 0)) s" by auto
from a4  have tmp:"formEval (inv_210 1)  s"   
            by (force simp del:inv_210_def)
        	 with b0 a1 have c9:"formEval  (conclude (inv_210 1)) s" by auto
from a4  have tmp:"formEval (inv_91)  s"   
            by (force simp del:inv_91_def)
        	 with b0 a1 have c10:"formEval  (conclude (inv_91)) s" by auto

      from a1 a3 b0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 show "formEval (pre ?r') s" 
       by (auto simp del:evalEqn)
     qed
   next 
	show "(\<forall>  v. v \<in>  varOfSent (act  ?r') \<longrightarrow>  v \<in> VF \<longrightarrow> formEval (pre ?r) s \<longrightarrow> 
    expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s)"
   proof(rule allI,(rule impI)+)
      fix  v
     assume b1:"v\<in> VF"  and b2:"formEval (pre ?r) s" and b3:"v \<in>varOfSent (act ?r')"
  
  show "expEval (substExpByStatement (IVar v)  (act ?r')) s = expEval (substExpByStatement (IVar v)  (act ?r)) s"  
       apply (cut_tac  a1 b1 b2 ,auto ) done
   qed
 next
   show "\<forall>  v. v \<in>  varOfSent (act ?r) \<longrightarrow>  v \<in> VF \<longrightarrow> v \<in>  varOfSent (act ?r')" by(cut_tac a1, auto)

  
 next 
   show "\<forall> v va. v \<in> varOfSent (act ?r') \<longrightarrow>va\<in>varOfExp ( substExpByStatement (IVar v)  (act ?r'))\<longrightarrow> va \<in> VF "
     by auto  
 next
   show "\<forall>v. v \<in> varOfForm (pre (?r')) \<longrightarrow> v \<in> VF" by auto
qed
end