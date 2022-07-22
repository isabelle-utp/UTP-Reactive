section \<open> Reactive Healthiness Conditions \<close>

theory utp_rea_healths
  imports utp_rea_core
begin

subsection \<open> R1: Events cannot be undone \<close>

definition R1 :: "('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" where
R1_def [pred]: "R1 (P) = (P \<and> tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e"

expr_ctr R1

lemma R1_idem: "R1(R1(P)) = R1(P)"
  by pred_auto

lemma R1_Idempotent [closure]: "Idempotent R1"
  by (simp add: Idempotent_def R1_idem)

lemma R1_mono: "P \<sqsubseteq> Q \<Longrightarrow> R1(P) \<sqsubseteq> R1(Q)"
  by pred_auto

lemma R1_Monotonic: "Monotonic R1"
  by (simp add: mono_def R1_mono)
     (pred_auto)

lemma R1_Continuous: "Continuous R1"
  by (simp add: Continuous_def, pred_auto)

(*
lemma R1_unrest: "\<lbrakk> x \<bowtie> in_var tr; x \<bowtie> out_var tr; x \<sharp> P \<rbrakk> \<Longrightarrow> x \<sharp> R1(P)"
  by (simp add: R1_def unrest lens_indep_sym)
*)

lemma R1_false: "R1(false) = false"
  by pred_auto


lemma R1_conj: "R1(P \<and> Q) = (R1(P) \<and> R1(Q))"
  by pred_auto

lemma conj_R1_closed_1 [closure]: "P is R1 \<Longrightarrow> (P \<and> Q) is R1"
  by (simp add: Healthy_def, pred_auto)

lemma conj_R1_closed_2 [closure]: "Q is R1 \<Longrightarrow> (P \<and> Q) is R1"
  by (simp add: Healthy_def, pred_auto)

lemma R1_disj: "R1(P \<or> Q) = (R1(P) \<or> R1(Q))"
  by pred_auto

lemma disj_R1_closed [closure]: "\<lbrakk> P is R1; Q is R1 \<rbrakk> \<Longrightarrow> (P \<or> Q) is R1"
  by (simp add: Healthy_def R1_def; pred_auto; blast)

lemma 1: "(P \<and> Q) = (\<lambda> s. P s \<and> Q s)"
  by (metis conj_pred_def inf1E inf1I)

lemma 2: "(P \<or> Q) = (\<lambda> s. P s \<or> Q s)"
  by (metis disj_pred_def sup1CI sup1E)

lemma 3: "(\<not> P) = (\<lambda> s. \<not> (P s))"
  by (simp add: fun_Compl_def not_pred_def)

lemma "((P::'s pred) \<longrightarrow> (Q::'s pred)) = (\<not>P \<or> Q)"
  by (simp add: impl_pred_def fun_eq_iff 1 2 3)

lemma R1_impl: "R1(P \<longrightarrow> Q) = ((\<not> R1(\<not> P)) \<longrightarrow> R1(Q))"
  by (simp add: R1_def; pred_auto)

lemma R1_inf: "R1(P \<sqinter> Q) = (R1(P) \<sqinter> R1(Q))"
  by pred_auto

(*
lemma R1_USUP:
  "R1(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> R1(P(i)))"
  by (rel_auto)

lemma R1_Sup [closure]: "\<lbrakk> \<And> P. P \<in> A \<Longrightarrow> P is R1; A \<noteq> {} \<rbrakk> \<Longrightarrow> \<Sqinter> A is R1"
  using R1_Continuous by (auto simp add: Continuous_def Healthy_def)

*)

(* .... *)

subsection \<open> R2: No dependence upon trace history \<close>

text \<open> There are various ways of expressing $R2$, which are enumerated below. \<close>

definition R2a :: "('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp" where
[pred]: "R2a (P) = (\<Sqinter> s. P\<lbrakk>\<guillemotleft>s\<guillemotright>,(\<guillemotleft>s\<guillemotright>+(tr\<^sup>>-tr\<^sup><))/tr\<^sup><,tr\<^sup>>\<rbrakk>)\<^sub>e"

(* ... *)


end
