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

(* .... *)

subsection \<open> R2: No dependence upon trace history \<close>

text \<open> There are various ways of expressing $R2$, which are enumerated below. \<close>

definition R2a :: "('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp" where
[pred]: "R2a (P) = (\<Sqinter> s. P\<lbrakk>\<guillemotleft>s\<guillemotright>,(\<guillemotleft>s\<guillemotright>+(tr\<^sup>>-tr\<^sup><))/tr\<^sup><,tr\<^sup>>\<rbrakk>)\<^sub>e"

(* ... *)


end
