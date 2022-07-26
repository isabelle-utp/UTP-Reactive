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
lemma R1_unrest:
  assumes "x \<bowtie> (tr ;\<^sub>L fst\<^sub>L)" "x \<bowtie> (tr ;\<^sub>L snd\<^sub>L)" "unrest ($x) P"
  shows "unrest ($x) (R1 P)"
proof -
  assume "mwb_lens x"
  have 1: "unrest ($x) (tr\<^sup><)\<^sub>e"
    using assms(1) apply(unrest)
    oops
    
qed
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

lemma R1_USUP:
  "R1 (\<Sqinter>i \<in> A. P i) = (\<Sqinter> i \<in> A. R1 (P i))"
  by (simp add: fun_eq_iff R1_def)

lemma R1_Sup [closure]: "\<lbrakk> \<And> P. P \<in> A \<Longrightarrow> P is R1; A \<noteq> {} \<rbrakk> \<Longrightarrow> \<Sqinter> A is R1"
  using R1_Continuous by (auto simp add: Continuous_def Healthy_def)

lemma R1_UINF:
  assumes "A \<noteq> {}"
  shows "R1(\<Squnion> i \<in> A. P(i)) = (\<Squnion> i \<in> A. R1(P(i)))"
  by (pred_auto assms: assms)

lemma R1_UINF_ind:
  "R1(\<Squnion> i. P(i)) = (\<Squnion> i. R1(P(i)))"
  by pred_auto

lemma UINF_ind_R1_closed [closure]:
  "\<lbrakk> \<And> i. P(i) is R1 \<rbrakk> \<Longrightarrow> (\<Sqinter> i. P(i)) is R1"
  by (simp add: Healthy_def; pred_auto; blast)


lemma UINF_R1_closed [closure]:
  "\<lbrakk> \<And> i. P i is R1 \<rbrakk> \<Longrightarrow> (\<Sqinter> i \<in> A. P i) is R1"
  by (simp add: Healthy_def; pred_auto; blast)


lemma tr_ext_conj_R1 [closure]: 
  "(tr\<^sup>> = tr\<^sup>< @ e)\<^sub>e \<and> P is R1"
  by (simp add: Healthy_def; pred_auto)

lemma tr_id_conj_R1 [closure]: 
  "(tr\<^sup>> = tr\<^sup><)\<^sub>e \<and> P is R1"
  by (simp add: Healthy_def; pred_auto)

lemma R1_extend_conj: "R1(P \<and> Q) = (R1(P) \<and> Q)"
  by pred_auto

lemma R1_extend_conj': "R1(P \<and> Q) = (P \<and> R1(Q))"
  by pred_auto

lemma R1_cond: "R1(P \<triangleleft> b \<triangleright> Q) = (R1(P) \<triangleleft> b \<triangleright> R1(Q))"
  by pred_auto

lemma R1_cond': "R1(P \<triangleleft> b \<triangleright> Q) = (R1(P) \<triangleleft> R1(b) \<triangleright> R1(Q))"
  by pred_auto

lemma R1_negate_R1: "R1(\<not> R1(P)) = R1(\<not> P)"
  by pred_auto

lemma R1_wait_true [usubst]: "(R1 P)\<^sub>t = R1(P)\<^sub>t"
  by pred_auto

lemma R1_wait_false [usubst]: "(R1 P) \<^sub>f = R1(P) \<^sub>f"
  by pred_auto

lemma R1_wait'_true [usubst]: "(R1 P)\<lbrakk>True/wait\<^sup>>\<rbrakk> = R1(P\<lbrakk>True/wait\<^sup>>\<rbrakk>)"
  by pred_auto

term "P\<lbrakk>False/wait\<^sup>>\<rbrakk>"
(* term "[wait\<^sup>> \<leadsto> false] \<dagger> P" *)

lemma R1_wait'_false [usubst]: "(R1 P)\<lbrakk>False/wait\<^sup>>\<rbrakk> = R1(P\<lbrakk>False/wait\<^sup>>\<rbrakk>)"
  by pred_auto

lemma R1_wait_false_closed [closure]: "P is R1 \<Longrightarrow> P\<lbrakk>False/wait\<^sup><\<rbrakk> is R1"
  by (simp add: Healthy_def; pred_auto)
     (metis rea_vars.select_convs(2) rea_vars.surjective rea_vars.update_convs(1))

lemma R1_wait'_false_closed [closure]: "P is R1 \<Longrightarrow> P\<lbrakk>False/wait\<^sup>>\<rbrakk> is R1"
  by (simp add: Healthy_def; pred_auto)
     (metis rea_vars.select_convs(2) rea_vars.surjective rea_vars.update_convs(1))

lemma R1_skip: "R1(II) = II"
  by pred_auto

lemma skip_is_R1 [closure]: "II is R1"
  by (simp add: Healthy_def R1_skip)

(* Belongs in UTP *)
text \<open> If a variable is unrestricted in a substitution then it's application has no effect. \<close>

lemma usubst_apply_unrest:
  "\<lbrakk> vwb_lens x; $x \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>s x = var x"
proof -
  assume 1: "vwb_lens x" and "$x \<sharp>\<^sub>s \<sigma>"
  hence "\<forall>s s'. \<sigma> (s \<oplus>\<^sub>L s' on x) = \<sigma> s \<oplus>\<^sub>L s' on x"
    by (simp add: unrest_usubst_def)
  thus "\<langle>\<sigma>\<rangle>\<^sub>s x = var x"
    by (metis 1 lens_override_def lens_override_idem mwb_lens_weak subst_lookup_def vwb_lens_mwb weak_lens.put_get)
qed

lemma subst_R1:
  assumes "$tr\<^sup>< \<sharp>\<^sub>s \<sigma>" "$tr\<^sup>> \<sharp>\<^sub>s \<sigma>"
  shows   "\<sigma> \<dagger> (R1 P) = R1(\<sigma> \<dagger> P)"
proof -
  have "\<langle>\<sigma>\<rangle>\<^sub>s (tr ;\<^sub>L fst\<^sub>L) = var (tr ;\<^sub>L fst\<^sub>L)"
    using assms(1)
    by (simp add: comp_vwb_lens ns_alpha_def usubst_apply_unrest)
  moreover have "\<langle>\<sigma>\<rangle>\<^sub>s (tr ;\<^sub>L snd\<^sub>L) = var (tr ;\<^sub>L snd\<^sub>L)"
    using assms(2)
    by (simp add: comp_vwb_lens ns_alpha_def usubst_apply_unrest)
  ultimately show ?thesis
    by pred_auto
qed
  
lemma subst_R1_closed [closure]: "\<lbrakk> $tr\<^sup>< \<sharp>\<^sub>s \<sigma>; $tr\<^sup>> \<sharp>\<^sub>s \<sigma>; P is R1 \<rbrakk> \<Longrightarrow> \<sigma> \<dagger> P is R1"
  by (metis Healthy_def subst_R1)


lemma R1_by_refinement:
  "P is R1 \<longleftrightarrow> ((tr\<^sup>< \<le> tr\<^sup>>)\<^sub>e \<sqsubseteq> P)"
  by (simp add: Healthy_def; pred_auto)

lemma R1_trace_extension [closure]:
  "(tr\<^sup>> \<ge> tr\<^sup>< @ e)\<^sub>e is R1"
  by (simp add: Healthy_def; pred_auto)

lemma tr_le_trans:
  "((tr\<^sup>< \<le> tr\<^sup>>)\<^sub>e ;; (tr\<^sup>< \<le> tr\<^sup>>)\<^sub>e) = (tr\<^sup>< \<le> tr\<^sup>>)\<^sub>e"
  by (pred_auto; metis order_refl rea_vars.select_convs(2))

lemma R1_seqr:
  "R1(R1(P) ;; R1(Q)) = (R1(P) ;; R1(Q))"
  by pred_auto

lemma R1_seqr_closure [closure]:
  assumes "(P ::('t::trace, '\<alpha>, '\<beta>) rel_rp) is R1"
          "(Q ::('t::trace, '\<beta>, '\<gamma>) rel_rp) is R1"
  shows "(P ;; Q) is R1"
proof -
  have 1: "(tr\<^sup>< \<le> tr\<^sup>>)\<^sub>e \<sqsubseteq> P"
    using assms by (simp add: R1_by_refinement)
  have 2: "(tr\<^sup>< \<le> tr\<^sup>>)\<^sub>e \<sqsubseteq> Q"
    using assms by (simp add: R1_by_refinement)
  have "(((tr\<^sup>< \<le> tr\<^sup>>)\<^sub>e :: ('t::trace, '\<alpha>, '\<beta>) rel_rp);;(tr\<^sup>< \<le> tr\<^sup>>)\<^sub>e) \<sqsubseteq> (P;;Q)" (is "?l \<sqsubseteq> ?r")
    using 1 2 by (simp add: seqr_mono)
  moreover have "?l = (tr\<^sup>< \<le> tr\<^sup>>)\<^sub>e"
    using tr_le_trans by blast
  ultimately show ?thesis
    by (simp add: R1_by_refinement)
qed

lemma R1_power [closure]: "P is R1 \<Longrightarrow> P\<^bold>^n is R1"
  by (induct n, simp_all add: upred_semiring.power_Suc closure)

lemma R1_true_comp [simp]: "(R1(true) ;; R1(true)) = R1(true)"
  by (pred_auto; metis order_refl rea_vars.select_convs(2))


lemma R1_ok'_true: "(R1(P))\<^sup>t = R1(P\<^sup>t)"
  by pred_auto

(*
lemma R1_ok'_false: "(R1(P))\<^sup>f = R1(P\<^sup>f)"
  by pred_auto
*)

lemma R1_ok_true: "(R1(P))\<lbrakk>true/ok\<^sup><\<rbrakk> = R1(P\<lbrakk>true/ok\<^sup><\<rbrakk>)"
  by pred_auto

lemma R1_ok_false: "(R1(P))\<lbrakk>False/ok\<^sup><\<rbrakk> = R1(P\<lbrakk>False/ok\<^sup><\<rbrakk>)"
  by pred_auto

lemma seqr_R1_true_right: "((P ;; R1(true)) \<or> P) = (P ;; (tr\<^sup>< \<le> tr\<^sup>>)\<^sub>e)"
  by (pred_auto)

lemma conj_R1_true_right: "(P;;R1(true) \<and> Q;;R1(true)) ;; R1(true) = (P;;R1(true) \<and> Q;;R1(true))"
  apply (pred_auto)
  using dual_order.trans apply blast
  using dual_order.trans apply blast
  by (metis order_refl rea_vars.select_convs(2))

(* Why is this a lemma given the assumptions are not needed? *)
lemma R1_extend_conj_unrest: "\<lbrakk> $tr\<^sup>< \<sharp> Q; $tr\<^sup>> \<sharp> Q \<rbrakk> \<Longrightarrow> R1 (P \<and> Q) = (R1 P \<and> Q)"
  by (rule R1_extend_conj)

lemma R1_extend_conj_unrest': "\<lbrakk> $tr\<^sup>< \<sharp> Q; $tr\<^sup>> \<sharp> Q \<rbrakk> \<Longrightarrow> R1 (P \<and> Q) = (P \<and> R1 Q)"
  by (rule R1_extend_conj')

lemma R1_tr'_eq_tr: "R1(tr\<^sup>> = tr\<^sup><)\<^sub>e = (tr\<^sup>> = tr\<^sup><)\<^sub>e"
  by (pred_auto)

lemma R1_tr_less_tr': "R1(tr\<^sup>< < tr\<^sup>>)\<^sub>e = (tr\<^sup>< < tr\<^sup>>)\<^sub>e"
  by (pred_auto)

lemma tr_strict_prefix_R1_closed [closure]: "(tr\<^sup>< < tr\<^sup>>)\<^sub>e is R1"
  by (simp add: Healthy_def; pred_auto)

(* Need design healthiness conditions
lemma R1_H2_commute: "R1(H2(P)) = H2(R1(P))"
  by (simp add: H2_split R1_def usubst, rel_auto)
*)

subsection \<open> R2: No dependence upon trace history \<close>

text \<open> There are various ways of expressing $R2$, which are enumerated below. \<close>

definition R2a :: "('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp" where
[pred]: "R2a (P) = (\<Sqinter> s. P\<lbrakk>\<guillemotleft>s\<guillemotright>,(\<guillemotleft>s\<guillemotright>+(tr\<^sup>>-tr\<^sup><))/tr\<^sup><,tr\<^sup>>\<rbrakk>)\<^sub>e"

(* ... *)


end
