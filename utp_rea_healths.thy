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

lemma R1_USUP:
  "R1 (\<Sqinter>i \<in> A. P i) = (\<Sqinter> i \<in> A. R1 (P i))"
  by (simp add: fun_eq_iff R1_def)

(* Worse version without lattice expressions *)
lemma R1_USUP':
  "R1(SEXP(\<lambda> s. \<Sqinter> i. (i \<in> A \<and> P(i)(s)))) = SEXP(\<lambda> s. \<Sqinter> i. (i \<in> A \<and> (R1(P(i)))(s)))"
  by (simp add: fun_eq_iff R1_def; pred_auto)

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
  "\<lbrakk> vwb_lens x; unrest_usubst \<lbrakk>x\<rbrakk>\<^sub>\<sim> \<sigma> \<rbrakk> \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>s x = var x"
proof -
  assume 1: "vwb_lens x" and "unrest_usubst \<lbrakk>x\<rbrakk>\<^sub>\<sim> \<sigma>"
  hence "\<forall>s s'. \<sigma> (s \<oplus>\<^sub>L s' on x) = \<sigma> s \<oplus>\<^sub>L s' on x"
    by (metis lens_scene_override unrest_usubst_def vwb_lens_mwb)
  thus "\<langle>\<sigma>\<rangle>\<^sub>s x = get\<^bsub>x\<^esub>"
    by (metis 1 fun_eq_iff lens_override_def lens_override_idem mwb_lens_weak subst_lookup_def vwb_lens_mwb weak_lens.put_get)
qed

lemma subst_R1: "\<lbrakk> (unrest_usubst \<lbrakk>tr ;\<^sub>L fst\<^sub>L\<rbrakk>\<^sub>\<sim> \<sigma>); (unrest_usubst \<lbrakk> tr ;\<^sub>L snd\<^sub>L\<rbrakk>\<^sub>\<sim> \<sigma>) \<rbrakk> \<Longrightarrow> \<sigma> \<dagger> (R1 P) = R1(\<sigma> \<dagger> P)"
proof -
  assume "unrest_usubst \<lbrakk>tr ;\<^sub>L fst\<^sub>L\<rbrakk>\<^sub>\<sim> \<sigma>"
  hence 1: "\<langle>\<sigma>\<rangle>\<^sub>s (tr ;\<^sub>L fst\<^sub>L) = var (tr ;\<^sub>L fst\<^sub>L)"
    using comp_vwb_lens fst_vwb_lens tr_vwb_lens usubst_apply_unrest by blast
  assume "unrest_usubst \<lbrakk>tr ;\<^sub>L snd\<^sub>L\<rbrakk>\<^sub>\<sim> \<sigma>"
  hence 2: "\<langle>\<sigma>\<rangle>\<^sub>s (tr ;\<^sub>L snd\<^sub>L) = var (tr ;\<^sub>L snd\<^sub>L)"
    using comp_vwb_lens snd_vwb_lens tr_vwb_lens usubst_apply_unrest by blast
  show ?thesis
    using 1 2 by (pred_auto)
qed

(* .... *)

subsection \<open> R2: No dependence upon trace history \<close>

text \<open> There are various ways of expressing $R2$, which are enumerated below. \<close>

definition R2a :: "('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp" where
[pred]: "R2a (P) = (\<Sqinter> s. P\<lbrakk>\<guillemotleft>s\<guillemotright>,(\<guillemotleft>s\<guillemotright>+(tr\<^sup>>-tr\<^sup><))/tr\<^sup><,tr\<^sup>>\<rbrakk>)\<^sub>e"

(* ... *)


end
