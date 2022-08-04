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
  by (pred_auto, blast)

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
  by (pred_auto; blast)


lemma UINF_R1_closed [closure]:
  "\<lbrakk> \<And> i. P i is R1 \<rbrakk> \<Longrightarrow> (\<Sqinter> i \<in> A. P i) is R1"
  by (simp add: Healthy_def; pred_auto; blast)


lemma tr_ext_conj_R1 [closure]: 
  "(tr\<^sup>> = tr\<^sup>< @ e)\<^sub>e \<and> P is R1"
  by (pred_auto add: Prefix_Order.prefixI)

lemma tr_id_conj_R1 [closure]: 
  "(tr\<^sup>> = tr\<^sup><)\<^sub>e \<and> P is R1"
  by pred_auto

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
  by pred_auto

lemma R1_wait'_false_closed [closure]: "P is R1 \<Longrightarrow> P\<lbrakk>False/wait\<^sup>>\<rbrakk> is R1"
  by pred_auto

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
  by (pred_auto, blast+)

lemma R1_trace_extension [closure]:
  "(tr\<^sup>> \<ge> tr\<^sup>< @ e)\<^sub>e is R1"
  by (simp add: Healthy_def; pred_auto)

lemma tr_le_trans:
  "((tr\<^sup>< \<le> tr\<^sup>>)\<^sub>e ;; (tr\<^sup>< \<le> tr\<^sup>>)\<^sub>e) = (tr\<^sup>< \<le> tr\<^sup>>)\<^sub>e"
  by (pred_auto; metis order_refl)

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

(*
lemma R1_ok'_true: "(R1(P))\<^sup>t = R1(P\<^sup>t)"
  by pred_auto

lemma R1_ok'_false: "(R1(P))\<^sup>f = R1(P\<^sup>f)"
  by pred_auto
*)

lemma R1_ok_true: "(R1(P))\<lbrakk>True/ok\<^sup><\<rbrakk> = R1(P\<lbrakk>True/ok\<^sup><\<rbrakk>)"
  by pred_auto

lemma R1_ok_false: "(R1(P))\<lbrakk>False/ok\<^sup><\<rbrakk> = R1(P\<lbrakk>False/ok\<^sup><\<rbrakk>)"
  by pred_auto

lemma seqr_R1_true_right: "((P ;; R1(true)) \<or> P) = (P ;; (tr\<^sup>< \<le> tr\<^sup>>)\<^sub>e)"
  by (pred_auto)

lemma conj_R1_true_right: "(P;;R1(true) \<and> Q;;R1(true)) ;; R1(true) = (P;;R1(true) \<and> Q;;R1(true))"
  apply (pred_auto)
  using dual_order.trans apply blast
  using dual_order.trans apply blast
  by (metis order_refl)

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

definition R2a' :: "('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp" where
[pred]: "R2a' P = (R2a(P) \<triangleleft> R1(true) \<triangleright> P)"

definition R2s :: "('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp" where
[pred]: "R2s (P) = (P\<lbrakk>0, (tr\<^sup>>-tr\<^sup><) / tr\<^sup><, tr\<^sup>>\<rbrakk>)\<^sub>e"

lemma "R2s((tr\<^sup>> = [1,2]) \<and> (tr\<^sup>< = [1]))\<^sub>e = ((tr\<^sup>> = [2]) \<and> (tr\<^sup>< = []))\<^sub>e"
  apply pred_auto
  apply (simp add: zero_list_def)
  apply (simp add: zero_list_def)
  oops

definition R2 :: "('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" where
[pred]: "R2(P) = R1(R2s(P))"

definition R2c :: "('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" where
[pred]: "R2c(P) = (R2s(P) \<triangleleft> R1(true) \<triangleright> P)"

expr_ctr R2a R2a' R2s R2 R2c

text \<open> @{term R2a} and @{term R2s} are the standard definitions from the UTP book~\cite{Hoare&98}.
  An issue with these forms is that their definition depends upon @{term R1} also being 
  satisfied~\cite{Foster17b}, since otherwise the trace minus operator is not well defined. 
  We overcome this with our own version, @{term R2c}, which applies @{term R2s} if @{term R1} holds,
  and otherwise has no effect. This latter healthiness condition can therefore be reasoned about
  independently of @{term R1}, which is useful in some circumstances. \<close>

lemma unrest_ok_R2s [unrest]: "$ok\<^sup>< \<sharp> P \<Longrightarrow> $ok\<^sup>< \<sharp> R2s(P)"
  apply (simp add: R2s_def unrest)
  apply(unrest)
  oops

lemma unrest_ok'_R2s [unrest]: "$ok\<^sup>> \<sharp> P \<Longrightarrow> $ok\<^sup>> \<sharp> R2s(P)"
  oops

lemma unrest_ok_R2c [unrest]: "$ok\<^sup>< \<sharp> P \<Longrightarrow> $ok\<^sup>< \<sharp> R2c(P)"
  oops


(* TODO: this should have a better proof *)
lemma R2s_unrest [unrest]: "\<lbrakk> vwb_lens x; x \<bowtie> (tr ;\<^sub>L fst\<^sub>L); x \<bowtie> (tr ;\<^sub>L snd\<^sub>L); $x \<sharp> P \<rbrakk> \<Longrightarrow> $x \<sharp> R2s(P)"
  apply (simp add: R2s_def unrest usubst lens_indep_sym)
  by (smt (z3) SEXP_def aext_var lens_indep.lens_put_comm lens_indep.lens_put_irr2 ns_alpha_def subst_SEXP subst_id_def subst_upd_def subst_var unrest_lens vwb_lens_mwb)

term "$ok\<^sup>>"
term "ok ;\<^sub>L fst\<^sub>L"

(*
lemma unrest_ok'_R2c [unrest]: "$ok\<^sup>> \<sharp> P \<Longrightarrow> $ok\<^sup>> \<sharp> R2c(P)"
proof -
  assume 1: "$ok\<^sup>> \<sharp> P"
  have "R2c(P) = ((R2s(P) \<and> R1(true)) \<or> (P \<and> \<not> R1(true)))"
    by (pred_auto)
  have 2: "vwb_lens (ok ;\<^sub>L fst\<^sub>L)"
    by (simp add: comp_vwb_lens) 
  have 3: "\<And> a b. ([tr\<^sup>< \<leadsto> 0, tr\<^sup>> \<leadsto> $tr\<^sup>> - $tr\<^sup><] sset[$ok\<^sup>>, (a, b)] = [tr\<^sup>< \<leadsto> 0, tr\<^sup>> \<leadsto> $tr\<^sup>> - $tr\<^sup><])"

  have "$ok\<^sup>> \<sharp> (R2s(P) \<and> R1(true))"
    apply(simp add: R2s_def R1_def)
    using 1 apply(subst_eval)
    apply(pred_auto)
    sledgehammer
*)

(* TODO: why can't the following set of lemmas be proved using simp e.g.
     by (simp add: R2_def R1_def R2s_def usubst unrest)
    as in old UTP *)

lemma R2s_subst_wait_true [usubst]:
  "(R2s(P))\<lbrakk>True/wait\<^sup><\<rbrakk> = R2s(P\<lbrakk>True/wait\<^sup><\<rbrakk>)"
  by (pred_auto; metis rea_vars.surjective rea_vars.update_convs(1) rea_vars.update_convs(2))

lemma R2s_subst_wait'_true [usubst]:
  "(R2s(P))\<lbrakk>True/wait\<^sup>>\<rbrakk> = R2s(P\<lbrakk>True/wait\<^sup>>\<rbrakk>)"
  by (pred_auto; metis rea_vars.surjective rea_vars.update_convs(1) rea_vars.update_convs(2))

lemma R2_subst_wait_true [usubst]:
  "(R2(P))\<lbrakk>True/wait\<^sup><\<rbrakk> = R2(P\<lbrakk>True/wait\<^sup><\<rbrakk>)"
  by (pred_auto; metis rea_vars.surjective rea_vars.update_convs(1) rea_vars.update_convs(2))

lemma R2_subst_wait'_true [usubst]:
  "(R2(P))\<lbrakk>True/wait\<^sup>>\<rbrakk> = R2(P\<lbrakk>True/wait\<^sup>>\<rbrakk>)"
  by (pred_auto; metis rea_vars.surjective rea_vars.update_convs(1) rea_vars.update_convs(2))

lemma R2_subst_wait_false [usubst]:
  "(R2(P))\<lbrakk>False/wait\<^sup><\<rbrakk> = R2(P\<lbrakk>False/wait\<^sup><\<rbrakk>)"
  by (pred_auto; metis rea_vars.surjective rea_vars.update_convs(1) rea_vars.update_convs(2))

lemma R2_subst_wait'_false [usubst]:
  "(R2(P))\<lbrakk>False/wait\<^sup>>\<rbrakk> = R2(P\<lbrakk>False/wait\<^sup>>\<rbrakk>)"
  by (pred_auto; metis rea_vars.surjective rea_vars.update_convs(1) rea_vars.update_convs(2))

lemma R2c_R2s_absorb: "R2c(R2s(P)) = R2s(P)"
  by (pred_auto)

lemma R2a_R2s: "R2a(R2s(P)) = R2s(P)"
  by (pred_auto)

lemma R2s_R2a: "R2s(R2a(P)) = R2a(P)"
  by (pred_auto)

lemma R2a_equiv_R2s: "P is R2a \<longleftrightarrow> P is R2s"
  by (metis Healthy_def' R2a_R2s R2s_R2a)

lemma R2a_idem: "R2a(R2a(P)) = R2a(P)"
  by (pred_auto)

lemma R2a'_idem: "R2a'(R2a'(P)) = R2a'(P)"
  by (pred_auto)

lemma R2a_mono: "P \<sqsubseteq> Q \<Longrightarrow> R2a(P) \<sqsubseteq> R2a(Q)"
  by (pred_auto, blast)

lemma R2a'_mono: "P \<sqsubseteq> Q \<Longrightarrow> R2a'(P) \<sqsubseteq> R2a'(Q)"
  by (pred_auto; blast)

lemma R2a'_weakening: "R2a'(P) \<sqsubseteq> P"
  by(pred_auto, metis diff_add_cancel_left')

lemma R2s_idem: "R2s(R2s(P)) = R2s(P)"
  by (pred_auto)

lemma R2_idem: "R2(R2(P)) = R2(P)"
  by (pred_auto)

lemma R2_mono: "P \<sqsubseteq> Q \<Longrightarrow> R2(P) \<sqsubseteq> R2(Q)"
  by (pred_auto)

lemma R2_implies_R1 [closure]: "P is R2 \<Longrightarrow> P is R1"
  by (pred_auto, blast)

lemma R2_implies_R2c [closure]: "P is R2 \<Longrightarrow> P is R2c"
  by (pred_auto; blast)

lemma R2c_Continuous: "Continuous R2c"
  by pred_auto

lemma R2c_lit: "R2c(\<guillemotleft>x\<guillemotright>)\<^sub>e = (\<guillemotleft>x\<guillemotright>)\<^sub>e"
  by pred_auto

lemma tr_strict_prefix_R2c_closed [closure]: "(tr\<^sup>< < tr\<^sup>>)\<^sub>e is R2c"
  by pred_auto

lemma R2s_conj: "R2s(P \<and> Q) = (R2s(P) \<and> R2s(Q))"
  by pred_auto

lemma R2_conj: "R2(P \<and> Q) = (R2(P) \<and> R2(Q))"
  by pred_auto

lemma R2s_disj: "R2s(P \<or> Q) = (R2s(P) \<or> R2s(Q))"
  by pred_auto

lemma R2s_USUP:
  "R2s(\<Sqinter> i \<in> A. P(i)) = (\<Sqinter> i \<in> A. R2s(P(i)))"
  by pred_auto

lemma R2c_USUP:
  "R2c(\<Sqinter> i \<in> A. P(i)) = (\<Sqinter> i \<in> A. R2c(P(i)))"
  by pred_auto

lemma R2s_UINF:
  "R2s(\<Squnion> i \<in> A. P(i)) = (\<Squnion> i \<in> A. R2s(P(i)))"
  by pred_auto

lemma R2c_UINF:
  "R2c(\<Squnion> i \<in> A. P(i)) = (\<Squnion> i \<in> A. R2c(P(i)))"
  by pred_auto

lemma R2_disj: "R2(P \<or> Q) = (R2(P) \<or> R2(Q))"
  by pred_auto

lemma R2s_not: "R2s(\<not> P) = (\<not> R2s(P))"
  by pred_auto

lemma R2s_condr: "R2s(P \<triangleleft> b \<triangleright> Q) = (R2s(P) \<triangleleft> R2s(b) \<triangleright> R2s(Q))"
  by pred_auto

lemma R2_condr: "R2(P \<triangleleft> b \<triangleright> Q) = (R2(P) \<triangleleft> R2(b) \<triangleright> R2(Q))"
  by pred_auto

lemma R2_condr': "R2(P \<triangleleft> b \<triangleright> Q) = (R2(P) \<triangleleft> R2s(b) \<triangleright> R2(Q))"
  by pred_auto

lemma R2s_ok: "R2s(ok\<^sup><) = ok\<^sup><"
  by pred_auto

lemma R2s_ok': "R2s(ok\<^sup>>) = ok\<^sup>>"
  by pred_auto

lemma R2s_wait: "R2s(wait\<^sup><) = wait\<^sup><"
  by pred_auto

lemma R2s_wait': "R2s(wait\<^sup>>) = wait\<^sup>>"
  by pred_auto

lemma R2s_true: "R2s(true) = true"
  by pred_auto

lemma R2s_false: "R2s(false) = false"
  by pred_auto

lemma true_is_R2s:
  "true is R2s"
  by (simp add: Healthy_def R2s_true)

(*
lemma R2s_lift_rea: "R2s(\<lceil>P\<rceil>\<^sub>R) = \<lceil>P\<rceil>\<^sub>R"
  by (simp add: R2s_def usubst unrest)

lemma R2c_lift_rea: "R2c(\<lceil>P\<rceil>\<^sub>R) = \<lceil>P\<rceil>\<^sub>R"
  by (simp add: R2c_def R2s_lift_rea cond_idem usubst unrest)
*)

lemma R2c_true: "R2c(true) = true"
  by pred_auto

lemma R2c_false: "R2c(false) = false"
  by pred_auto

lemma R2c_and: "R2c(P \<and> Q) = (R2c(P) \<and> R2c(Q))"
  by pred_auto

lemma conj_R2c_closed [closure]: "\<lbrakk> P is R2c; Q is R2c \<rbrakk> \<Longrightarrow> (P \<and> Q) is R2c"
  by (simp add: Healthy_def R2c_and)

lemma R2c_disj: "R2c(P \<or> Q) = (R2c(P) \<or> R2c(Q))"
  by pred_auto

lemma R2c_inf: "R2c(P \<sqinter> Q) = (R2c(P) \<sqinter> R2c(Q))"
  by pred_auto

lemma R2c_not: "R2c(\<not> P) = (\<not> R2c(P))"
  by pred_auto

lemma R2c_ok: "R2c(ok\<^sup><) = (ok\<^sup><)"
  by pred_auto

lemma R2c_ok': "R2c(ok\<^sup>>) = (ok\<^sup>>)"
  by pred_auto

lemma R2c_wait: "R2c(wait\<^sup><) = wait\<^sup><"
  by pred_auto

lemma R2c_wait': "R2c(wait\<^sup>>) = wait\<^sup>>"
  by pred_auto

lemma R2c_wait'_true [usubst]: "(R2c P)\<lbrakk>True/wait\<^sup>>\<rbrakk> = R2c(P\<lbrakk>True/wait\<^sup>>\<rbrakk>)"
  by pred_auto
  
lemma R2c_wait'_false [usubst]: "(R2c P)\<lbrakk>False/wait\<^sup>>\<rbrakk> = R2c(P\<lbrakk>False/wait\<^sup>>\<rbrakk>)"
  by pred_auto  

lemma R2c_tr'_minus_tr: "R2c(tr\<^sup>> = tr\<^sup><)\<^sub>e = (tr\<^sup>> = tr\<^sup><)\<^sub>e"
  apply (pred_auto) using minus_zero_eq by blast

lemma R2c_tr_le_tr': "R2c(tr\<^sup>< \<le> tr\<^sup>>)\<^sub>e = (tr\<^sup>< \<le> tr\<^sup>>)\<^sub>e"
  by pred_auto

lemma R2c_tr'_ge_tr: "R2c(tr\<^sup>> \<ge> tr\<^sup><)\<^sub>e = (tr\<^sup>> \<ge> tr\<^sup><)\<^sub>e"
  by pred_auto

lemma R2c_tr_less_tr': "R2c(tr\<^sup>< < tr\<^sup>>)\<^sub>e = (tr\<^sup>< < tr\<^sup>>)\<^sub>e"
  by pred_auto

lemma R2c_condr: "R2c(P \<triangleleft> b \<triangleright> Q) = (R2c(P) \<triangleleft> R2c(b) \<triangleright> R2c(Q))"
  by pred_auto

lemma shAll_meet: "(\<Squnion> x. (\<guillemotleft>f\<guillemotright> \<guillemotleft>x\<guillemotright>)\<^sub>e) = (\<forall> x. \<guillemotleft>f\<guillemotright> x)\<^sub>e"
  by pred_auto

lemma shAll_meet2: "(\<Squnion> x. f (P \<guillemotleft>x\<guillemotright>)\<^sub>e) = (\<forall> x. (\<guillemotleft>f\<guillemotright> P) x)\<^sub>e"
  apply pred_auto
  oops
  (* sledgehammer *)

ML \<open>
  @{term "(R2c(P x))\<^sub>e"}
\<close>

lemma shAll_meet3: "(\<Squnion> x. (\<guillemotleft>f\<guillemotright> (P \<guillemotleft>x\<guillemotright>))\<^sub>e) = (\<forall> x. \<guillemotleft>f\<guillemotright> (P x))\<^sub>e"
  by pred_auto

(* Cannot quite make the equivalence work
lemma R2c_shAll: "R2c (\<forall> x. P x)\<^sub>e = (\<forall> x. R2c(P x))\<^sub>e"
  apply(pred_auto)
proof - 
  have "R2c (\<forall> x. P x)\<^sub>e = R2c (\<Squnion> x. (P \<guillemotleft>x\<guillemotright>)\<^sub>e)"
    by pred_auto
  also have "\<dots> = (\<Squnion> x. R2c(P \<guillemotleft>x\<guillemotright>)\<^sub>e)"
    using R2c_UINF by blast
  also have "\<dots> = (\<forall> x. R2c(P x))\<^sub>e"
    apply pred_simp
    oops
qed
*)

lemma R2c_impl: "R2c(P \<longrightarrow> Q) = (R2c(P) \<longrightarrow> R2c(Q))"
  oops

(* Need an implementation of alphabet restriction e.g.

text \<open> We implement a poor man's version of alphabet restriction that hides a variable within 
  a relation. \<close>

definition rel_var_res :: "'\<alpha> hrel \<Rightarrow> ('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel" (infix "\<restriction>\<^sub>\<alpha>" 80) where
[rel]: "P \<restriction>\<^sub>\<alpha> x = (\<exists> y. \<exists> z. P\<lbrakk> y,z/x\<^sup><,x\<^sup>> \<rbrakk>)\<^sub>e"

expr_ctr rel_var_res

lemma skip_r_unfold:
  "vwb_lens x \<Longrightarrow> II = ((tr\<^sup>> = tr\<^sup><)\<^sub>e \<and> II\<restriction>\<^sub>\<alpha>x)"
  sorry
(*  by (simp add: rel_var_res_def; pred_auto) *)

lemma R2c_skip_tr: "R2c(II\<restriction>\<^sub>\<alpha>tr) = II\<restriction>\<^sub>\<alpha>tr"
  by (simp add: rel_var_res_def; pred_auto)

*)

lemma R2c_skip_r: "R2c(II) = II"
  by (pred_auto, metis add.right_neutral diff_add_cancel_left')

lemma R1_R2c_commute: "R1(R2c(P)) = R2c(R1(P))"
  by pred_auto

lemma R1_R2c_is_R2: "R1(R2c(P)) = R2(P)"
  by pred_auto

lemma R1_R2s_R2c: "R1(R2s(P)) = R1(R2c(P))"
  by pred_auto

lemma R1_R2s_tr_wait:
  "R1 (R2s (((tr\<^sup>> = tr\<^sup><) \<and> wait\<^sup>>)\<^sub>e)) = ((tr\<^sup>> = tr\<^sup><) \<and> wait\<^sup>>)\<^sub>e"
  apply pred_auto using minus_zero_eq by blast

lemma R1_R2s_tr'_eq_tr:
  "R1 (R2s (tr\<^sup>> = tr\<^sup><)\<^sub>e) = (tr\<^sup>> = tr\<^sup><)\<^sub>e"
  apply pred_auto using minus_zero_eq by blast

(* Need to figure out how to prove (3) or a better proof
lemma R1_R2s_tr'_extend_tr:
  "\<lbrakk> $tr\<^sup>< \<sharp> v; $tr\<^sup>> \<sharp> v \<rbrakk> \<Longrightarrow> R1 (R2s (tr\<^sup>> = tr\<^sup>< @ v)\<^sub>e) = (tr\<^sup>> = tr\<^sup>< @ v)\<^sub>e"
proof (simp add: R1_def R2s_def)
  assume 1: "$tr\<^sup>< \<sharp> v" and 2: "$tr\<^sup>> \<sharp> v"
  have 3:  "\<And>a b s s'. v (s \<lparr>tr\<^sub>v := a\<rparr>, s' \<lparr>tr\<^sub>v := b\<rparr>) = v (s, s')"
    sorry
  show "([tr\<^sup>< \<leadsto> 0, tr\<^sup>> \<leadsto> ($tr)\<^sup>> - ($tr)\<^sup><] \<dagger> (($tr)\<^sup>> = ($tr)\<^sup>< @ v) \<and> ($tr)\<^sup>< \<le> $tr\<^sup>>)\<^sub>e = (($tr)\<^sup>> = ($tr)\<^sup>< @ v)\<^sub>e"
    apply (subst_eval)
    apply(pred_auto)
    apply(simp_all add: 3 zero_list_def)
    using zero_list_def by force
qed
*)

lemma R2_tr_prefix: "R2(tr\<^sup>< \<le> tr\<^sup>>)\<^sub>e = (tr\<^sup>< \<le> tr\<^sup>>)\<^sub>e"
  by pred_auto

lemma R2_form:
  "R2(P) = (\<exists> tt\<^sub>0. P\<lbrakk>0,\<guillemotleft>tt\<^sub>0\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk> \<and> (tr\<^sup>> = tr\<^sup>< + \<guillemotleft>tt\<^sub>0\<guillemotright>))\<^sub>e"
  by(pred_auto; metis diff_add_cancel_left')

lemma R2_subst_tr: 
  assumes "P is R2" 
  shows "[tr\<^sup>< \<leadsto> tr\<^sub>0, tr\<^sup>> \<leadsto> tr\<^sub>0 + t] \<dagger> P = [tr\<^sup>< \<leadsto> 0, tr\<^sup>> \<leadsto> t] \<dagger> P"
proof -
  have "[tr\<^sup>< \<leadsto> tr\<^sub>0, tr\<^sup>> \<leadsto> tr\<^sub>0 + t] \<dagger> R2 P = [tr\<^sup>< \<leadsto> 0, tr\<^sup>> \<leadsto> t] \<dagger> R2 P"
    by (simp add: R2_def R1_def R2s_def; pred_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma R2_seqr_form:
  shows "(R2(P) ;; R2(Q)) =
         (\<Sqinter> tt\<^sub>1 tt\<^sub>2. ((P\<lbrakk>0,\<guillemotleft>tt\<^sub>1\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk> ;; Q\<lbrakk>0,\<guillemotleft>tt\<^sub>2\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk>)
                    \<and> (tr\<^sup>> = tr\<^sup>< + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)\<^sub>e))"
proof -
  have "(R2(P) ;; R2(Q)) = (\<Sqinter> tr\<^sub>0. (R2(P))\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/tr\<^sup>>\<rbrakk> ;; (R2(Q))\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/tr\<^sup><\<rbrakk>)"
    by (subst seqr_middle[of tr], simp_all)
  also have "\<dots> =
       (\<Sqinter> tr\<^sub>0 tt\<^sub>1 tt\<^sub>2. ((P\<lbrakk>0, \<guillemotleft>tt\<^sub>1\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk> \<and> (\<guillemotleft>tr\<^sub>0\<guillemotright> = tr\<^sup>< + \<guillemotleft>tt\<^sub>1\<guillemotright>)\<^sub>e) ;;
                        (Q\<lbrakk>0, \<guillemotleft>tt\<^sub>2\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk> \<and> (tr\<^sup>> = \<guillemotleft>tr\<^sub>0\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)\<^sub>e)))"
    by (simp add: R2_form, pred_auto; blast)
  also have "\<dots> =
       (\<Sqinter> tr\<^sub>0 tt\<^sub>1 tt\<^sub>2. (((\<guillemotleft>tr\<^sub>0\<guillemotright> = tr\<^sup>< + \<guillemotleft>tt\<^sub>1\<guillemotright>)\<^sub>e \<and> P\<lbrakk>0,\<guillemotleft>tt\<^sub>1\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk>) ;;
                        (Q\<lbrakk>0,\<guillemotleft>tt\<^sub>2\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk> \<and> (tr\<^sup>> = \<guillemotleft>tr\<^sub>0\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)\<^sub>e)))"
    by pred_auto
  also have "\<dots> =
       (\<Sqinter> tr\<^sub>0 tt\<^sub>1 tt\<^sub>2. (P\<lbrakk>0,\<guillemotleft>tt\<^sub>1\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk> ;; Q\<lbrakk>0,\<guillemotleft>tt\<^sub>2\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk>)
                     \<and> (\<guillemotleft>tr\<^sub>0\<guillemotright> = tr\<^sup>< + \<guillemotleft>tt\<^sub>1\<guillemotright>)\<^sub>e \<and> (tr\<^sup>> = \<guillemotleft>tr\<^sub>0\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)\<^sub>e)"
    by (pred_auto; blast)
  also have "\<dots> =
       (\<Sqinter> tt\<^sub>1 tt\<^sub>2. (P\<lbrakk>0,\<guillemotleft>tt\<^sub>1\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk> ;; Q\<lbrakk>0,\<guillemotleft>tt\<^sub>2\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk>)
                 \<and> (\<Sqinter> tr\<^sub>0. (\<guillemotleft>tr\<^sub>0\<guillemotright> = tr\<^sup>< + \<guillemotleft>tt\<^sub>1\<guillemotright>)\<^sub>e \<and> (tr\<^sup>> = \<guillemotleft>tr\<^sub>0\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)\<^sub>e))"
    by pred_auto
  also have "\<dots> =
             (\<Sqinter> tt\<^sub>1 tt\<^sub>2. (P\<lbrakk>0,\<guillemotleft>tt\<^sub>1\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk> ;; Q\<lbrakk>0,\<guillemotleft>tt\<^sub>2\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk>)
                 \<and> (tr\<^sup>> = tr\<^sup>< + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)\<^sub>e)"
    by pred_auto
  finally show ?thesis .
qed

lemma R2_seqr_form':
  assumes "P is R2" "Q is R2"
  shows "P ;; Q =
         (\<Sqinter> tt\<^sub>1 tt\<^sub>2. (P\<lbrakk>0,\<guillemotleft>tt\<^sub>1\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk> ;; Q\<lbrakk>0,\<guillemotleft>tt\<^sub>2\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk>)
                   \<and> (tr\<^sup>> = tr\<^sup>< + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)\<^sub>e)"
  using R2_seqr_form[of P Q] by (simp add: Healthy_if assms)

(* Not sure if this version of the lemma is still useful
lemma R2_seqr_form'':
  assumes "P is R2" "Q is R2"
  shows "P ;; Q =
         (\<^bold>\<exists> (tt\<^sub>1, tt\<^sub>2) \<bullet> ((P\<lbrakk>0,\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr,$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>0,\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr,$tr\<acute>\<rbrakk>))
                         \<and> ($tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>))"
  by (subst R2_seqr_form', simp_all add: assms, rel_auto)
*)

lemma R2_tr_middle:
  assumes "P is R2" "Q is R2"
  shows "(\<Sqinter> tr\<^sub>0. (P\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/tr\<^sup>>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/tr\<^sup><\<rbrakk>) \<and> (\<guillemotleft>tr\<^sub>0\<guillemotright> \<le> tr\<^sup>>)\<^sub>e) = (P ;; Q)"
proof -
  have "(P ;; Q) = (\<Sqinter> tr\<^sub>0. (P\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/tr\<^sup>>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/tr\<^sup><\<rbrakk>))"
    by (simp add: seqr_middle)
  also have "... = (\<Sqinter> tr\<^sub>0. ((R2 P)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/tr\<^sup>>\<rbrakk> ;; (R2 Q)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/tr\<^sup><\<rbrakk>))"
    by (simp add: assms Healthy_if)
  also have "... = (\<Sqinter> tr\<^sub>0. ((R2 P)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/tr\<^sup>>\<rbrakk> ;; (R2 Q)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/tr\<^sup><\<rbrakk>) \<and> (\<guillemotleft>tr\<^sub>0\<guillemotright> \<le> tr\<^sup>>)\<^sub>e)"
    by pred_auto
  also have "... = (\<Sqinter> tr\<^sub>0. (P\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/tr\<^sup>>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/tr\<^sup><\<rbrakk>) \<and> (\<guillemotleft>tr\<^sub>0\<guillemotright> \<le> tr\<^sup>>)\<^sub>e)"
    by (simp add: assms Healthy_if)
  finally show ?thesis ..
qed

lemma tr_contribution_sum: "\<And> tt\<^sub>1 tt\<^sub>2. (((tr\<^sup>> - tr\<^sup>< = \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> tr\<^sup>> \<ge> tr\<^sup><)\<^sub>e :: ('t,'\<alpha>,'\<gamma>) rel_rp)
                                     = (tr\<^sup>> = tr\<^sup>< + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)\<^sub>e)"
  apply (pred_auto)
  apply (metis add.assoc diff_add_cancel_left')
  apply (simp add: add.assoc)
  apply (meson le_add order_trans)
  done

lemma R2_seqr_distribute:
  fixes P :: "('t::trace,'\<alpha>,'\<beta>) rel_rp" and Q :: "('t,'\<beta>,'\<gamma>) rel_rp"
  shows "R2(R2(P) ;; R2(Q)) = (R2(P) ;; R2(Q))"
proof -
  have "R2(R2(P) ;; R2(Q)) =
    ((\<Sqinter> tt\<^sub>1 tt\<^sub>2. (P\<lbrakk>0,\<guillemotleft>tt\<^sub>1\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk> ;; Q\<lbrakk>0,\<guillemotleft>tt\<^sub>2\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk>)\<lbrakk>(tr\<^sup>> - tr\<^sup><)/tr\<^sup>>\<rbrakk>
      \<and> (tr\<^sup>> - tr\<^sup>< = \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)\<^sub>e) \<and> (tr\<^sup>> \<ge> tr\<^sup><)\<^sub>e)"
    by (simp add: R2_seqr_form; pred_auto)
  also have "\<dots> =
    ((\<Sqinter> tt\<^sub>1 tt\<^sub>2. (P\<lbrakk>0,\<guillemotleft>tt\<^sub>1\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk> ;; Q\<lbrakk>0,\<guillemotleft>tt\<^sub>2\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk>)\<lbrakk>(\<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)/tr\<^sup>>\<rbrakk>
      \<and> (tr\<^sup>> - tr\<^sup>< = \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)\<^sub>e) \<and> (tr\<^sup>> \<ge> tr\<^sup><)\<^sub>e)"
      by pred_auto
  also have "\<dots> =
    ((\<Sqinter> tt\<^sub>1 tt\<^sub>2. (P\<lbrakk>0,\<guillemotleft>tt\<^sub>1\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk> ;; Q\<lbrakk>0,\<guillemotleft>tt\<^sub>2\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk>)
      \<and> (tr\<^sup>> - tr\<^sup>< = \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)\<^sub>e) \<and> (tr\<^sup>> \<ge> tr\<^sup><)\<^sub>e)"
      by pred_auto
  also have "\<dots> =
    (\<Sqinter> tt\<^sub>1 tt\<^sub>2. (P\<lbrakk>0,\<guillemotleft>tt\<^sub>1\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk> ;; Q\<lbrakk>0,\<guillemotleft>tt\<^sub>2\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk>)
      \<and> (tr\<^sup>> - tr\<^sup>< = \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> tr\<^sup>> \<ge> tr\<^sup><)\<^sub>e)"
    by (pred_auto; blast)
  also have "\<dots> =
    (\<Sqinter> tt\<^sub>1 tt\<^sub>2. (P\<lbrakk>0,\<guillemotleft>tt\<^sub>1\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk> ;; Q\<lbrakk>0,\<guillemotleft>tt\<^sub>2\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk>)
              \<and> (tr\<^sup>> = tr\<^sup>< + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)\<^sub>e)"
    by (simp add: tr_contribution_sum)
  also have "... = (R2(P) ;; R2(Q))"
    by (simp add: R2_seqr_form)
  finally show ?thesis .
qed

lemma R2_seqr_closure [closure]:
  assumes "P is R2" "Q is R2"
  shows "(P ;; Q) is R2"
  by (metis Healthy_def' R2_seqr_distribute assms(1) assms(2))

lemma false_R2 [closure]: "false is R2"
  by (simp add: Healthy_def; pred_auto)
    
lemma R1_R2_commute:
  "R1(R2(P)) = R2(R1(P))"
  by pred_auto

lemma R2_R1_form: "R2(R1(P)) = R1(R2s(P))"
  by pred_auto

(* Need rdes healthiness conditions
lemma R2s_H1_commute:
  "R2s(H1(P)) = H1(R2s(P))"
  by pred_auto

lemma R2s_H2_commute:
  "R2s(H2(P)) = H2(R2s(P))"
  by (simp add: H2_split R2s_def usubst)
*)

lemma R2_R1_seq_drop_left:
  "R2(R1(P) ;; R1(Q)) = R2(P ;; R1(Q))"
  by pred_auto

lemma R2c_idem: "R2c(R2c(P)) = R2c(P)"
  by pred_auto

lemma R2c_Idempotent [closure]: "Idempotent R2c"
  by (simp add: Idempotent_def R2c_idem)

lemma R2c_Monotonic [closure]: "Monotonic R2c"
  by (simp add: mono_def; pred_auto)

(* 
lemma R2c_H2_commute: "R2c(H2(P)) = H2(R2c(P))"
  by (simp add: H2_split R2c_disj R2c_def R2s_def usubst, rel_auto)
*)

lemma R2c_seq: "R2c(R2(P) ;; R2(Q)) = (R2(P) ;; R2(Q))"
  by (metis (no_types, lifting) R1_R2c_commute R1_R2c_is_R2 R2_seqr_distribute R2c_idem)

lemma R2_R2c_def: "R2(P) = R1(R2c(P))"
  by pred_auto

lemma R2_comp_def: "R2 = R1 \<circ> R2c"
  by (auto simp add: R2_R2c_def)

lemma R2c_R1_seq: "R2c(R1(R2c(P)) ;; R1(R2c(Q))) = (R1(R2c(P)) ;; R1(R2c(Q)))"
  using R2c_seq[of P Q] by (simp add: R2_R2c_def)

lemma R1_R2c_seqr_distribute:
  fixes P :: "('t::trace,'\<alpha>,'\<beta>) rel_rp" and Q :: "('t,'\<beta>,'\<gamma>) rel_rp"
  assumes "P is R1" "P is R2c" "Q is R1" "Q is R2c"
  shows "R1(R2c(P ;; Q)) = P ;; Q"
  by (metis Healthy_if R1_seqr R2c_R1_seq assms)

lemma R2_R1_true:
  "R2(R1(true)) = R1(true)"
  by (simp add: R2_R1_form R2s_true)
    
lemma R1_true_R2 [closure]: "R1(true) is R2"
  by (simp add: Healthy_def; pred_auto)

lemma R1_R2s_R1_true_lemma:
  "R1(R2s(R1 (\<not> R2s P) ;; R1 true)) = R1(R2s((\<not> P) ;; R1 true))"
  by pred_auto

lemma R2c_healthy_R2s: "P is R2c \<Longrightarrow> R1(R2s(P)) = R1(P)"
  by (simp add: Healthy_def R1_R2s_R2c) 

subsection \<open> R3: No activity while predecessor is waiting \<close>

definition R3 :: "('t::trace, '\<alpha>) hrel_rp \<Rightarrow> ('t, '\<alpha>) hrel_rp" where
[pred]: "R3(P) = (II \<triangleleft> wait\<^sup>< \<triangleright> P)\<^sub>e"

expr_ctr R3

lemma R3_idem: "R3(R3(P)) = R3(P)"
  by pred_auto

lemma R3_Idempotent [closure]: "Idempotent R3"
  by (simp add: Idempotent_def R3_idem)

lemma R3_mono: "P \<sqsubseteq> Q \<Longrightarrow> R3(P) \<sqsubseteq> R3(Q)"
  by pred_auto

lemma R3_Monotonic: "Monotonic R3"
  by (simp add: mono_def; pred_auto)

lemma R3_Continuous: "Continuous R3"
  by pred_auto

lemma R3_conj: "R3(P \<and> Q) = (R3(P) \<and> R3(Q))"
  by pred_auto

lemma R3_disj: "R3(P \<or> Q) = (R3(P) \<or> R3(Q))"
  by pred_auto

lemma R3_USUP:
  assumes "A \<noteq> {}"
  shows "R3(\<Sqinter> i \<in> A. P(i)) = (\<Sqinter> i \<in> A. R3(P(i)))"
  using assms by pred_auto

lemma R3_UINF:
  assumes "A \<noteq> {}"
  shows "R3(\<Squnion> i \<in> A. P(i)) = (\<Squnion> i \<in> A. R3(P(i)))"
  using assms by pred_auto

lemma R3_condr: "R3(P \<triangleleft> b \<triangleright> Q) = (R3(P) \<triangleleft> b \<triangleright> R3(Q))"
  by pred_auto

lemma R3_skipr: "R3(II) = II"
  by pred_auto

lemma R3_form: "R3(P) = ((wait\<^sup>< \<and> II) \<or> (\<not> wait\<^sup>< \<and> P))\<^sub>e"
  by (pred_auto; metis (full_types))

lemma wait_R3:
  "(wait\<^sup>< \<and> R3(P))\<^sub>e = (II \<and> wait\<^sup>>)\<^sub>e"
  by (pred_auto; metis (full_types))

lemma nwait_R3:
  "(\<not>wait\<^sup>< \<and> R3(P))\<^sub>e = (\<not>wait\<^sup>< \<and> P)\<^sub>e"
  by pred_auto

lemma R3_semir_form:
  "(R3(P) ;; R3(Q)) = R3(P ;; R3(Q))"
  by (pred_simp, safe; metis)

lemma R3_semir_closure:
  assumes "P is R3" "Q is R3"
  shows "(P ;; Q) is R3"
  using assms
  by (metis Healthy_def' R3_semir_form)

lemma R1_R3_commute: "R1(R3(P)) = R3(R1(P))"
  by pred_auto

lemma R2_R3_commute: "R2(R3(P)) = R3(R2(P))"
  by (pred_auto, metis add.right_neutral diff_add_cancel_left')+

subsection \<open> R4: The trace strictly increases \<close>

definition R4 :: "('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" where
[pred]: "R4(P) = (P \<and> (tr\<^sup>< < tr\<^sup>>)\<^sub>e)"

expr_ctr R4

lemma R4_implies_R1 [closure]: "P is R4 \<Longrightarrow> P is R1"
  apply(simp add: Healthy_def)
  apply pred_auto
  using order_less_imp_le by blast  

lemma R4_iff_refine:
  "P is R4 \<longleftrightarrow> (tr\<^sup>< < tr\<^sup>>)\<^sub>e \<sqsubseteq> P"
  by (pred_auto; blast)

lemma R4_idem: "R4 (R4 P) = R4 P"
  by pred_auto

lemma R4_false: "R4(false) = false"
  by pred_auto

lemma R4_conj: "R4(P \<and> Q) = (R4(P) \<and> R4(Q))"
  by pred_auto

lemma R4_disj: "R4(P \<or> Q) = (R4(P) \<or> R4(Q))"
  by pred_auto

lemma R4_is_R4 [closure]: "R4(P) is R4"
  by (simp add: Healthy_def; pred_auto)

lemma false_R4 [closure]: "false is R4"
  by (simp add: Healthy_def; pred_auto)

lemma UINF_R4_closed [closure]: 
  "\<lbrakk> \<And> i. P i is R4 \<rbrakk> \<Longrightarrow> (\<Sqinter> i. P i) is R4"
  by (simp add: Healthy_def; pred_auto; blast)

lemma conj_R4_closed [closure]:
  "\<lbrakk> P is R4; Q is R4 \<rbrakk> \<Longrightarrow> (P \<and> Q) is R4"
  by (simp add: Healthy_def R4_conj)

lemma disj_R4_closed [closure]:
  "\<lbrakk> P is R4; Q is R4 \<rbrakk> \<Longrightarrow> (P \<or> Q) is R4"
  by (simp add: Healthy_def R4_disj)

lemma seq_R4_closed_1 [closure]:
  "\<lbrakk> P is R4; Q is R1 \<rbrakk> \<Longrightarrow> (P ;; Q) is R4"
  apply (simp add: Healthy_def; pred_auto)
  using less_le_trans by blast

lemma seq_R4_closed_2 [closure]:
  "\<lbrakk> P is R1; Q is R4 \<rbrakk> \<Longrightarrow> (P ;; Q) is R4"
  by (simp add: Healthy_def; pred_auto, meson order_le_less_trans)

subsection \<open> R5: The trace does not increase \<close>

definition R5 :: "('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" where
[pred]: "R5(P) = (P \<and> (tr\<^sup>< = tr\<^sup>>)\<^sub>e)"

expr_ctr R5

lemma R5_implies_R1 [closure]: "P is R5 \<Longrightarrow> P is R1"
  by (pred_auto, metis order_refl)

lemma R5_iff_refine:
  "P is R5 \<longleftrightarrow> (tr\<^sup>< = tr\<^sup>>)\<^sub>e \<sqsubseteq> P"
  by (simp add: Healthy_def; pred_auto; blast)

lemma R5_conj: "R5(P \<and> Q) = (R5(P) \<and> R5(Q))"
  by pred_auto

lemma R5_disj: "R5(P \<or> Q) = (R5(P) \<or> R5(Q))"
  by pred_auto

lemma R4_R5: "R4 (R5 P) = false"
  by pred_auto

lemma R5_R4: "R5 (R4 P) = false"
  by pred_auto

lemma UINF_R5_closed [closure]: 
  "\<lbrakk> \<And> i. P i is R5 \<rbrakk> \<Longrightarrow> (\<Sqinter> i. P i) is R5"
  by (simp add: Healthy_def; pred_auto; blast)

lemma conj_R5_closed [closure]:
  "\<lbrakk> P is R5; Q is R5 \<rbrakk> \<Longrightarrow> (P \<and> Q) is R5"
  by (simp add: Healthy_def R5_conj)

lemma disj_R5_closed [closure]:
  "\<lbrakk> P is R5; Q is R5 \<rbrakk> \<Longrightarrow> (P \<or> Q) is R5"
  by (simp add: Healthy_def R5_disj)

lemma seq_R5_closed [closure]:
  "\<lbrakk> P is R5; Q is R5 \<rbrakk> \<Longrightarrow> (P ;; Q) is R5"
  by (pred_auto, metis)


subsection {* RP laws *}

definition RP_def [pred]: "RP(P) = R1(R2c(R3(P)))"

expr_ctr RP

lemma RP_comp_def: "RP = R1 \<circ> R2c \<circ> R3"
  by (auto simp add: RP_def)

lemma RP_alt_def: "RP(P) = R1(R2(R3(P)))"
  by (metis R1_R2c_is_R2 R1_idem RP_def)

lemma RP_intro: "\<lbrakk> P is R1; P is R2; P is R3 \<rbrakk> \<Longrightarrow> P is RP"
  by (simp add: Healthy_def' RP_alt_def)

lemma RP_idem: "RP(RP(P)) = RP(P)"
  by (simp add: R1_R2c_is_R2 R2_R3_commute R2_idem R3_idem RP_def)

lemma RP_Idempotent [closure]: "Idempotent RP"
  by (simp add: Idempotent_def RP_idem)

lemma RP_mono: "P \<sqsubseteq> Q \<Longrightarrow> RP(P) \<sqsubseteq> RP(Q)"
  by (simp add: R1_R2c_is_R2 R2_mono R3_mono RP_def)

lemma RP_Monotonic: "Monotonic RP"
  by (simp add: mono_def, pred_auto)
(* would be nice to reuse RP_mono
 * apply (simp add: mono_def RP_mono) *)

lemma RP_Continuous: "Continuous RP"
  by (simp add: Continuous_comp R1_Continuous R2c_Continuous R3_Continuous RP_comp_def)

lemma RP_skip:
  "RP(II) = II"
  by (simp add: R1_skip R2c_skip_r R3_skipr RP_def)

lemma RP_skip_closure [closure]:
  "II is RP"
  by (simp add: Healthy_def' RP_skip)

lemma RP_seq_closure [closure]:
  assumes "P is RP" "Q is RP"
  shows "(P ;; Q) is RP"
proof (rule RP_intro)
  show "(P ;; Q) is R1"
    by (metis Healthy_def R1_seqr RP_def assms)
  thus "(P ;; Q) is R2"
    by (metis Healthy_def' R2_R2c_def R2c_R1_seq RP_def  assms)
  show "(P ;; Q) is R3"
    by (metis (no_types, lifting) Healthy_def' R1_R2c_is_R2 R2_R3_commute R3_idem R3_semir_form RP_def assms)
qed

(*
subsection \<open> UTP theories \<close>

interpretation rea_theory: utp_theory_continuous RP
  rewrites "P \<in> carrier rea_theory.thy_order \<longleftrightarrow> P is RP"
  and "le des_theory.thy_order = (\<sqsubseteq>)"
  and "eq des_theory.thy_order = (=)"  
proof -
  show "utp_theory_continuous RP"
    by (unfold_locales, simp_all add: RP_idem RP_Continuous)
qed (simp_all)

notation rea_theory.utp_top ("\<^bold>\<top>\<^sub>r")
notation rea_theory.utp_bottom ("\<^bold>\<bottom>\<^sub>r")

interpretation rea_theory_rel: utp_theory_unital RP skip_r
  by (unfold_locales, simp_all add: closure)

lemma rea_top: "\<^bold>\<top>\<^sub>r = ($wait \<and> II)"
proof -
  have "\<^bold>\<top>\<^sub>r = RP(false)"
    by (simp add: rea_theory.healthy_top)
  also have "... = ($wait \<and> II)"
    by (rel_auto, metis minus_zero_eq)
  finally show ?thesis .
qed

lemma rea_top_left_zero:
  assumes "P is RP"
  shows "(\<^bold>\<top>\<^sub>r ;; P) = \<^bold>\<top>\<^sub>r"
proof -
  have "(\<^bold>\<top>\<^sub>r ;; P) = (($wait \<and> II) ;; R3(P))"
    by (metis (no_types, lifting) Healthy_def R1_R2c_is_R2 R2_R3_commute R3_idem RP_def assms rea_top)
  also have "... = ($wait \<and> R3(P))"
    by (rel_auto)
  also have "... = ($wait \<and> II)"
    by (metis R3_skipr wait_R3)
  also have "... = \<^bold>\<top>\<^sub>r"
    by (simp add: rea_top)
  finally show ?thesis .
qed

lemma rea_bottom: "\<^bold>\<bottom>\<^sub>r = R1($wait \<Rightarrow> II)"
proof -
  have "\<^bold>\<bottom>\<^sub>r = RP(true)"
    by (simp add: rea_theory.healthy_bottom)
  also have "... = R1($wait \<Rightarrow> II)"
    by (rel_auto, metis minus_zero_eq)
  finally show ?thesis .
qed
*)

end
