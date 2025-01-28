section \<open> Reactive Relations \<close>

theory utp_rea_rel
  imports 
    utp_rea_healths
    (* "utp_kleene" *)
begin

text \<open> This theory defines a reactive relational calculus for @{term R1}-@{term R2} predicates as an 
  extension of the standard alphabetised predicate calculus. This enables us to formally characterise
  relational programs that refer to both state variables and a trace history. For more details on
  reactive relations, please see the associated journal paper~\cite{Foster17c}. \<close>

subsection \<open> Healthiness Conditions \<close>

(*
definition RR :: "('t::trace, '\<alpha>, '\<beta>) rp_rel \<Rightarrow> ('t, '\<alpha>, '\<beta>) rp_rel" where
[pred]: "RR(P) = (\<Sqinter> k k' w w' :: bool. (R2 P)\<lbrakk>\<guillemotleft>k\<guillemotright>,\<guillemotleft>k'\<guillemotright>,\<guillemotleft>w\<guillemotright>,\<guillemotleft>w'\<guillemotright>/ok\<^sup><,ok\<^sup>>,wait\<^sup><,wait\<^sup>>\<rbrakk>)"
*)

definition RR :: "('t::trace, '\<alpha>, '\<beta>) rp_rel \<Rightarrow> ('t, '\<alpha>, '\<beta>) rp_rel" where
[pred]: "RR(P) = (\<exists> (ok\<^sup><,ok\<^sup>>,wait\<^sup><,wait\<^sup>>) \<Zspot> R2 P)"


expr_constructor RR

lemma RR_idem: "RR(RR(P)) = RR(P)"
  by pred_auto

lemma RR_Idempotent [closure]: "Idempotent RR"
  by (simp add: Idempotent_def RR_idem)

lemma RR_Continuous [closure]: "Continuous RR"
  by (pred_auto; blast)
    
lemma R1_RR: "R1(RR(P)) = RR(P)"
  by pred_auto
    
lemma R2c_RR: "R2c(RR(P)) = RR(P)"
  by pred_auto
    
lemma RR_implies_R1 [closure]: "P is RR \<Longrightarrow> P is R1"
  by (metis Healthy_def R1_RR)
  
lemma RR_implies_R2c: "P is RR \<Longrightarrow> P is R2c"
  by (metis Healthy_def R2c_RR)
  
lemma RR_implies_R2 [closure]: "P is RR \<Longrightarrow> P is R2"
  by (metis Healthy_def R1_RR R2_R2c_def R2c_RR)

(* TODO: is it possible to use a shorter simplifier proof as in UTP1? *)
lemma RR_intro:
  assumes "$ok\<^sup>< \<sharp> P" "$ok\<^sup>> \<sharp> P" "$wait\<^sup>< \<sharp> P" "$wait\<^sup>> \<sharp> P" "P is R1" "P is R2c"
  shows "P is RR"
proof (unfold Healthy_def)
  have "RR P = (\<Sqinter>k k' w w'. [ok\<^sup>< \<leadsto> k, ok\<^sup>> \<leadsto> k', wait\<^sup>< \<leadsto> w, wait\<^sup>> \<leadsto> w'] \<dagger> (R2s P \<triangleleft> (tr\<^sup>< \<le> tr\<^sup>>) \<triangleright> (P \<and> (tr\<^sup>< \<le> tr\<^sup>>)\<^sub>e)))"
    by (simp add: RR_def Healthy_def R2_R2c_def R1_def R2c_def R2s_def)
       (pred_auto; meson)
  also have "\<dots> = (\<Sqinter>k k' w w'. ([ok\<^sup>< \<leadsto> k, ok\<^sup>> \<leadsto> k', wait\<^sup>< \<leadsto> w, wait\<^sup>> \<leadsto> w'] \<dagger> R2s P) \<triangleleft> ([ok\<^sup>< \<leadsto> k, ok\<^sup>> \<leadsto> k', wait\<^sup>< \<leadsto> w, wait\<^sup>> \<leadsto> w'] \<dagger> (tr\<^sup>< \<le> tr\<^sup>>)) \<triangleright> ([ok\<^sup>< \<leadsto> k, ok\<^sup>> \<leadsto> k', wait\<^sup>< \<leadsto> w, wait\<^sup>> \<leadsto> w'] \<dagger> (P \<and> (tr\<^sup>< \<le> tr\<^sup>>)\<^sub>e)))"
    by pred_auto
  also have "\<dots> = (\<Sqinter>k k' w w'. ([ok\<^sup>< \<leadsto> k, ok\<^sup>> \<leadsto> k', wait\<^sup>< \<leadsto> w, wait\<^sup>> \<leadsto> w'] \<dagger> R2s P) \<triangleleft> (tr\<^sup>< \<le> tr\<^sup>>) \<triangleright> ([ok\<^sup>< \<leadsto> k, ok\<^sup>> \<leadsto> k', wait\<^sup>< \<leadsto> w, wait\<^sup>> \<leadsto> w'] \<dagger> P) \<and> (tr\<^sup>< \<le> tr\<^sup>>)\<^sub>e)"
    by (pred_auto)
  also have "\<dots> = (\<Sqinter>k k' w w'. R1([ok\<^sup>< \<leadsto> k, ok\<^sup>> \<leadsto> k', wait\<^sup>< \<leadsto> w, wait\<^sup>> \<leadsto> w'] \<dagger> R2s P))"
    by pred_auto
  also have "\<dots> = R1(R2s P)"
    using assms by (pred_auto; meson)
  also have "\<dots> = P"
    using assms unfolding Healthy_def
    by (simp add: R1_R2s_R2c)
  finally show "RR P = P" . 
qed

lemma RR_R2_intro:
  assumes "$ok\<^sup>< \<sharp> P" "$ok\<^sup>> \<sharp> P" "$wait\<^sup>< \<sharp> P" "$wait\<^sup>> \<sharp> P" "P is R2"
  shows "P is RR"
proof (unfold Healthy_def)
  have "\<And>k k' k'' k''' w w' w'' w''' t t' m m'.
        P (\<lparr>ok\<^sub>v = k, wait\<^sub>v = w, tr\<^sub>v = t, \<dots> = m\<rparr>, \<lparr>ok\<^sub>v = k', wait\<^sub>v = w', tr\<^sub>v = t', \<dots> = m'\<rparr>)
      = P (\<lparr>ok\<^sub>v = k'', wait\<^sub>v = w'', tr\<^sub>v = t, \<dots> = m\<rparr>, \<lparr>ok\<^sub>v = k''', wait\<^sub>v = w''', tr\<^sub>v = t', \<dots> = m'\<rparr>)"
    using assms apply pred_auto
    by meson+
  hence "RR(P) = R2 P"
    by (pred_auto; blast)
  thus "RR P = P"
    by (simp add: Healthy_if assms(5))
qed

lemma RR_unrests [unrest]:
  assumes "P is RR"
  shows "$ok\<^sup>< \<sharp> P" "$ok\<^sup>> \<sharp> P" "$wait\<^sup>< \<sharp> P" "$wait\<^sup>> \<sharp> P"
proof -
  have "$ok\<^sup>< \<sharp> RR P" "$ok\<^sup>> \<sharp> RR(P)" "$wait\<^sup>< \<sharp> RR(P)" "$wait\<^sup>> \<sharp> RR(P)"
    by (simp_all add: RR_def)
       (pred_auto+)
  thus "$ok\<^sup>< \<sharp> P" "$ok\<^sup>> \<sharp> P" "$wait\<^sup>< \<sharp> P" "$wait\<^sup>> \<sharp> P"
    by (simp_all add: assms Healthy_if)
qed

lemma RR_refine_intro:
  assumes "P is RR" "Q is RR" "\<And> t. P\<lbrakk>0,\<guillemotleft>t\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk> \<sqsubseteq> Q\<lbrakk>0,\<guillemotleft>t\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk>"
  shows "P \<sqsubseteq> Q"
proof -
  have "\<And> t. (RR P)\<lbrakk>0,\<guillemotleft>t\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk> \<sqsubseteq> (RR Q)\<lbrakk>0,\<guillemotleft>t\<guillemotright>/tr\<^sup><,tr\<^sup>>\<rbrakk>"
    by (simp add: Healthy_if assms)
  hence "RR(P) \<sqsubseteq> RR(Q)"
    by pred_auto
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma RR_eq_transfer:
  assumes "P is RR" "Q is RR" 
    "(\<And> t. [ok\<^sup>< \<leadsto> True, ok\<^sup>> \<leadsto> True, wait\<^sup>< \<leadsto> False, wait\<^sup>> \<leadsto> False, tr\<^sup>< \<leadsto> 0, tr\<^sup>> \<leadsto> \<guillemotleft>t\<guillemotright>] \<dagger> P 
          = [ok\<^sup>< \<leadsto> True, ok\<^sup>> \<leadsto> True, wait\<^sup>< \<leadsto> False, wait\<^sup>> \<leadsto> False, tr\<^sup>< \<leadsto> 0, tr\<^sup>> \<leadsto> \<guillemotleft>t\<guillemotright>] \<dagger> Q)"
  shows "P = Q"
proof -
  have "(\<And> t. [ok\<^sup>< \<leadsto> True, ok\<^sup>> \<leadsto> True, wait\<^sup>< \<leadsto> False, wait\<^sup>> \<leadsto> False, tr\<^sup>< \<leadsto> 0, tr\<^sup>> \<leadsto> \<guillemotleft>t\<guillemotright>] \<dagger> RR P 
            = [ok\<^sup>< \<leadsto> True, ok\<^sup>> \<leadsto> True, wait\<^sup>< \<leadsto> False, wait\<^sup>> \<leadsto> False, tr\<^sup>< \<leadsto> 0, tr\<^sup>> \<leadsto> \<guillemotleft>t\<guillemotright>] \<dagger> RR Q)"
    by (metis Healthy_if assms(1) assms(2) assms(3))
  hence "RR P = RR Q"
    by (simp add: RR_def; pred_auto)
  thus ?thesis
    by (metis Healthy_if assms(1) assms(2))
qed

text \<open> Tailored proof strategy for reactive relations -- eliminates irrelevant variables like ok, wait, and tr. \<close>

method rrel_auto uses cls = (rule RR_eq_transfer, simp add: closure cls, simp add: closure cls, rel_auto)

lemma R4_RR_closed [closure]:
  assumes "P is RR"
  shows "R4(P) is RR"
proof -
  have "R4(RR(P)) is RR"
    by pred_auto
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma R5_RR_closed [closure]:
  assumes "P is RR"
  shows "R5(P) is RR"
proof -
  have "R5(RR(P)) is RR"
    using minus_zero_eq by pred_auto
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

subsection \<open> Reactive relational operators \<close>

named_theorems rpred
  
abbreviation rea_true :: "('t::trace,'\<alpha>,'\<beta>) rp_rel" ("true\<^sub>r") where 
"true\<^sub>r \<equiv> R1(true)"     

definition rea_not :: "('t::trace,'\<alpha>,'\<beta>) rp_rel \<Rightarrow> ('t,'\<alpha>,'\<beta>) rp_rel" ("\<not>\<^sub>r _" [40] 40) 
  where [pred]: "(\<not>\<^sub>r P) = R1(\<not> P)"

expr_constructor rea_not

definition rea_diff :: "('t::trace,'\<alpha>,'\<beta>) rp_rel \<Rightarrow> ('t,'\<alpha>,'\<beta>) rp_rel \<Rightarrow> ('t,'\<alpha>,'\<beta>) rp_rel" (infixl "-\<^sub>r" 65)
where [pred]: "rea_diff P Q = (P \<and> \<not>\<^sub>r Q)"

expr_constructor rea_diff 

definition rea_impl :: 
  "('t::trace,'\<alpha>,'\<beta>) rp_rel \<Rightarrow> ('t,'\<alpha>,'\<beta>) rp_rel \<Rightarrow> ('t,'\<alpha>,'\<beta>) rp_rel" (infixr "\<longrightarrow>\<^sub>r" 25) 
where [pred]: "(P \<longrightarrow>\<^sub>r Q) = (\<not>\<^sub>r P \<or> Q)"

expr_constructor rea_impl

definition rea_lift :: "('t::trace,'\<alpha>,'\<beta>) rp_rel \<Rightarrow> ('t,'\<alpha>,'\<beta>) rp_rel" ("[_]\<^sub>r") 
where [pred]: "[P]\<^sub>r = R1(P)"

expr_constructor rea_lift

definition rea_skip :: "('t::trace,'\<alpha>) rp_hrel" ("II\<^sub>r") 
where [pred]: "II\<^sub>r = (tr\<^sup>> = tr\<^sup>< \<and> \<^bold>v\<^sub>R\<^sup>> = \<^bold>v\<^sub>R\<^sup><)\<^sub>e"

expr_constructor rea_skip

definition rea_assert :: "('t::trace,'\<alpha>) rp_hrel \<Rightarrow> ('t,'\<alpha>) rp_hrel" ("{_}\<^sub>r")
where [pred]: "{b}\<^sub>r = (II\<^sub>r \<or> \<not>\<^sub>r b)"

expr_constructor rea_assert

text \<open> Convert from one trace algebra to another using renamer functions, which are a kind of
  monoid homomorphism. \<close>

locale renamer =
  fixes f :: "'a::trace \<Rightarrow> 'b::trace"
  assumes 
    injective: "inj f" and
    add: "f (x + y) = f x + f y"
begin
  lemma zero: "f 0 = 0"
    by (metis add add.right_neutral add_monoid_diff_cancel_left)

  lemma monotonic: "mono f"
    by (metis add monoI trace_class.le_iff_add)

  lemma minus: "x \<le> y \<Longrightarrow> f (y - x) = f(y) - f(x)"
    by (metis add diff_add_cancel_left' trace_class.add_diff_cancel_left)
end

declare renamer.add [simp]
declare renamer.zero [simp]
declare renamer.minus [simp]

lemma renamer_id: "renamer id"
  by (unfold_locales, simp_all)

lemma renamer_comp: "\<lbrakk> renamer f; renamer g \<rbrakk> \<Longrightarrow> renamer (f \<circ> g)"
  by (unfold_locales, simp_all add: inj_compose renamer.injective)

lemma renamer_map: "inj f \<Longrightarrow> renamer (map f)"
  by (unfold_locales, simp_all add: plus_list_def)

definition rea_rename :: "('t\<^sub>1::trace,'\<alpha>) rp_hrel \<Rightarrow> ('t\<^sub>1 \<Rightarrow> 't\<^sub>2) \<Rightarrow> ('t\<^sub>2::trace,'\<alpha>) rp_hrel" ("(_)\<lparr>_\<rparr>\<^sub>r" [999, 0] 999) where
[pred]: "rea_rename P f = R2(((tr\<^sup>> = 0) \<and> \<^bold>v\<^sub>R\<^sup>> = \<^bold>v\<^sub>R\<^sup><)\<^sub>e ;; P ;; (tr\<^sup>> = \<guillemotleft>f\<guillemotright> (tr\<^sup><) \<and> \<^bold>v\<^sub>R\<^sup>> = \<^bold>v\<^sub>R\<^sup><)\<^sub>e)"

text \<open> Trace contribution substitution: make a substitution for the trace contribution lens 
  @{term tt}, and apply @{term R1} to make the resulting predicate healthy again. \<close>

definition rea_subst :: "('t :: trace, '\<alpha>) rp hrel \<Rightarrow> (('t, '\<alpha>) rp \<times> ('t, '\<alpha>) rp \<Rightarrow> 't) \<Rightarrow> ('t, '\<alpha>) rp hrel" ("_\<lbrakk>_\<rbrakk>\<^sub>r" [999,0] 999) 
where [pred]: "P\<lbrakk>v\<rbrakk>\<^sub>r = R1(P\<lbrakk>v/tt\<rbrakk>)\<^sub>e"

subsection \<open> Unrestriction and substitution laws \<close>

lemma rea_true_unrest [unrest]:
  assumes "mwb_lens x" "x \<bowtie> (ns_alpha fst\<^sub>L tr)" "x \<bowtie> (ns_alpha snd\<^sub>L tr)"
  shows "$x \<sharp> true\<^sub>r"
  by (simp add: R1_unrest assms unrest_pred)

lemma rea_not_unrest [unrest]:
  assumes "mwb_lens x" "x \<bowtie> (ns_alpha fst\<^sub>L tr)" "x \<bowtie> (ns_alpha snd\<^sub>L tr)" "$x \<sharp> P"
  shows "$x \<sharp> \<not>\<^sub>r P"
  using assms by (simp add: rea_not_def unrest_pred ns_alpha_def R1_unrest)
 
lemma rea_impl_unrest [unrest]:
  assumes "mwb_lens x" "x \<bowtie> (ns_alpha fst\<^sub>L tr)" "x \<bowtie> (ns_alpha snd\<^sub>L tr)" "$x \<sharp> P" "$x \<sharp> Q"
  shows "$x \<sharp> P \<longrightarrow>\<^sub>r Q"
  using assms by (simp add: rea_impl_def unrest)

lemma rea_true_usubst [usubst]:
  "\<lbrakk> $tr\<^sup>< \<sharp>\<^sub>s \<sigma>; $tr\<^sup>> \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> \<dagger> true\<^sub>r = true\<^sub>r"
  by (simp add: R1_def, subst_eval)
  
lemma rea_not_usubst [usubst]:
  "\<lbrakk> $tr\<^sup>< \<sharp>\<^sub>s \<sigma>; $tr\<^sup>> \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> \<dagger> (\<not>\<^sub>r P) = (\<not>\<^sub>r \<sigma> \<dagger> P)"
  by (simp add: rea_not_def R1_def, subst_eval)

lemma rea_impl_usubst [usubst]:
  "\<lbrakk> $tr\<^sup>< \<sharp>\<^sub>s \<sigma>; $tr\<^sup>> \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> \<dagger> (P \<longrightarrow>\<^sub>r Q) = (\<sigma> \<dagger> P \<longrightarrow>\<^sub>r \<sigma> \<dagger> Q)"
  by (simp add: rea_impl_def usubst R1_def)

lemma rea_true_usubst_tt [usubst]: 
  "R1(true)\<lbrakk>e/tt\<rbrakk> = true"
  by pred_auto

lemma unrests_rea_rename [unrest]: 
  "$ok\<^sup>< \<sharp> P \<Longrightarrow> $ok\<^sup>< \<sharp> P\<lparr>f\<rparr>\<^sub>r"
  "$ok\<^sup>> \<sharp> P \<Longrightarrow> $ok\<^sup>> \<sharp> P\<lparr>f\<rparr>\<^sub>r"
  "$wait\<^sup>< \<sharp> P \<Longrightarrow> $wait\<^sup>< \<sharp> P\<lparr>f\<rparr>\<^sub>r"
  "$wait\<^sup>> \<sharp> P \<Longrightarrow> $wait\<^sup>< \<sharp> P\<lparr>f\<rparr>\<^sub>r"
  by pred_auto+

lemma unrest_rea_subst [unrest]: 
  assumes "mwb_lens x" "x \<bowtie> (ns_alpha fst\<^sub>L tr)" "x \<bowtie> (ns_alpha snd\<^sub>L tr)" "$x \<sharp> v" "$x \<sharp> P" 
  shows "$x \<sharp> (P\<lbrakk>v\<rbrakk>\<^sub>r)"
proof -
  have "$x \<sharp> P\<lbrakk>v/tt\<rbrakk>"
    (* TODO: is there a non-SMT proof of this *)
    by (smt (verit) SEXP_def assms lens_indep.lens_put_comm subst_id_def subst_upd_def tt_indeps(2) unrest_lens unrest_subst_apply unrest_subst_lens)
  thus ?thesis
    using assms by (metis R1_unrest SEXP_def rea_subst_def)
qed

lemma rea_substs [usubst]: 
  "true\<^sub>r\<lbrakk>v\<rbrakk>\<^sub>r = true\<^sub>r" "true\<lbrakk>v\<rbrakk>\<^sub>r = true\<^sub>r" "false\<lbrakk>v\<rbrakk>\<^sub>r = false"
  "(\<not>\<^sub>r P)\<lbrakk>v\<rbrakk>\<^sub>r = (\<not>\<^sub>r P\<lbrakk>v\<rbrakk>\<^sub>r)" "(P \<and> Q)\<lbrakk>v\<rbrakk>\<^sub>r = (P\<lbrakk>v\<rbrakk>\<^sub>r \<and> Q\<lbrakk>v\<rbrakk>\<^sub>r)" "(P \<or> Q)\<lbrakk>v\<rbrakk>\<^sub>r = (P\<lbrakk>v\<rbrakk>\<^sub>r \<or> Q\<lbrakk>v\<rbrakk>\<^sub>r)"
  "(P \<longrightarrow>\<^sub>r Q)\<lbrakk>v\<rbrakk>\<^sub>r = (P\<lbrakk>v\<rbrakk>\<^sub>r \<longrightarrow>\<^sub>r Q\<lbrakk>v\<rbrakk>\<^sub>r)"
  by pred_auto+

lemma rea_substs_lattice [usubst]:
  "(\<Sqinter> i. P(i))\<lbrakk>v\<rbrakk>\<^sub>r   = (\<Sqinter> i. (P(i))\<lbrakk>v\<rbrakk>\<^sub>r)"
  "(\<Sqinter> i\<in>A. P(i))\<lbrakk>v\<rbrakk>\<^sub>r = (\<Sqinter> i\<in>A. (P(i))\<lbrakk>v\<rbrakk>\<^sub>r)"
  "(\<Squnion> i. P(i))\<lbrakk>v\<rbrakk>\<^sub>r   = (\<Squnion> i. (P(i))\<lbrakk>v\<rbrakk>\<^sub>r)"
   by pred_auto+
    
lemma rea_subst_USUP_set [usubst]:
  "A \<noteq> {} \<Longrightarrow> (\<Squnion> i\<in>A. P(i))\<lbrakk>v\<rbrakk>\<^sub>r   = (\<Squnion> i\<in>A. (P(i))\<lbrakk>v\<rbrakk>\<^sub>r)"
  by pred_auto+

subsection \<open> Closure laws \<close>

lemma rea_lift_R1 [closure]: "[P]\<^sub>r is R1"
  by pred_auto
    
lemma R1_rea_not: "R1(\<not>\<^sub>r P) = (\<not>\<^sub>r P)"
  by pred_auto
    
lemma R1_rea_not': "R1(\<not>\<^sub>r P) = (\<not>\<^sub>r R1(P))"
  by pred_auto 
  
lemma R2c_rea_not: "R2c(\<not>\<^sub>r P) = (\<not>\<^sub>r R2c(P))"
  by pred_auto

lemma RR_rea_not: "RR(\<not>\<^sub>r RR(P)) = (\<not>\<^sub>r RR(P))"
  by pred_auto
    
lemma R1_rea_impl: "R1(P \<longrightarrow>\<^sub>r Q) = (P \<longrightarrow>\<^sub>r R1(Q))"
  by pred_auto

lemma R1_rea_impl': "R1(P \<longrightarrow>\<^sub>r Q) = (R1(P) \<longrightarrow>\<^sub>r R1(Q))"
  by pred_auto
    
lemma R2c_rea_impl: "R2c(P \<longrightarrow>\<^sub>r Q) = (R2c(P) \<longrightarrow>\<^sub>r R2c(Q))"
  by pred_auto

lemma RR_rea_impl: "RR(RR(P) \<longrightarrow>\<^sub>r RR(Q)) = (RR(P) \<longrightarrow>\<^sub>r RR(Q))"
  by pred_auto
 
lemma rea_true_R1 [closure]: "true\<^sub>r is R1"
  by pred_auto
  
lemma rea_true_R2c [closure]: "true\<^sub>r is R2c"
  by pred_auto
    
lemma rea_true_RR [closure]: "true\<^sub>r is RR"
  by pred_auto
     
lemma rea_not_R1 [closure]: "\<not>\<^sub>r P is R1"
  by pred_auto

lemma rea_not_R2c [closure]: "P is R2c \<Longrightarrow> \<not>\<^sub>r P is R2c"
  by (simp add: Healthy_def rea_not_def R1_R2c_commute[THEN sym] R2c_not)
   
lemma rea_not_R2_closed [closure]:
  "P is R2 \<Longrightarrow> (\<not>\<^sub>r P) is R2"
  by (simp add: Healthy_def' R1_rea_not' R2_R2c_def R2c_rea_not)

lemma rea_no_RR [closure]:
  "\<lbrakk> P is RR \<rbrakk> \<Longrightarrow> (\<not>\<^sub>r P) is RR"
  by (metis Healthy_def' RR_rea_not)

lemma rea_impl_R1 [closure]: 
  "Q is R1 \<Longrightarrow> (P \<longrightarrow>\<^sub>r Q) is R1"
  by (pred_auto; blast)

lemma rea_impl_R2c [closure]: 
  "\<lbrakk> P is R2c; Q is R2c \<rbrakk> \<Longrightarrow> (P \<longrightarrow>\<^sub>r Q) is R2c"
  by (simp add: rea_impl_def Healthy_def rea_not_def R1_R2c_commute[THEN sym] R2c_not R2c_disj)

lemma rea_impl_R2 [closure]: 
  "\<lbrakk> P is R2; Q is R2 \<rbrakk> \<Longrightarrow> (P \<longrightarrow>\<^sub>r Q) is R2"
  by (pred_auto; blast)

lemma rea_impl_RR [closure]:
  "\<lbrakk> P is RR; Q is RR \<rbrakk> \<Longrightarrow> (P \<longrightarrow>\<^sub>r Q) is RR"
  by (metis Healthy_def' RR_rea_impl)


lemma conj_RR [closure]:
  "\<lbrakk> P is RR; Q is RR \<rbrakk> \<Longrightarrow> (P \<and> Q) is RR"
  by (meson RR_implies_R1 RR_implies_R2c RR_intro RR_unrests conj_R1_closed_1 conj_R2c_closed unrest_pred)

lemma disj_RR [closure]:
  "\<lbrakk> P is RR; Q is RR \<rbrakk> \<Longrightarrow> (P \<or> Q) is RR"
  by (metis Healthy_def' R1_RR R1_idem R1_rea_not' RR_rea_impl RR_rea_not pred_ba.boolean_algebra.double_compl rea_impl_def rea_not_def)

lemma USUP_mem_RR_closed [closure]:
  assumes "\<And> i. i \<in> A \<Longrightarrow> P i is RR" "A \<noteq> {}"
  shows "(\<Squnion> i\<in>A. P(i)) is RR"
proof -
  have 1:"(\<Squnion> i\<in>A. P(i)) is R1"
    by (unfold Healthy_def, subst R1_UINF, simp_all add: Healthy_if assms closure cong: INF_cong)
  have 2:"(\<Squnion> i\<in>A. P(i)) is R2c"
    by (unfold Healthy_def, subst R2c_UINF, simp_all add: Healthy_if assms RR_implies_R2c closure cong: INF_cong)
  show ?thesis
    using 1 2 by (rule_tac RR_intro, simp_all add: unrest assms)
qed

lemma USUP_ind_RR_closed [closure]:
  assumes "\<And> i. P i is RR"
  shows "(\<Squnion> i. P(i)) is RR"
  using USUP_mem_RR_closed[of UNIV P] by (simp add: assms)

lemma UINF_mem_RR_closed [closure]:
  assumes "\<And> i. i \<in> A \<Longrightarrow> P i is RR"
  shows "(\<Sqinter> i\<in>A. P(i)) is RR"
proof -
  have 1:"(\<Sqinter> i\<in>A. P(i)) is R1"
    by (unfold Healthy_def, subst R1_USUP, simp add: Healthy_if RR_implies_R1 assms cong: SUP_cong)
  have 2:"(\<Sqinter> i\<in>A. P(i)) is R2c"
    by (unfold Healthy_def, subst R2c_USUP, simp add: Healthy_if RR_implies_R2c assms cong: SUP_cong)
  show ?thesis
    using 1 2 by (rule_tac RR_intro, simp_all add: unrest assms)
qed
    
lemma UINF_ind_RR_closed [closure]:
  assumes "\<And> i. P i is RR"
  shows "(\<Sqinter> i. P(i)) is RR"
  by (simp add: assms closure)

lemma USUP_elem_RR [closure]: 
  assumes "\<And> i. P i is RR" "A \<noteq> {}"
  shows "(\<Squnion> i \<in> A. P i) is RR"
proof -
  have "(\<Squnion> i\<in>A. P(i)) is R1"
    by (unfold Healthy_def, subst R1_UINF, simp_all add: Healthy_if assms closure)
  moreover have "(\<Squnion> i\<in>A. P(i)) is R2c"
    by (unfold Healthy_def, subst R2c_UINF, simp_all add: Healthy_if assms RR_implies_R2c closure)
  ultimately show ?thesis
    by (rule_tac RR_intro, simp_all add: unrest assms)
qed

lemma seq_RR_closed [closure]: 
  assumes "P is RR" "Q is RR"
  shows "P ;; Q is RR"
proof -
  have "P is R2" "Q is R2"
    using RR_implies_R2 assms by blast+
  then have 1: "P ;; Q is R2"
    using R2_seqr_closure by blast
  have "$ok\<^sup>< \<sharp> P" "$wait\<^sup>< \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$wait\<^sup>> \<sharp> Q"
    using RR_unrests assms by blast+
  then have 2: "$ok\<^sup>< \<sharp> P ;; Q" "$wait\<^sup>< \<sharp> P ;; Q" "$ok\<^sup>> \<sharp> P ;; Q" "$wait\<^sup>> \<sharp> P ;; Q"
    by (metis ok_vwb_lens wait_vwb_lens seqr_liberate_left seqr_liberate_right unrest_liberate_iff)+
  then show ?thesis
    using 1 2 RR_R2_intro by blast
qed

lemma power_Suc_RR_closed [closure]:
  "P is RR \<Longrightarrow> P ;; P \<^bold>^ i is RR"
  by (induct i, simp_all add: closure upred_semiring.power_Suc)
    
lemma seqr_iter_RR_closed [closure]:
  "\<lbrakk> I \<noteq> []; \<And> i. i \<in> set(I) \<Longrightarrow> P(i) is RR \<rbrakk> \<Longrightarrow> (;; i : I \<bullet> P(i)) is RR"
  apply (induct I, simp_all)
  apply (rename_tac i I)
  apply (case_tac I)
  apply (simp_all add: seq_RR_closed)
  done

lemma cond_tt_RR_closed [closure]: 
  assumes "P is RR" "Q is RR"
  shows "P \<triangleleft> $tr\<^sup>> = $tr\<^sup>< \<triangleright> Q is RR"
proof -
  have "RR P \<triangleleft> $tr\<^sup>> = $tr\<^sup>< \<triangleright> RR Q is RR"
    by (pred_simp, meson dual_order.refl minus_zero_eq trace_class.diff_cancel)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma rea_skip_RR [closure]:
  "II\<^sub>r is RR"
  apply pred_auto using minus_zero_eq by blast

lemma tr_eq_tr'_RR_closed [closure]: "(tr\<^sup>< = tr\<^sup>>)\<^sub>e is RR"
  apply pred_auto using minus_zero_eq by auto

lemma tr'_eq_tr_RR_closed [closure]: "(tr\<^sup>> = tr\<^sup><)\<^sub>e is RR"
  apply pred_auto using minus_zero_eq by auto

lemma inf_RR_closed [closure]: 
  "\<lbrakk> P is RR; Q is RR \<rbrakk> \<Longrightarrow> P \<sqinter> Q is RR"
  by (metis disj_RR disj_pred_def)

lemma conj_tr_strict_RR_closed [closure]: 
  assumes "P is RR"
  shows "(P \<and> (tr\<^sup>< < tr\<^sup>>)\<^sub>e) is RR"
proof -
  have "RR(RR(P) \<and> (tr\<^sup>< < tr\<^sup>>)\<^sub>e) = (RR(P) \<and> (tr\<^sup>< < tr\<^sup>>)\<^sub>e)"
    by pred_auto
  thus ?thesis
    by (metis (no_types, lifting) Healthy_def assms)  
qed

lemma rea_assert_RR_closed [closure]:
  assumes "b is RR"
  shows "{b}\<^sub>r is RR"
  by (simp add: closure assms rea_assert_def)  

lemma upower_RR_closed [closure]:
  "\<lbrakk> i > 0; P is RR \<rbrakk> \<Longrightarrow> P \<^bold>^ i is RR"
  apply (induct i, simp_all)
  apply (rename_tac i)
  apply (case_tac "i = 0")
   apply (simp_all add: closure upred_semiring.power_Suc)
  done

lemma seq_power_RR_closed [closure]:
  assumes "P is RR" "Q is RR"
  shows "(P \<^bold>^ i) ;; Q is RR"
  by (metis assms neq0_conv seq_RR_closed seqr_left_unit upower_RR_closed upred_semiring.power_0)

(*
lemma ustar_right_RR_closed [closure]:
  assumes "P is RR" "Q is RR"
  shows "P ;; Q\<^sup>\<star> is RR"
proof -
  have "P ;; Q\<^sup>\<star> = P ;; (\<Sqinter> i \<in> {0..} \<bullet> Q \<^bold>^ i)"
    by (simp add: ustar_def)
  also have "... = P ;; (II \<sqinter> (\<Sqinter> i \<in> {1..} \<bullet> Q \<^bold>^ i))"
    by (metis One_nat_def UINF_atLeast_first upred_semiring.power_0)
  also have "... = (P \<or> P ;; (\<Sqinter> i \<in> {1..} \<bullet> Q \<^bold>^ i))"
    by (simp add: disj_upred_def[THEN sym] seqr_or_distr)
  also have "... is RR"
  proof -
    have "(\<Sqinter> i \<in> {1..} \<bullet> Q \<^bold>^ i) is RR"
      by (rule UINF_mem_Continuous_closed, simp_all add: assms closure)
    thus ?thesis
      by (simp add: assms closure)
  qed
  finally show ?thesis .
qed

lemma ustar_left_RR_closed [closure]:
  assumes "P is RR" "Q is RR"
  shows "P\<^sup>\<star> ;; Q is RR"
proof -
  have "P\<^sup>\<star> ;; Q = (\<Sqinter> i \<in> {0..} \<bullet> P \<^bold>^ i) ;; Q"
    by (simp add: ustar_def)
  also have "... = (II \<sqinter> (\<Sqinter> i \<in> {1..} \<bullet> P \<^bold>^ i)) ;; Q"
    by (metis One_nat_def UINF_atLeast_first upred_semiring.power_0)
  also have "... = (Q \<or> (\<Sqinter> i \<in> {1..} \<bullet> P \<^bold>^ i) ;; Q)"
    by (simp add: disj_upred_def[THEN sym] seqr_or_distl)
  also have "... is RR"
  proof -
    have "(\<Sqinter> i \<in> {1..} \<bullet> P \<^bold>^ i) is RR"
      by (rule UINF_mem_Continuous_closed, simp_all add: assms closure)
    thus ?thesis
      by (simp add: assms closure)
  qed
  finally show ?thesis .
qed

lemma uplus_RR_closed [closure]: "P is RR \<Longrightarrow> P\<^sup>+ is RR"
  by (simp add: uplus_def ustar_right_RR_closed)
*)

(* TODO: should hold for an arbitrary trace algebra *)
lemma trace_ext_prefix_RR [closure]: "$tr\<^sup>< \<sharp> e \<Longrightarrow> $ok\<^sup>< \<sharp> e \<Longrightarrow> $wait\<^sup>< \<sharp> e \<Longrightarrow> out\<alpha> \<sharp> e \<Longrightarrow> (($tr)\<^sup>< @ e \<le> ($tr)\<^sup>>)\<^sub>e is RR"
  apply(pred_auto)
  apply (metis (no_types, lifting) Prefix_Order.prefixE Prefix_Order.same_prefix_prefix append_minus append_self_conv2 zero_list_def)
  by (metis (no_types, lifting) Prefix_Order.same_prefix_prefix diff_add_cancel_left' list_append_prefixD plus_list_def self_append_conv2 zero_list_def)

lemma rea_subst_R1_closed [closure]: "P\<lbrakk>v\<rbrakk>\<^sub>r is R1"
  by pred_auto

lemma R5_comp [rpred]:
  assumes "P is RR" "Q is RR"
  shows "R5(P ;; Q) = R5(P) ;; R5(Q)"
proof -
  have "R5(RR(P) ;; RR(Q)) = R5(RR(P)) ;; R5(RR(Q))"
    by (pred_auto; force)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma R4_comp [rpred]:
  assumes "P is R4" "Q is RR"
  shows "R4(P ;; Q) = P ;; Q"
proof -
  have "R4(R4(P) ;; RR(Q)) = R4(P) ;; RR(Q)"
    by (pred_auto, blast)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma rea_rename_RR_closed [closure]: 
  assumes "P is RR"
  shows "P\<lparr>f\<rparr>\<^sub>r is RR"
proof -
  have "(RR P)\<lparr>f\<rparr>\<^sub>r is RR"
    by pred_auto
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

subsection \<open> Reactive relational calculus \<close>

lemma rea_skip_unit [rpred]:
  assumes "P is RR"
  shows "P ;; II\<^sub>r = P" "II\<^sub>r ;; P = P"
proof -
  have 1: "RR(P) ;; II\<^sub>r = RR(P)"
    by pred_auto
  have 2: "II\<^sub>r ;; RR(P) = RR(P)"
    by pred_auto
  from 1 2 show "P ;; II\<^sub>r = P" "II\<^sub>r ;; P = P"
    by (simp_all add: Healthy_if assms)
qed

lemma rea_true_conj [rpred]: 
  assumes "P is R1"
  shows "(true\<^sub>r \<and> P) = P" "(P \<and> true\<^sub>r) = P"
  using assms apply (metis Healthy_if R1_extend_conj pred_ba.inf_top_left)
  using assms apply (metis Healthy_if R1_conj pred_ba.inf_top.right_neutral)
  done

lemma rea_true_disj [rpred]: 
  assumes "P is R1"
  shows "(true\<^sub>r \<or> P) = true\<^sub>r" "(P \<or> true\<^sub>r) = true\<^sub>r"
  apply (metis assms disj_R1_closed pred_ba.inf_sup_absorb rea_true_R1 rea_true_conj(1))
  apply (metis Healthy_if R1_disj assms pred_ba.boolean_algebra.disj_one_right)
  done

lemma rea_not_not [rpred]: "P is R1 \<Longrightarrow> (\<not>\<^sub>r \<not>\<^sub>r P) = P"
  by (simp add: rea_not_def R1_negate_R1 Healthy_if)
    
lemma rea_not_rea_true [simp]: "(\<not>\<^sub>r true\<^sub>r) = false"
  by (simp add: rea_not_def R1_negate_R1 R1_false)
    
lemma rea_not_false [simp]: "(\<not>\<^sub>r false) = true\<^sub>r"
  by (simp add: rea_not_def)
    
lemma rea_true_impl [rpred]:
  "P is R1 \<Longrightarrow> (true\<^sub>r \<longrightarrow>\<^sub>r P) = P"
  by (simp add: rea_not_def rea_impl_def R1_negate_R1 R1_false Healthy_if)

lemma rea_true_impl' [rpred]:
  "P is R1 \<Longrightarrow>(true \<longrightarrow>\<^sub>r P) = P"
  by (simp add: rea_not_def rea_impl_def R1_negate_R1 R1_false Healthy_if)

lemma rea_false_impl [rpred]:
  "P is R1 \<Longrightarrow> (false \<longrightarrow>\<^sub>r P) = true\<^sub>r"
  by (simp add: rea_impl_def rpred Healthy_if)
 
lemma rea_impl_true [simp]: "(P \<longrightarrow>\<^sub>r true\<^sub>r) = true\<^sub>r"
  by pred_auto
    
lemma rea_impl_false [simp]: "(P \<longrightarrow>\<^sub>r false) = (\<not>\<^sub>r P)"
  by pred_simp

lemma rea_imp_refl [rpred]: "P is R1 \<Longrightarrow> (P \<longrightarrow>\<^sub>r P) = true\<^sub>r"
  by (pred_auto; blast)

lemma rea_impl_conj [rpred]: 
  "(P \<longrightarrow>\<^sub>r Q \<longrightarrow>\<^sub>r R) = ((P \<and> Q) \<longrightarrow>\<^sub>r R)"
  by pred_auto

lemma rea_impl_mp [rpred]:
  "(P \<and> (P \<longrightarrow>\<^sub>r Q)) = (P \<and> Q)"
  by pred_auto

lemma rea_impl_conj_combine [rpred]: 
  "((P \<longrightarrow>\<^sub>r Q) \<and> (P \<longrightarrow>\<^sub>r R)) = (P \<longrightarrow>\<^sub>r Q \<and> R)"
  by pred_auto

lemma rea_impl_alt_def:
  assumes "Q is R1"
  shows "(P \<longrightarrow>\<^sub>r Q) = R1(P \<longrightarrow> Q)"
proof -
  have "(P \<longrightarrow>\<^sub>r R1(Q)) = R1(P \<longrightarrow> Q)"
    by pred_auto
  thus ?thesis
    by (simp add: assms Healthy_if)
qed

lemma rea_impl_disj:
  "(P \<longrightarrow>\<^sub>r Q \<or> R) = (Q \<or> (P \<longrightarrow>\<^sub>r R))"
  by pred_auto

lemma rea_not_true [simp]: "(\<not>\<^sub>r true) = false"
  by pred_auto
    
lemma rea_not_demorgan1 [simp]:
  "(\<not>\<^sub>r (P \<and> Q)) = (\<not>\<^sub>r P \<or> \<not>\<^sub>r Q)"
  by pred_auto

lemma rea_not_demorgan2 [simp]:
  "(\<not>\<^sub>r (P \<or> Q)) = (\<not>\<^sub>r P \<and> \<not>\<^sub>r Q)"
  by pred_auto

lemma rea_not_or [rpred]:
  "P is R1 \<Longrightarrow> (P \<or> \<not>\<^sub>r P) = true\<^sub>r"
  by (pred_auto; blast)

lemma rea_not_and [simp]:
  "(P \<and> \<not>\<^sub>r P) = false"
  by pred_auto

lemma truer_bottom_rpred [rpred]: "P is RR \<Longrightarrow> R1(true) \<sqsubseteq> P"
  by (simp add: RR_implies_R1 pred_ba.sup.order_iff rea_true_disj(1))

lemma ext_close_weakening: "P ;; true\<^sub>r \<sqsubseteq> P"
  by pred_auto

lemma rea_not_INFIMUM [simp]:
  "(\<not>\<^sub>r (\<Squnion>i\<in>A. Q(i))) = (\<Sqinter>i\<in>A. \<not>\<^sub>r Q(i))"
  by pred_auto

(* Why is this a separate law? *)
lemma rea_not_USUP [simp]:
  "(\<not>\<^sub>r (\<Squnion>i\<in>A. Q(i))) = (\<Sqinter>i\<in>A. \<not>\<^sub>r Q(i))"
  by simp
    
lemma rea_not_SUPREMUM [simp]:
  "A \<noteq> {} \<Longrightarrow> (\<not>\<^sub>r (\<Sqinter>i\<in>A. Q(i))) = (\<Squnion>i\<in>A. \<not>\<^sub>r Q(i))"
  by pred_auto

(* Why is this a separate law? *)
lemma rea_not_UINF [simp]:
  "A \<noteq> {} \<Longrightarrow> (\<not>\<^sub>r (\<Sqinter>i\<in>A. Q(i))) = (\<Squnion>i\<in>A. \<not>\<^sub>r Q(i))"
  by pred_auto

lemma USUP_mem_rea_true [simp]: "A \<noteq> {} \<Longrightarrow> (\<Squnion> i \<in> A. true\<^sub>r) = true\<^sub>r"
  by pred_auto

lemma USUP_ind_rea_true [simp]: "(\<Squnion> i. true\<^sub>r) = true\<^sub>r"
  by pred_auto
    
lemma UINF_ind_rea_true [rpred]: "A \<noteq> {} \<Longrightarrow> (\<Sqinter> i\<in>A. true\<^sub>r) = true\<^sub>r"
  by pred_auto

lemma UINF_rea_impl: "(\<Sqinter> P\<in>A. F(P) \<longrightarrow>\<^sub>r G(P)) = ((\<Squnion> P\<in>A. F(P)) \<longrightarrow>\<^sub>r (\<Sqinter> P\<in>A. G(P)))"
  by pred_auto  

(*
lemma rea_not_shEx [rpred]: "(\<not>\<^sub>r shEx P) = (shAll (\<lambda> x. \<not>\<^sub>r P x))"
  by pred_auto
*)

lemma rea_assert_true:
  "{true\<^sub>r}\<^sub>r = II\<^sub>r"
  by pred_auto

lemma rea_false_true:
  "{false}\<^sub>r = true\<^sub>r"
  by pred_auto

lemma rea_rename_id [rpred]: 
  assumes "P is RR"
  shows "P\<lparr>id\<rparr>\<^sub>r = P"
proof -
  have "(RR P)\<lparr>id\<rparr>\<^sub>r = RR P"
    by pred_auto
  thus ?thesis by (simp add: Healthy_if assms)
qed

(* twright: This was also oopsed in UTP1
lemma rea_rename_comp [rpred]: 
  assumes "renamer f" "renamer g" "P is RR"
  shows "P\<lparr>g \<circ> f\<rparr>\<^sub>r = P\<lparr>g\<rparr>\<^sub>r\<lparr>f\<rparr>\<^sub>r"
  oops
*)

lemma rea_rename_false [rpred]: "false\<lparr>f\<rparr>\<^sub>r = false"
  by pred_auto

lemma rea_rename_disj [rpred]: 
  "(P \<or> Q)\<lparr>f\<rparr>\<^sub>r = (P\<lparr>f\<rparr>\<^sub>r \<or> Q\<lparr>f\<rparr>\<^sub>r)"
  by (pred_auto; blast)

lemma rea_rename_UINF_ind [rpred]:
  "(\<Sqinter> i. P i)\<lparr>g\<rparr>\<^sub>r = (\<Sqinter> i. (P i)\<lparr>g\<rparr>\<^sub>r)"
  by (pred_auto; blast)

lemma rea_rename_UINF_mem [rpred]:
  "(\<Sqinter> i\<in>A. P i)\<lparr>g\<rparr>\<^sub>r = (\<Sqinter> i\<in>A. (P i)\<lparr>g\<rparr>\<^sub>r)"
  by (pred_auto; blast)

lemma rea_rename_conj [rpred]: 
  assumes "renamer g" "P is RR" "Q is RR"
  shows "(P \<and> Q)\<lparr>g\<rparr>\<^sub>r = (P\<lparr>g\<rparr>\<^sub>r \<and> Q\<lparr>g\<rparr>\<^sub>r)"
proof -
  interpret ren: renamer g by (simp add: assms)
  have "(RR P \<and> RR Q)\<lparr>g\<rparr>\<^sub>r = ((RR P)\<lparr>g\<rparr>\<^sub>r \<and> (RR Q)\<lparr>g\<rparr>\<^sub>r)"
    using injD[OF ren.injective]
    by (pred_auto; blast)
  thus ?thesis by (simp add: Healthy_if assms)
qed

lemma rea_rename_USUP_ind [rpred]:
  assumes "renamer g" "\<And> i. P i is RR"
  shows "(\<Squnion> i. P i)\<lparr>g\<rparr>\<^sub>r = (\<Squnion> i. (P i)\<lparr>g\<rparr>\<^sub>r)"
proof -
  interpret ren: renamer g by (simp add: assms)
  have "(\<Squnion> i. RR(P i))\<lparr>g\<rparr>\<^sub>r = (\<Squnion> i. (RR (P i))\<lparr>g\<rparr>\<^sub>r)"
    using injD[OF ren.injective]
    by (pred_auto, blast, metis (mono_tags, opaque_lifting))
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma rea_rename_USUP_mem [rpred]:
  assumes "renamer g" "A \<noteq> {}" "\<And> i. i \<in> A \<Longrightarrow> P i is RR"
  shows "(\<Squnion> i\<in>A. P i)\<lparr>g\<rparr>\<^sub>r = (\<Squnion> i\<in>A. (P i)\<lparr>g\<rparr>\<^sub>r)"
proof -
  interpret ren: renamer g by (simp add: assms)
  have "(\<Squnion> i\<in>A. RR(P i))\<lparr>g\<rparr>\<^sub>r = (\<Squnion> i\<in>A. (RR (P i))\<lparr>g\<rparr>\<^sub>r)"
    using injD[OF ren.injective] assms(2)
    by (pred_auto, blast, metis (no_types, opaque_lifting))
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma rea_rename_skip_rea [rpred]: "renamer f \<Longrightarrow> II\<^sub>r\<lparr>f\<rparr>\<^sub>r = II\<^sub>r"
  using minus_zero_eq by pred_auto

lemma rea_rename_seq [rpred]: 
  assumes "renamer g" "P is RR" "Q is RR"
  shows "(P ;; Q)\<lparr>g\<rparr>\<^sub>r = P\<lparr>g\<rparr>\<^sub>r ;; Q\<lparr>g\<rparr>\<^sub>r"
proof -
  interpret ren: renamer g by (simp add: assms)
  from assms(1) have "(RR(P) ;; RR(Q))\<lparr>g\<rparr>\<^sub>r = (RR P)\<lparr>g\<rparr>\<^sub>r ;; (RR Q)\<lparr>g\<rparr>\<^sub>r"
    by (pred_auto)
       (metis (no_types, lifting) diff_add_cancel_left' le_add minus_assoc mono_def ren.minus ren.monotonic trace_class.add_diff_cancel_left trace_class.add_left_mono)+
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

declare R4_idem [rpred]
declare R4_false [rpred]
declare R4_conj [rpred]
declare R4_disj [rpred]

declare R4_R5 [rpred]
declare R5_R4 [rpred]

declare R5_conj [rpred]
declare R5_disj [rpred]

lemma R4_USUP [rpred]: "I \<noteq> {} \<Longrightarrow> R4(\<Squnion> i\<in>I. P(i)) = (\<Squnion> i\<in>I. R4(P(i)))"
  by pred_auto

lemma R5_USUP [rpred]: "I \<noteq> {} \<Longrightarrow> R5(\<Squnion> i\<in>I. P(i)) = (\<Squnion> i\<in>I. R5(P(i)))"
  by pred_auto

lemma R4_UINF [rpred]: "R4(\<Sqinter> i\<in>I. P(i)) = (\<Sqinter> i\<in>I. R4(P(i)))"
  by pred_auto

lemma R5_UINF [rpred]: "R5(\<Sqinter> i\<in>I. P(i)) = (\<Sqinter> i\<in>I. R5(P(i)))"
  by pred_auto

subsection \<open> UTP theory \<close>

text \<open> We create a UTP theory of reactive relations which in particular provides Kleene star theorems \<close>

interpretation rrel_theory: utp_theory_kleene RR II\<^sub>r
  rewrites "P \<in> carrier rrel_theory.thy_order \<longleftrightarrow> P is RR"
  and "le rrel_theory.thy_order = (\<sqsubseteq>)"
  and "eq rrel_theory.thy_order = (=)"  
  and rrel_top: "rrel_theory.utp_top = false"
  and rrel_bottom: "rrel_theory.utp_bottom = true\<^sub>r"
proof -
  interpret utp_theory_continuous RR
    by (unfold_locales, simp_all add: add: RR_Idempotent RR_Continuous)
  show top:"utp_top = false"
    by (simp add: healthy_top, pred_auto)
  show bot:"utp_bottom = true\<^sub>r"
    by (simp add: healthy_bottom, pred_auto)
  show "utp_theory_kleene RR II\<^sub>r"
    by (unfold_locales, simp_all add: closure rpred top)
qed (simp_all)

abbreviation rea_star :: "_ \<Rightarrow> _"  ("_\<^sup>\<star>\<^sup>r" [999] 999) where
"P\<^sup>\<star>\<^sup>r \<equiv> rrel_theory.utp_star P"

text \<open> The supernova tactic explodes conjectures using the Kleene star laws and relational calculus \<close>

method supernova = ((safe intro!: rrel_theory.Star_inductr rrel_theory.Star_inductl, simp_all add: closure) ; rel_auto)[1]

find_theorems unrest expr_if


subsection \<open> Instantaneous Reactive Relations \<close>

text \<open> Instantaneous Reactive Relations, where the trace stays the same. \<close>
  
abbreviation Instant :: "('t::trace, '\<alpha>) rp_hrel \<Rightarrow> ('t, '\<alpha>) rp_hrel" where
"Instant(P) \<equiv> (- $tr):[P]"

lemma skip_rea_Instant [closure]: "II\<^sub>r is Instant"
  by (pred_auto)

end