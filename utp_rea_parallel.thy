section \<open> Reactive Parallel-by-Merge \<close>

theory utp_rea_parallel
  imports utp_rea_healths
begin

unbundle UTP_Syntax

text \<open> We show closure of parallel by merge under the reactive healthiness conditions by means
  of suitable restrictions on the merge predicate~\cite{Foster17b}. We first define healthiness 
  conditions for $R1$ and $R2$ merge predicates. \<close>

definition R1m :: "('t :: trace, '\<alpha>) rp merge \<Rightarrow> ('t, '\<alpha>) rp merge"
  where [pred]: "R1m(M) = (M \<and> $<:tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e"

definition R1m' :: "('t :: trace, '\<alpha>) rp merge \<Rightarrow> ('t, '\<alpha>) rp merge"
  where [pred]: "R1m'(M) = (M \<and> $<:tr\<^sup>< \<le> $tr\<^sup>> \<and> $<:tr\<^sup>< \<le> $0:tr\<^sup>< \<and> $<:tr\<^sup>< \<le> $1:tr\<^sup><)\<^sub>e"

text \<open> A merge predicate can access the history through $tr$, as usual, but also through $0.tr$ and
  $1.tr$. Thus we have to remove the latter two histories as well to satisfy R2 for the overall
  construction. \<close>

definition R2m :: "('t :: trace, '\<alpha>) rp merge \<Rightarrow> ('t, '\<alpha>) rp merge"
  where [pred]: "R2m(M) = R1m(M\<lbrakk>0,($tr\<^sup>>-$<:tr\<^sup><),($0:tr\<^sup><-$<:tr\<^sup><),($1:tr\<^sup><-$<:tr\<^sup><)/<:tr\<^sup><,tr\<^sup>>,0:tr\<^sup><,1:tr\<^sup><\<rbrakk>)\<^sub>e"

definition R2m' :: "('t :: trace, '\<alpha>) rp merge \<Rightarrow> ('t, '\<alpha>) rp merge"
  where [pred]: "R2m'(M) = R1m'(M\<lbrakk>0,($tr\<^sup>>-$<:tr\<^sup><),($0:tr\<^sup><-$<:tr\<^sup><),($1:tr\<^sup><-$<:tr\<^sup><)/<:tr\<^sup><,tr\<^sup>>,0:tr\<^sup><,1:tr\<^sup><\<rbrakk>)"

definition R2cm :: "('t :: trace, '\<alpha>) rp merge \<Rightarrow> ('t, '\<alpha>) rp merge"
  where [pred]: "R2cm(M) = (M\<lbrakk>0,($tr\<^sup>>-$<:tr\<^sup><),($0:tr\<^sup><-$<:tr\<^sup><),($1:tr\<^sup><-$<:tr\<^sup><)/<:tr\<^sup><,tr\<^sup>>,0:tr\<^sup><,1:tr\<^sup><\<rbrakk> \<triangleleft> $<:tr\<^sup>< \<le> $tr\<^sup>> \<triangleright> M)\<^sub>e"

lemma R2m'_form:
  "R2m'(M) =
  (\<exists> tt\<^sub>p tt\<^sub>0 tt\<^sub>1. M\<lbrakk>0,\<guillemotleft>tt\<^sub>p\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/<:tr\<^sup><,tr\<^sup>>,0:tr\<^sup><,1:tr\<^sup><\<rbrakk>
                 \<and> $tr\<^sup>> = $<:tr\<^sup>< + \<guillemotleft>tt\<^sub>p\<guillemotright>
                 \<and> $0:tr\<^sup>< = $<:tr\<^sup>< + \<guillemotleft>tt\<^sub>0\<guillemotright>
                 \<and> $1:tr\<^sup>< = $<:tr\<^sup>< + \<guillemotleft>tt\<^sub>1\<guillemotright>)\<^sub>e"
  by (pred_auto, metis diff_add_cancel_left')

lemma R1m_idem: "R1m(R1m(P)) = R1m(P)"
  by (pred_auto)

lemma R1m_seq_lemma: "R1m(R1m(M) ;; R1(P)) = R1m(M) ;; R1(P)"
  by (pred_auto)

lemma R1m_seq [closure]:
  assumes "M is R1m" "P is R1"
  shows "M ;; P is R1m"
proof -
  from assms have "R1m(M ;; P) = R1m(R1m(M) ;; R1(P))"
    by (simp add: Healthy_if)
  also have "... = R1m(M) ;; R1(P)"
    by (simp add: R1m_seq_lemma)
  also have "... = M ;; P"
    by (simp add: Healthy_if assms)
  finally show ?thesis
    by (simp add: Healthy_def)
qed

lemma R2m_idem: "R2m(R2m(P)) = R2m(P)"
  by (pred_auto)

lemma R2m_seq_lemma: "R2m'(R2m'(M) ;; R2(P)) = R2m'(M) ;; R2(P)"
  apply (simp add: R2m'_form R2_form)
  apply (pred_auto)
   apply (metis (no_types, lifting) add.assoc)+
  done

lemma R2m'_seq [closure]:
  assumes "M is R2m'" "P is R2"
  shows "M ;; P is R2m'"
  by (metis Healthy_def' R2m_seq_lemma assms(1) assms(2))

lemma R1_par_by_merge [closure]:
  "M is R1m \<Longrightarrow> (P \<parallel>\<^bsub>M\<^esub> Q) is R1"
  by (pred_simp, blast)
    
lemma R2_R2m'_pbm: "R2(P \<parallel>\<^bsub>M\<^esub> Q) = (R2(P) \<parallel>\<^bsub>R2m'(M)\<^esub> R2(Q))"
  by (pred_auto)
     (metis le_add trace_class.add_diff_cancel_left, blast)

lemma R2m_R2m'_pbm: "(R2(P) \<parallel>\<^bsub>R2m(M)\<^esub> R2(Q)) = (R2(P) \<parallel>\<^bsub>R2m'(M)\<^esub> R2(Q))"
  by (pred_simp, blast)

lemma R2_par_by_merge [closure]:
  assumes "P is R2" "Q is R2" "M is R2m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is R2"
  by (metis Healthy_def' R2_R2m'_pbm R2m_R2m'_pbm assms(1) assms(2) assms(3))

lemma R2_par_by_merge' [closure]:
  assumes "P is R2" "Q is R2" "M is R2m'"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is R2"
  by (metis Healthy_def' R2_R2m'_pbm assms(1) assms(2) assms(3))
  
lemma R1m_skip_merge: "R1m(skip\<^sub>m) = skip\<^sub>m"
  by (pred_auto)

lemma R1m_disj: "R1m(P \<or> Q) = (R1m(P) \<or> R1m(Q))"
  by (pred_auto)

lemma R1m_conj: "R1m(P \<and> Q) = (R1m(P) \<and> R1m(Q))"
  by (pred_auto)

lemma R2m_skip_merge: "R2m(skip\<^sub>m) = skip\<^sub>m"
  apply (pred_auto) using minus_zero_eq by blast

lemma R2m_disj: "R2m(P \<or> Q) = (R2m(P) \<or> R2m(Q))"
  by (pred_auto)

lemma R2m_conj: "R2m(P \<and> Q) = (R2m(P) \<and> R2m(Q))"
  by (pred_auto)

definition R3m :: "('t :: trace, '\<alpha>) rp merge \<Rightarrow> ('t, '\<alpha>) rp merge" where
  [pred]: "R3m(M) = skip\<^sub>m \<triangleleft> $<:wait\<^sup>< \<triangleright> M"

lemma R3_par_by_merge:
  assumes
    "P is R3" "Q is R3" "M is R3m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is R3"
proof -
  have "(P \<parallel>\<^bsub>M\<^esub> Q) = ((P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>True/wait\<^sup><\<rbrakk> \<triangleleft> $wait\<^sup>< \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (metis expr_if_bool_var_left expr_if_idem fst_vwb_lens ns_alpha_vwb wait_vwb_lens)
  also have "... = (((R3 P)\<lbrakk>True/wait\<^sup><\<rbrakk> \<parallel>\<^bsub>(R3m M)\<lbrakk>True/<:wait\<^sup><\<rbrakk>\<^esub> (R3 Q)\<lbrakk>True/wait\<^sup><\<rbrakk>) \<triangleleft> $wait\<^sup>< \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (simp add: usubst Healthy_if assms)
  also have "... = ((II\<lbrakk>True/wait\<^sup><\<rbrakk> \<parallel>\<^bsub>skip\<^sub>m\<lbrakk>True/<:wait\<^sup><\<rbrakk>\<^esub> II\<lbrakk>True/wait\<^sup><\<rbrakk>) \<triangleleft> $wait\<^sup>< \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (simp add: R3_def R3m_def usubst)
  also have "... = ((II \<parallel>\<^bsub>skip\<^sub>m\<^esub> II)\<lbrakk>True/wait\<^sup><\<rbrakk> \<triangleleft> $wait\<^sup>< \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (simp add: usubst)
  also have "... = (II \<triangleleft> $wait\<^sup>< \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (simp add: expr_if_bool_var_left par_by_merge_skip)
  also have "... = R3(P \<parallel>\<^bsub>M\<^esub> Q)"
    by (simp add: R3_def usubst)
  finally show ?thesis
    by (simp add: Healthy_def)
qed

lemma SymMerge_R1_true [closure]:
  "M is SymMerge \<Longrightarrow> M ;; R1(true) is SymMerge"
  by (pred_auto)

end