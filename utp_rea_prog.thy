section \<open> Reactive Programs \<close>

(* NOTE: virtually all of this theory is commented out right now. *)

theory utp_rea_prog
  (* TODO(@MattWindsor91): import utp_rea_cond instead *)
  imports utp_rea_core "Shallow-Expressions.Shallow_Expressions" "Optics.Optics" 
begin

subsection \<open> Stateful reactive alphabet \<close>

text \<open> @{term R3} as presented in the UTP book and related publications is not sensitive to state, 
  although reactive programs often need this property. Thus is is necessary to use a modification 
  of @{term R3} from Butterfield et al.~\cite{BGW09} that explicitly states that intermediate
  waiting states do not propagate final state variables. In order to do this we need an additional
  observational variable that capture the program state that we call $st$. Upon this foundation,
  we can define operators for reactive programs~\cite{Foster17c}. \<close>

alphabet ('t, 's) rsp_vars = "'t::trace rea_vars" +
  st :: 's

(* TODO(@MattWindsor91): do we need the type synonyms and translations? *)

type_synonym ('s,'t,'\<alpha>) rsp = "('t, 's, '\<alpha>) rsp_vars_scheme" \<comment> \<open> Reactive state predicate \<close>
type_synonym ('s,'t,'\<alpha>,'\<beta>) rel_rsp  = "(('s,'t,'\<alpha>) rsp \<leftrightarrow> ('s,'t,'\<beta>) rsp)" \<comment> \<open> Relation on the above \<close>
type_synonym ('s,'t,'\<alpha>) hrel_rsp  = "('s,'t,'\<alpha>,'\<alpha>) rel_rsp" \<comment> \<open> Homogeneous relation on the above \<close>
type_synonym ('s,'t) rdes = "('s,'t,unit) hrel_rsp" \<comment> \<open> Reactive design? \<close>

(* TODO(@MattWindsor91): probably remove or replace with core version *)
type_synonym ('t,'\<alpha>) rp = "('t,'\<alpha>) rea_vars_scheme"
type_synonym ('t,'\<alpha>,'\<beta>) rel_rp  = "(('t,'\<alpha>) rp \<leftrightarrow> ('t,'\<beta>) rp)"

translations
  (type) "('s,'t,'\<alpha>) rsp" <= (type) "('t, ('s, '\<alpha>) rsp_vars_ext) rp"
  (type) "('s,'t,'\<alpha>) rsp" <= (type) "('t, ('s, '\<alpha>) rsp_vars_scheme) rp"
  (type) "('s,'t,unit) rsp" <= (type) "('t, 's rsp_vars) rp"
  (type) "('s,'t,'\<alpha>,'\<beta>) rel_rsp" <= (type) "(('s,'t,'\<alpha>) rsp \<leftrightarrow> ('s1,'t1,'\<beta>) rsp)"
  (type) "('s,'t,'\<alpha>) hrel_rsp"  <= (type) "(('s, 't, '\<alpha>) rsp \<leftrightarrow> ('s1,'t1,'\<alpha>1) rsp)" (* ? *)
  (type) "('s,'t) rdes" <= (type) "('s, 't, unit) hrel_rsp"

text \<open> Shorthand for the alphabet of a stateful reactive program \<close>

notation rsp_vars.more\<^sub>L ("\<Sigma>\<^sub>S")

syntax
  "_svid_st_alpha"  :: "svid" ("\<Sigma>\<^sub>S")

translations
  "_svid_st_alpha" => "CONST rsp_vars.more\<^sub>L"

(* TODO(@MattWindsor91): need \<Sigma>\<^sub>R
lemma rea_lens_equiv_st_rest: "\<Sigma>\<^sub>R \<approx>\<^sub>L st +\<^sub>L \<Sigma>\<^sub>S"
  by simp
*)

(* TODO(@MattWindsor91): need \<Sigma>\<^sub>R
lemma srea_lens_bij: "bij_lens (ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L st +\<^sub>L \<Sigma>\<^sub>S)"
proof -
  have "ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L st +\<^sub>L \<Sigma>\<^sub>S \<approx>\<^sub>L ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L \<Sigma>\<^sub>R"
    by (auto intro!:lens_plus_cong, rule lens_equiv_sym, simp add: rea_lens_equiv_st_rest)
  also have "... \<approx>\<^sub>L 1\<^sub>L"
    using bij_lens_equiv_id[of "ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L \<Sigma>\<^sub>R"] by (simp add: rea_lens_bij)
  finally show ?thesis
    by (simp add: bij_lens_equiv_id)
qed
*)

(* TODO(@MattWindsor91): how to type this?
lemma st_qual_alpha [alpha]: "x ;\<^sub>L fst\<^sub>L ;\<^sub>L st \<times>\<^sub>L st = st:x"
  by (metis (no_types, opaque_lifting) in_var_def in_var_prod_lens lens_comp_assoc st_vwb_lens vwb_lens_wb)
*)

(*
interpretation alphabet_state:
  lens_interp "\<lambda>(ok, wait, tr, r). (ok, wait, tr, st\<^sub>v r, more r)"
  apply (unfold_locales)
  apply (rule injI)
  apply (clarsimp)
  done

interpretation alphabet_state_rel: lens_interp "\<lambda>(ok, ok', wait, wait', tr, tr', r, r').
  (ok, ok', wait, wait', tr, tr', st\<^sub>v r, st\<^sub>v r', more r, more r')"
  apply (unfold_locales)
  apply (rule injI)
  apply (clarsimp)
  done
*)

(* TODO(@MattWindsor91): need RR, RC
lemma unrest_st'_neg_RC [unrest]:
  assumes "P is RR" "P is RC"
  shows "$st\<acute> \<sharp> P"
proof -
  have "P = (\<not>\<^sub>r \<not>\<^sub>r P)"
    by (simp add: closure rpred assms)
  also have "... = (\<not>\<^sub>r (\<not>\<^sub>r P) ;; true\<^sub>r)"
    by (metis Healthy_if RC1_def RC_implies_RC1 assms(2) calculation)
  also have "$st\<acute> \<sharp> ..."
    by (rel_auto)
  finally show ?thesis .
qed
*)

(* TODO(@MattWindsor91): need RR
lemma ex_st'_RR_closed [closure]: 
  assumes "P is RR"
  shows "(\<exists> $st\<acute> \<bullet> P) is RR"
proof -
  have "RR (\<exists> $st\<acute> \<bullet> RR(P)) = (\<exists> $st\<acute> \<bullet> RR(P))"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def assms)
qed
*)

(* TODO(@MattWindsor91): need R4
lemma unrest_st'_R4 [unrest]:
  "$st\<acute> \<sharp> P \<Longrightarrow> $st\<acute> \<sharp> R4(P)"
  by (rel_auto)
*)

(* TODO(@MattWindsor91): need R5
lemma unrest_st'_R5 [unrest]:
  "$st\<acute> \<sharp> P \<Longrightarrow> $st\<acute> \<sharp> R5(P)"
  by (rel_auto)
*)

subsection \<open> State Lifting \<close>

(* TODO(@MattWindsor91): neither of these want to work either; subst overloading problems
definition lift_state_rel :: "('t, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('s, 't, '\<alpha>, '\<beta>) rel_rsp" ("\<lceil>_\<rceil>\<^sub>S")
  where "\<lceil>P\<rceil>\<^sub>S \<equiv> P \<up> (\<Sigma>\<^sub>S\<^sup>2)"

term lift_state_rel

definition drop_state_rel :: "('s, 't, '\<alpha>, '\<beta>) rel_rsp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" ("\<lfloor>_\<rfloor>\<^sub>S")
where "\<lfloor>P\<rfloor>\<^sub>S \<equiv> P \<down> (\<Sigma>\<^sub>S\<^sup>2)"
*)

(* TODO(@MattWindsor91): depends on nonexistent lifting?
abbreviation lift_state_pre ("\<lceil>_\<rceil>\<^sub>S\<^sub><")
where "\<lceil>p\<rceil>\<^sub>S\<^sub>< \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub><\<rceil>\<^sub>S"
*)

(* TODO(@MattWindsor91): depends on nonexistent dropping?
abbreviation drop_state_pre ("\<lfloor>_\<rfloor>\<^sub>S\<^sub><")
where "\<lfloor>p\<rfloor>\<^sub>S\<^sub>< \<equiv> \<lfloor>\<lfloor>p\<rfloor>\<^sub>S\<rfloor>\<^sub><"
*)

(* TODO(@MattWindsor91): depends on nonexistent lifting?
abbreviation lift_state_post ("\<lceil>_\<rceil>\<^sub>S\<^sub>>")
where "\<lceil>p\<rceil>\<^sub>S\<^sub>> \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub>>\<rceil>\<^sub>S"
*)

(* TODO(@MattWindsor91): depends on nonexistent dropping?
abbreviation drop_state_post ("\<lfloor>_\<rfloor>\<^sub>S\<^sub>>")
where "\<lfloor>p\<rfloor>\<^sub>S\<^sub>> \<equiv> \<lfloor>\<lfloor>p\<rfloor>\<^sub>S\<rfloor>\<^sub>>"
*)

(* TODO(@MattWindsor91): depends on above
lemma st_unrest_state_pre [unrest]: "&\<^bold>v \<sharp> s \<Longrightarrow> $st \<sharp> \<lceil>s\<rceil>\<^sub>S\<^sub><"
  by (rel_auto)
*)

(* TODO(@MattWindsor91): depends on above
lemma st'_unrest_st_lift_pred [unrest]:
  "$st\<acute> \<sharp> \<lceil>a\<rceil>\<^sub>S\<^sub><"
  by (pred_auto)
*)

(* TODO(@MattWindsor91): depends on above
lemma out_alpha_unrest_st_lift_pre [unrest]:
  "out\<alpha> \<sharp> \<lceil>a\<rceil>\<^sub>S\<^sub><"
  by (rel_auto)
*)

(*
lemma R1_st'_unrest [unrest]: "$st\<acute> \<sharp> P \<Longrightarrow> $st\<acute> \<sharp> R1(P)"
  by (simp add: R1_def unrest)

lemma R2c_st'_unrest [unrest]: "$st\<acute> \<sharp> P \<Longrightarrow> $st\<acute> \<sharp> R2c(P)"
  by (simp add: R2c_def unrest)

lemma unrest_st_rea_rename [unrest]: 
  "$st \<sharp> P \<Longrightarrow> $st \<sharp> P\<lparr>f\<rparr>\<^sub>r"
  "$st\<acute> \<sharp> P \<Longrightarrow> $st\<acute> \<sharp> P\<lparr>f\<rparr>\<^sub>r" 
  by (rel_blast)+

lemma st_lift_R1_true_right: "\<lceil>b\<rceil>\<^sub>S\<^sub>< ;; R1(true) = \<lceil>b\<rceil>\<^sub>S\<^sub><"
  by (rel_auto)

lemma R2c_lift_state_pre: "R2c(\<lceil>b\<rceil>\<^sub>S\<^sub><) = \<lceil>b\<rceil>\<^sub>S\<^sub><"
  by (rel_auto)
*)

subsection \<open> Reactive Program Operators \<close>

subsubsection \<open> State Substitution \<close>

text \<open> Lifting substitutions on the reactive state \<close>

(* TODO(@MattWindsor91): should this (and the others) be going to [rel], or somewhere else? *)
(* TODO(@MattWindsor91)
definition subst_st_lift ::
  "'s subst \<Rightarrow> (('s,'t::trace,'\<alpha>) rsp \<times> ('s,'t,'\<beta>) rsp) subst"  ("\<lceil>_\<rceil>\<^sub>S\<^sub>\<sigma>") where
[rel]: "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> = \<lceil>\<sigma> \<up> st\<rceil>\<^sub>s"

abbreviation st_subst :: "'s subst \<Rightarrow> ('s,'t::trace,'\<alpha>,'\<beta>) rel_rsp \<Rightarrow> ('s, 't, '\<alpha>, '\<beta>) rel_rsp" (infixr "\<dagger>\<^sub>S" 80) where
"\<sigma> \<dagger>\<^sub>S P \<equiv> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P"

translations
  "\<sigma> \<dagger>\<^sub>S P" <= "\<lceil>\<sigma> \<up> st\<rceil>\<^sub>s \<dagger> P"
  "\<sigma> \<dagger>\<^sub>S P" <= "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P"

lemma st_lift_lemma:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> = \<sigma> \<up> (fst\<^sub>L ;\<^sub>L (st \<times>\<^sub>L st))"
  by (rel_auto)
    
lemma unrest_st_lift [unrest]:
  fixes x :: "'a \<Longrightarrow> ('s, 't::trace, '\<alpha>) rsp \<times> ('s, 't, '\<alpha>) rsp"
  assumes "x \<bowtie> st"
  shows "x \<sharp>\<^sub>s \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma>" (is "?P")
  by (simp add: st_lift_lemma)
     (metis assms in_var_def in_var_prod_lens lens_comp_left_id st_vwb_lens unrest_subst_alpha_ext vwb_lens_wb)

lemma id_st_subst [usubst]: 
  "\<lceil>id\<^sub>s\<rceil>\<^sub>S\<^sub>\<sigma> = id\<^sub>s"
  by (pred_auto)
    
lemma st_subst_comp [usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<circ>\<^sub>s \<lceil>\<rho>\<rceil>\<^sub>S\<^sub>\<sigma> = \<lceil>\<sigma> \<circ>\<^sub>s \<rho>\<rceil>\<^sub>S\<^sub>\<sigma>"
  by (rel_auto)

definition lift_cond_srea ("\<lceil>_\<rceil>\<^sub>S\<^sub>\<leftarrow>") where
[rel]: "\<lceil>b\<rceil>\<^sub>S\<^sub>\<leftarrow> = \<lceil>b\<rceil>\<^sub>S\<^sub><"

lemma unrest_lift_cond_srea [unrest]:
  "x \<sharp> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<Longrightarrow> x \<sharp> \<lceil>b\<rceil>\<^sub>S\<^sub>\<leftarrow>"
  by (simp add: lift_cond_srea_def)

lemma st_subst_RR_closed [closure]:
  assumes "P is RR"
  shows "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P is RR"
proof -
  have "RR(\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> RR(P)) = \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> RR(P)"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma subst_lift_cond_srea [usubst]: "\<sigma> \<dagger>\<^sub>S \<lceil>P\<rceil>\<^sub>S\<^sub>\<leftarrow> = \<lceil>\<sigma> \<dagger> P\<rceil>\<^sub>S\<^sub>\<leftarrow>"
  by (rel_auto)

lemma st_subst_rea_not [usubst]: "\<sigma> \<dagger>\<^sub>S (\<not>\<^sub>r P) = (\<not>\<^sub>r \<sigma> \<dagger>\<^sub>S P)"
  by (rel_auto)

lemma st_subst_seq [usubst]: "\<sigma> \<dagger>\<^sub>S (P ;; Q) = \<sigma> \<dagger>\<^sub>S P ;; Q"
  by (rel_auto)
*)

(* TODO(@MattWindsor91): needs RC
lemma st_subst_RC_closed [closure]:
  assumes "P is RC"
  shows "\<sigma> \<dagger>\<^sub>S P is RC"
  apply (rule RC_intro, simp add: closure assms)
  apply (simp add: st_subst_rea_not[THEN sym] st_subst_seq[THEN sym])
  apply (metis Healthy_if RC1_def RC_implies_RC1 assms)
done
*)

subsubsection \<open> Assignment \<close>

(* TODO(@MattWindsor91)
definition rea_assigns :: "('s subst) \<Rightarrow> ('s, 't::trace, '\<alpha>) hrel_rsp" ("\<langle>_\<rangle>\<^sub>r") where
[rel]: "\<langle>\<sigma>\<rangle>\<^sub>r = (tr\<^sup>< = tr\<^sup>> \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S \<and> \<Sigma>\<^sub>S\<^sup>< = \<Sigma>\<^sub>S\<^sup>>)"

syntax
  "_assign_rea" :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  ("'(_') :=\<^sub>r '(_')")  
  "_assign_rea" :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  (infixr ":=\<^sub>r" 62)

translations
  "_assign_rea xs vs" => "CONST rea_assigns (_mk_usubst (id\<^sub>s) xs vs)"
  "_assign_rea x v" <= "CONST rea_assigns (CONST subst_upd (id\<^sub>s) x v)"
  "_assign_rea x v" <= "_assign_rea (_spvar x) v"
  "x,y :=\<^sub>r u,v" <= "CONST rea_assigns (CONST subst_upd (CONST subst_upd (id\<^sub>s) (CONST pr_var x) u) (CONST pr_var y) v)"
*)

(* TODO(@MattWindsor91): needs RR
lemma rea_assigns_RR_closed [closure]: 
  "\<langle>\<sigma>\<rangle>\<^sub>r is RR"
  apply (rel_auto) using minus_zero_eq by auto
*)

(* TODO(@MattWindsor91)
lemma st_subst_assigns_rea [usubst]:
  "\<sigma> \<dagger>\<^sub>S \<langle>\<rho>\<rangle>\<^sub>r = \<langle>\<rho> \<circ>\<^sub>s \<sigma>\<rangle>\<^sub>r"
  by (rel_auto)
    
lemma st_subst_rea_skip [usubst]:
  "\<sigma> \<dagger>\<^sub>S II\<^sub>r = \<langle>\<sigma>\<rangle>\<^sub>r"
  by (rel_auto)
*)

(* TODO(@MattWindsor91): needs RR
lemma rea_assigns_comp [rpred]:
  assumes "P is RR"
  shows "\<langle>\<sigma>\<rangle>\<^sub>r ;; P = \<sigma> \<dagger>\<^sub>S P"
proof -
  have "\<langle>\<sigma>\<rangle>\<^sub>r ;; (RR P) = \<sigma> \<dagger>\<^sub>S (RR P)"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def assms)
qed
*)

(* TODO(@MattWindsor91)
lemma rea_assigns_rename [rpred]:
  "renamer f \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>r\<lparr>f\<rparr>\<^sub>r = \<langle>\<sigma>\<rangle>\<^sub>r"
  using minus_zero_eq by rel_auto

lemma st_subst_RR [closure]:
  assumes "P is RR"
  shows "(\<sigma> \<dagger>\<^sub>S P) is RR"
proof -
  have "(\<sigma> \<dagger>\<^sub>S RR(P)) is RR"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma rea_assigns_st_subst [usubst]:
  "\<lceil>\<sigma> \<up> st\<rceil>\<^sub>s \<dagger> \<langle>\<rho>\<rangle>\<^sub>r = \<langle>\<rho> \<circ>\<^sub>s \<sigma>\<rangle>\<^sub>r"
  by (rel_auto)
*)

subsubsection \<open> Conditional \<close>

text \<open> We guard the reactive conditional condition so that it can't be simplified by alphabet
  laws unless explicitly simplified. \<close>

(* TODO(@MattWindsor91)
abbreviation cond_srea ::
  "('s,'t::trace,'\<alpha>,'\<beta>) rel_rsp \<Rightarrow>
  's pred \<Rightarrow>
  ('s,'t,'\<alpha>,'\<beta>) rel_rsp \<Rightarrow>
  ('s,'t,'\<alpha>,'\<beta>) rel_rsp" where
"cond_srea P b Q \<equiv> P \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>\<leftarrow> \<triangleright> Q"

syntax
  "_cond_srea" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(3_ \<triangleleft> _ \<triangleright>\<^sub>R/ _)" [52,0,53] 52)

translations
  "_cond_srea P b Q" == "CONST cond_srea P b Q"

lemma st_cond_assigns [rpred]:
  "\<langle>\<sigma>\<rangle>\<^sub>r \<triangleleft> b \<triangleright>\<^sub>R \<langle>\<rho>\<rangle>\<^sub>r = \<langle>\<sigma> \<triangleleft> b \<triangleright> \<rho>\<rangle>\<^sub>r"
  by (rel_auto)

lemma cond_srea_RR_closed [closure]:
  assumes "P is RR" "Q is RR"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q is RR"
proof -
  have "RR(RR(P) \<triangleleft> b \<triangleright>\<^sub>R RR(Q)) = RR(P) \<triangleleft> b \<triangleright>\<^sub>R RR(Q)"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def' assms(1) assms(2))
qed
  
lemma cond_srea_RC1_closed:
  assumes "P is RC1" "Q is RC1"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q is RC1"
proof -
  have "RC1(RC1(P) \<triangleleft> b \<triangleright>\<^sub>R RC1(Q)) = RC1(P) \<triangleleft> b \<triangleright>\<^sub>R RC1(Q)"
    using dual_order.trans by (rel_blast)
  thus ?thesis
    by (metis Healthy_def' assms)
qed

lemma cond_srea_RC_closed [closure]:
  assumes "P is RC" "Q is RC"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q is RC"
  by (rule RC_intro', simp_all add: closure cond_srea_RC1_closed RC_implies_RC1 assms)

lemma R4_cond [rpred]: "R4(P \<triangleleft> b \<triangleright>\<^sub>R Q) = (R4(P) \<triangleleft> b \<triangleright>\<^sub>R R4(Q))"
  by (rel_auto)

lemma R5_cond [rpred]: "R5(P \<triangleleft> b \<triangleright>\<^sub>R Q) = (R5(P) \<triangleleft> b \<triangleright>\<^sub>R R5(Q))"
  by (rel_auto)

lemma rea_rename_cond [rpred]: "(P \<triangleleft> b \<triangleright>\<^sub>R Q)\<lparr>f\<rparr>\<^sub>r = P\<lparr>f\<rparr>\<^sub>r \<triangleleft> b \<triangleright>\<^sub>R Q\<lparr>f\<rparr>\<^sub>r"
  by (rel_auto)
*)

subsubsection \<open> Assumptions \<close>

(* TODO(@MattWindsor91)
definition rea_assume :: "'s pred \<Rightarrow> ('s, 't::trace, '\<alpha>) hrel_rsp" ("[_]\<^sup>\<top>\<^sub>r") where
[rel]: "[b]\<^sup>\<top>\<^sub>r = (II\<^sub>r \<triangleleft> b \<triangleright>\<^sub>R false)"

lemma rea_assume_RR [closure]: "[b]\<^sup>\<top>\<^sub>r is RR"
  by (simp add: rea_assume_def closure)

lemma rea_assume_false [rpred]: "[false]\<^sup>\<top>\<^sub>r = false"
  by (rel_auto)

lemma rea_assume_true [rpred]: "[true]\<^sup>\<top>\<^sub>r = II\<^sub>r"
  by (rel_auto)

lemma rea_assume_comp [rpred]: "[b]\<^sup>\<top>\<^sub>r ;; [c]\<^sup>\<top>\<^sub>r = [b \<and> c]\<^sup>\<top>\<^sub>r"
  by (rel_auto)
*)

subsubsection \<open> State Abstraction \<close>

text \<open> We introduce state abstraction by creating some lens functors that allow us to lift
  a lens on the state-space to one on the whole stateful reactive alphabet. \<close>

definition lmap\<^sub>R :: "('a \<Longrightarrow> 'b) \<Rightarrow> ('t::trace, 'a) rp \<Longrightarrow> ('t, 'b) rp" where
[lens_defs]: "lmap\<^sub>R = lmap[rea_vars]"

text \<open> This construction lens is useful for conversion between a record and its product representation;
  it would be helpful if this could be automatically generated. \<close>

(* TODO(@MattWindsor91): doesn't type correctly
definition rsp_make_lens :: "('\<sigma>, '\<tau>::trace, '\<alpha>) rsp \<Longrightarrow> bool \<times> bool \<times> '\<tau> \<times> '\<sigma> \<times> '\<alpha>" where
[lens_defs]: "rsp_make_lens = \<lparr> lens_get = \<lambda> (ok, wait, tr, st, more). \<lparr> ok\<^sub>v = ok, wait\<^sub>v = wait, tr\<^sub>v = tr, st\<^sub>v = st, \<dots> = more \<rparr>
                              , lens_put = (\<lambda> s v. (ok\<^sub>v v, wait\<^sub>v v, tr\<^sub>v v, st\<^sub>v v, more v)) \<rparr>"

lemma rsp_make_lens_alt: "rsp_make_lens = inv\<^sub>L (ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L st +\<^sub>L rsp_vars.more\<^sub>L)"
  by (auto simp add: lens_defs)

lemma make_lens_bij [simp]: "bij_lens rsp_make_lens"
  by (unfold_locales, simp_all add: lens_defs prod.case_eq_if)
*)

text \<open> The following is an intuitive definition of the @{term st} functorial lens, which
  frames all the state space excluding @{term st}, to which another lens @{term l} is
  applied. We do this by splitting the state space into a product, including the application
  of @{term l} to @{term st}, and then invert the product creation lens to reconstruct
  the reactive state space. \<close>

definition map_st_lens ::
  "('\<sigma> \<Longrightarrow> '\<psi>) \<Rightarrow>
   (('\<sigma>, '\<tau>::trace, '\<alpha>) rsp \<Longrightarrow> ('\<psi>, '\<tau>::trace, '\<alpha>) rsp)" ("map'_st\<^sub>L") where
"map_st_lens l = inv\<^sub>L (ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L st +\<^sub>L rsp_vars.more\<^sub>L) ;\<^sub>L 
                 (ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L (l ;\<^sub>L st) +\<^sub>L rsp_vars.more\<^sub>L)"

text \<open> The above definition is intuitive, but unhelpful in proof automaton. Consequently,
  we the following optimised definition below. \<close>

lemma map_st_lens_alt_def [lens_defs]:
  "map_st_lens l = \<lparr> lens_get = \<lambda> s. \<lparr> ok\<^sub>v = ok\<^sub>v s, wait\<^sub>v = wait\<^sub>v s, tr\<^sub>v = tr\<^sub>v s, st\<^sub>v = get\<^bsub>l\<^esub> (st\<^sub>v s), \<dots> = more s \<rparr>
                  , lens_put = \<lambda> s v. \<lparr> ok\<^sub>v = ok\<^sub>v v, wait\<^sub>v = wait\<^sub>v v, tr\<^sub>v = tr\<^sub>v v, st\<^sub>v = put\<^bsub>l\<^esub> (st\<^sub>v s) (st\<^sub>v v), \<dots> = more v \<rparr> \<rparr>"
  by (auto simp add: map_st_lens_def lens_defs fun_eq_iff)

(* TODO(@MattWindsor91): missing def
lemma map_st_vwb [simp]: "vwb_lens X \<Longrightarrow> vwb_lens (map_st\<^sub>L X)"
  by (simp add: map_st_lens_def rsp_make_lens_alt[THEN sym])
*)

lemma map_st_lens_indep_st [simp]: 
  "a \<bowtie> x \<Longrightarrow> map_st\<^sub>L a \<bowtie> x ;\<^sub>L st"
  by (rule lens_indep.intro, simp_all add: lens_defs lens_indep_comm lens_indep.lens_put_irr2)

lemma map_st_lens_indep_st' [simp]: 
  "x \<bowtie> a \<Longrightarrow> map_st\<^sub>L a \<bowtie> x ;\<^sub>L st"
  by (rule lens_indep.intro, simp_all add: lens_defs lens_indep_comm lens_indep.lens_put_irr2)

syntax
  "_map_st_lens" :: "logic \<Rightarrow> salpha" ("map'_st\<^sub>L[_]")

translations
  "_map_st_lens a" => "CONST map_st_lens a"

abbreviation "abs_st\<^sub>L \<equiv> (map_st\<^sub>L 0\<^sub>L) \<times>\<^sub>L (map_st\<^sub>L 0\<^sub>L)"

(* TODO(@MattWindsor91): abbreviation being dropped
abbreviation abs_st ("\<langle>_\<rangle>\<^sub>S") where
"abs_st P \<equiv> P \<down> abs_st\<^sub>L"
*)

(* TODO(@MattWindsor91)
lemma rea_impl_aext_st [alpha]:
  "(P \<Rightarrow>\<^sub>r Q) \<oplus>\<^sub>r map_st\<^sub>L[a] = (P \<oplus>\<^sub>r map_st\<^sub>L[a] \<Rightarrow>\<^sub>r Q \<oplus>\<^sub>r map_st\<^sub>L[a])"
  by (rel_auto)

lemma rea_true_ext_st [alpha]: 
  "true\<^sub>r \<up> abs_st\<^sub>L = true\<^sub>r"
  by (rel_auto)
*)

subsubsection \<open> Reactive Frames and Extensions \<close>

(* TODO(@MattWindsor91)
definition rea_frame :: "('\<alpha> \<Longrightarrow> '\<beta>) \<Rightarrow> ('\<beta>, 't::trace, 'r) hrel_rsp \<Rightarrow> ('\<beta>, 't, 'r) hrel_rsp" where
[rel]: "rea_frame x P = frame (ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L (x ;\<^sub>L st) +\<^sub>L \<Sigma>\<^sub>S) P"

definition rea_frame_ext :: "('\<alpha> \<Longrightarrow> '\<beta>) \<Rightarrow> ('\<alpha>, 't::trace, 'r) hrel_rsp \<Rightarrow> ('\<beta>, 't, 'r) hrel_rsp" where
[rel]: "rea_frame_ext a P = rea_frame a (P \<oplus>\<^sub>r map_st\<^sub>L[a])"

syntax
  "_rea_frame"     :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]\<^sub>r" [99,0] 100)
  "_rea_frame_ext" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]\<^sub>r\<^sup>+" [99,0] 100)

translations
  "_rea_frame x P" => "CONST rea_frame x P"
  "_rea_frame (_salphaset (_salphamk x)) P" <= "CONST rea_frame x P"
  "_rea_frame_ext x P" => "CONST rea_frame_ext x P"
  "_rea_frame_ext (_salphaset (_salphamk x)) P" <= "CONST rea_frame_ext x P"

lemma rea_frame_R1_closed [closure]: 
  assumes "P is R1"
  shows "x:[P]\<^sub>r is R1"
proof -
  have "R1(x:[R1 P]\<^sub>r) = x:[R1 P]\<^sub>r"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_if Healthy_intro assms)
qed

lemma rea_frame_R2_closed [closure]: 
  assumes "P is R2"
  shows "x:[P]\<^sub>r is R2"
proof -
  have "R2(x:[R2 P]\<^sub>r) = x:[R2 P]\<^sub>r"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_if Healthy_intro assms)
qed

lemma rea_frame_RR_closed [closure]: 
  assumes "P is RR"
  shows "x:[P]\<^sub>r is RR"
proof -
  have "RR(x:[RR P]\<^sub>r) = x:[RR P]\<^sub>r"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_if Healthy_intro assms)
qed

lemma rea_aext_R1 [closure]:
  assumes "P is R1"
  shows "rel_aext P (map_st\<^sub>L x) is R1"
proof -
  have "rel_aext (R1 P) (map_st\<^sub>L x) is R1"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma rea_aext_R2 [closure]:
  assumes "P is R2"
  shows "rel_aext P (map_st\<^sub>L x) is R2"
proof -
  have "rel_aext (R2 P) (map_st\<^sub>L x) is R2"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma rea_aext_RR [closure]:
  assumes "P is RR"
  shows "rel_aext P (map_st\<^sub>L x) is RR"
proof -
  have "rel_aext (RR P) (map_st\<^sub>L x) is RR"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma true_rea_map_st [alpha]: "(R1 true \<oplus>\<^sub>r map_st\<^sub>L[a]) = R1 true"
  by (rel_auto)

lemma rea_frame_ext_R1_closed [closure]:
  "P is R1 \<Longrightarrow> x:[P]\<^sub>r\<^sup>+ is R1"
  by (simp add: rea_frame_ext_def closure)

lemma rea_frame_ext_R2_closed [closure]:
  "P is R2 \<Longrightarrow> x:[P]\<^sub>r\<^sup>+ is R2"
  by (simp add: rea_frame_ext_def closure)

lemma rea_frame_ext_RR_closed [closure]:
  "P is RR \<Longrightarrow> x:[P]\<^sub>r\<^sup>+ is RR"
  by (simp add: rea_frame_ext_def closure)

lemma rel_aext_st_Instant_closed [closure]:
  "P is Instant \<Longrightarrow> rel_aext P (map_st\<^sub>L x) is Instant"
  by (rel_auto)

lemma rea_frame_ext_false [frame]:
  "x:[false]\<^sub>r\<^sup>+ = false"
  by (rel_auto)
  
lemma rea_frame_ext_skip [frame]:
  "vwb_lens x \<Longrightarrow> x:[II\<^sub>r]\<^sub>r\<^sup>+ = II\<^sub>r"
  by (rel_auto)

lemma rea_frame_ext_assigns [frame]:
  "vwb_lens x \<Longrightarrow> x:[\<langle>\<sigma>\<rangle>\<^sub>r]\<^sub>r\<^sup>+ = \<langle>\<sigma> \<up> x\<rangle>\<^sub>r"
  by (rel_auto)

lemma rea_frame_ext_cond [frame]:
  "x:[P \<triangleleft> b \<triangleright>\<^sub>R Q]\<^sub>r\<^sup>+ = x:[P]\<^sub>r\<^sup>+ \<triangleleft> (b \<oplus>\<^sub>p x) \<triangleright>\<^sub>R x:[Q]\<^sub>r\<^sup>+"
  by (rel_auto)
    
lemma rea_frame_ext_seq [frame]:
  "vwb_lens x \<Longrightarrow> x:[P ;; Q]\<^sub>r\<^sup>+ = x:[P]\<^sub>r\<^sup>+ ;; x:[Q]\<^sub>r\<^sup>+"
  apply (simp add: rea_frame_ext_def rea_frame_def alpha frame)
  apply (subst frame_seq)
     apply (simp_all add: plus_vwb_lens closure)
   apply (rel_auto)+
  done

lemma rea_frame_ext_subst_indep [usubst]:
  assumes "x \<bowtie> y" "\<Sigma> \<sharp> v" "P is RR"
  shows "\<sigma>(y \<mapsto>\<^sub>s v) \<dagger>\<^sub>S x:[P]\<^sub>r\<^sup>+ = (\<sigma> \<dagger>\<^sub>S x:[P]\<^sub>r\<^sup>+) ;; y :=\<^sub>r v"
proof -
  from assms(1-2) have "\<sigma>(y \<mapsto>\<^sub>s v) \<dagger>\<^sub>S x:[RR P]\<^sub>r\<^sup>+ = (\<sigma> \<dagger>\<^sub>S x:[RR P]\<^sub>r\<^sup>+) ;; y :=\<^sub>r v"
    by (rel_auto, (metis (no_types, lifting) lens_indep.lens_put_comm lens_indep_get)+)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma rea_frame_ext_subst_within [usubst]:
  assumes "vwb_lens x" "vwb_lens y" "\<Sigma> \<sharp> v" "P is RR"
  shows "\<sigma>(x:y \<mapsto>\<^sub>s v) \<dagger>\<^sub>S x:[P]\<^sub>r\<^sup>+ = (\<sigma> \<dagger>\<^sub>S x:[y :=\<^sub>r (v \<restriction>\<^sub>e x) ;; P]\<^sub>r\<^sup>+)"
proof -
  from assms(1,3) have "\<sigma>(x:y \<mapsto>\<^sub>s v) \<dagger>\<^sub>S x:[RR P]\<^sub>r\<^sup>+ = (\<sigma> \<dagger>\<^sub>S x:[y :=\<^sub>r (v \<restriction>\<^sub>e x) ;; RR(P)]\<^sub>r\<^sup>+)"
    by (rel_auto, metis+)
  thus ?thesis
    by (simp add: assms Healthy_if)
qed

lemma rea_frame_ext_UINF_ind [frame]:
  "a:[\<Sqinter> x \<bullet> P x]\<^sub>r\<^sup>+ = (\<Sqinter> x \<bullet> a:[P x]\<^sub>r\<^sup>+)"
  by (rel_auto)

lemma rea_frame_ext_UINF_mem [frame]: 
  "a:[\<Sqinter> x\<in>A \<bullet> P x]\<^sub>r\<^sup>+ = (\<Sqinter> x\<in>A \<bullet> a:[P x]\<^sub>r\<^sup>+)"
  by (rel_auto)
*)

subsection \<open> Stateful Reactive specifications \<close>

(* TODO(@MattWindsor91)
definition rea_st_rel :: "'s hrel \<Rightarrow> ('s, 't::trace, '\<alpha>, '\<beta>) rel_rsp" ("[_]\<^sub>S") where
[rel]: "rea_st_rel b = (\<lceil>b\<rceil>\<^sub>S \<and> $tr\<acute> =\<^sub>u $tr)"

definition rea_st_rel' :: "'s hrel \<Rightarrow> ('s, 't::trace, '\<alpha>, '\<beta>) rel_rsp" ("[_]\<^sub>S''") where
[rel]: "rea_st_rel' b = R1(\<lceil>b\<rceil>\<^sub>S)"

definition rea_st_cond :: "'s upred \<Rightarrow> ('s, 't::trace, '\<alpha>, '\<beta>) rel_rsp" ("[_]\<^sub>S\<^sub><") where
[rel]: "rea_st_cond b = R1(\<lceil>b\<rceil>\<^sub>S\<^sub><)"

definition rea_st_post :: "'s upred \<Rightarrow> ('s, 't::trace, '\<alpha>, '\<beta>) rel_rsp" ("[_]\<^sub>S\<^sub>>") where
[rel]: "rea_st_post b = R1(\<lceil>b\<rceil>\<^sub>S\<^sub>>)"

lemma lift_state_pre_unrest [unrest]: "x \<bowtie> ($st)\<^sub>v \<Longrightarrow> x \<sharp> \<lceil>P\<rceil>\<^sub>S\<^sub><"
  by (rel_simp, simp add: lens_indep_def)

lemma rea_st_rel_unrest [unrest]:
  "\<lbrakk> x \<bowtie> ($tr)\<^sub>v; x \<bowtie> ($tr\<acute>)\<^sub>v; x \<bowtie> ($st)\<^sub>v; x \<bowtie> ($st\<acute>)\<^sub>v \<rbrakk> \<Longrightarrow> x \<sharp> [P]\<^sub>S\<^sub><"
  by (simp add: add: rea_st_cond_def R1_def unrest lens_indep_sym)
    
lemma rea_st_cond_unrest [unrest]:
  "\<lbrakk> x \<bowtie> ($tr)\<^sub>v; x \<bowtie> ($tr\<acute>)\<^sub>v; x \<bowtie> ($st)\<^sub>v \<rbrakk> \<Longrightarrow> x \<sharp> [P]\<^sub>S\<^sub><"
  by (simp add: add: rea_st_cond_def R1_def unrest lens_indep_sym)
  
lemma subst_st_cond [usubst]: "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> [P]\<^sub>S\<^sub>< = [\<sigma> \<dagger> P]\<^sub>S\<^sub><"
  by (rel_auto)
    
lemma rea_st_cond_R1 [closure]: "[b]\<^sub>S\<^sub>< is R1"
  by (rel_auto)

lemma rea_st_cond_R2c [closure]: "[b]\<^sub>S\<^sub>< is R2c"
  by (rel_auto)

lemma rea_st_rel_RR [closure]: "[P]\<^sub>S is RR"
  using minus_zero_eq by (rel_auto)

lemma rea_st_rel'_RR [closure]: "[P]\<^sub>S' is RR"
  by (rel_auto)

lemma rea_st_post_RR [closure]: "[b]\<^sub>S\<^sub>> is RR"
  by (rel_auto)

lemma st_subst_rel [usubst]:
  "\<sigma> \<dagger>\<^sub>S [P]\<^sub>S = [\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> P]\<^sub>S"
  by (rel_auto)
    
lemma st_rel_cond [rpred]:
  "[P \<triangleleft> b \<triangleright>\<^sub>r Q]\<^sub>S = [P]\<^sub>S \<triangleleft> b \<triangleright>\<^sub>R [Q]\<^sub>S"
  by (rel_auto)
   
lemma st_rel_false [rpred]: "[false]\<^sub>S = false"
  by (rel_auto)
    
lemma st_rel_skip [rpred]: 
  "[II]\<^sub>S = (II\<^sub>r :: ('s, 't::trace) rdes)"
  by (rel_auto)
    
lemma st_rel_seq [rpred]:
  "[P ;; Q]\<^sub>S = [P]\<^sub>S ;; [Q]\<^sub>S"
  by (rel_auto)
  
lemma st_rel_conj [rpred]:
  "([P]\<^sub>S \<and> [Q]\<^sub>S) = [P \<and> Q]\<^sub>S"
   by (rel_auto)

lemma st_cond_disj [rpred]: 
  "([P]\<^sub>S\<^sub>< \<or> [Q]\<^sub>S\<^sub><) = [P \<or> Q]\<^sub>S\<^sub><"
  by (rel_auto)

lemma rea_st_cond_RR [closure]: "[b]\<^sub>S\<^sub>< is RR"
  by (rule RR_intro, simp_all add: unrest closure)

lemma rea_st_cond_RC [closure]: "[b]\<^sub>S\<^sub>< is RC"
  by (rule RC_intro, simp add: closure, rel_auto)
    
lemma rea_st_cond_true [rpred]: "[true]\<^sub>S\<^sub>< = true\<^sub>r"
  by (rel_auto)

lemma rea_st_cond_false [rpred]: "[false]\<^sub>S\<^sub>< = false"
  by (rel_auto)
    
lemma st_cond_not [rpred]: "(\<not>\<^sub>r [P]\<^sub>S\<^sub><) = [\<not> P]\<^sub>S\<^sub><"
  by (rel_auto)

lemma st_cond_conj [rpred]: "([P]\<^sub>S\<^sub>< \<and> [Q]\<^sub>S\<^sub><) = [P \<and> Q]\<^sub>S\<^sub><"
  by (rel_auto)
    
lemma st_rel_assigns [rpred]:
  "[\<langle>\<sigma>\<rangle>\<^sub>a]\<^sub>S = (\<langle>\<sigma>\<rangle>\<^sub>r :: ('\<alpha>, 't::trace) rdes)"
  by (rel_auto)
        
lemma cond_st_distr: "(P \<triangleleft> b \<triangleright>\<^sub>R Q) ;; R = (P ;; R \<triangleleft> b \<triangleright>\<^sub>R Q ;; R)"
  by (rel_auto)
        
lemma cond_st_miracle [rpred]: "P is R1 \<Longrightarrow> P \<triangleleft> b \<triangleright>\<^sub>R false = ([b]\<^sub>S\<^sub>< \<and> P)"
  by (rel_blast)

lemma cond_st_true [rpred]: "P \<triangleleft> true \<triangleright>\<^sub>R Q = P"
  by (rel_blast)
    
lemma cond_st_false [rpred]: "P \<triangleleft> false \<triangleright>\<^sub>R Q = Q"
  by (rel_blast)
    
lemma st_cond_true_or [rpred]: "P is R1 \<Longrightarrow> (R1 true \<triangleleft> b \<triangleright>\<^sub>R P) = ([b]\<^sub>S\<^sub>< \<or> P)"
  by (rel_blast)
    
lemma st_cond_left_impl_RC_closed [closure]:
  "P is RC \<Longrightarrow> ([b]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P) is RC"
  by (simp add: rea_impl_def rpred closure)
*)
end