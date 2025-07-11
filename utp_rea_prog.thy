section \<open> Reactive Programs \<close>

theory utp_rea_prog
  imports utp_rea_cond
begin

subsection \<open> Stateful reactive alphabet \<close>

text \<open> @{term R3} as presented in the UTP book and related publications is not sensitive to state, 
  although reactive programs often need this property. Thus is is necessary to use a modification 
  of @{term R3} from Butterfield et al.~\cite{BGW09} that explicitly states that intermediate
  waiting states do not propagate final state variables. In order to do this we need an additional
  observational variable that capture the program state that we call $st$. Upon this foundation,
  we can define operators for reactive programs~\cite{Foster17c}. \<close>

alphabet ('t, 's) srea_vars = "'t::trace rea_vars" +
  st :: 's

type_synonym ('s,'t,'\<alpha>) rsp = "('t, 's, '\<alpha>) srea_vars_scheme" \<comment> \<open> Reactive state predicate \<close>
type_synonym ('s,'t,'\<alpha>,'\<beta>) rsp_rel  = "(('s,'t,'\<alpha>) rsp, ('s,'t,'\<beta>) rsp) urel" \<comment> \<open> Relation on the above \<close>
type_synonym ('s,'t,'\<alpha>) rsp_hrel  = "('s,'t,'\<alpha>,'\<alpha>) rsp_rel" \<comment> \<open> Homogeneous relation on the above \<close>
type_synonym ('s,'t) rdes = "('s,'t,unit) rsp_hrel" \<comment> \<open> Reactive design? \<close>

translations
  (type) "('s,'t,'\<alpha>) rsp" <= (type) "('t, ('s, '\<alpha>) srea_vars_ext) rp"
  (type) "('s,'t,'\<alpha>) rsp" <= (type) "('t, ('s, '\<alpha>) srea_vars_scheme) rp"
  (type) "('s,'t,unit) rsp" <= (type) "('t, 's srea_vars) rp"
  (type) "('s,'t,'\<alpha>,'\<beta>) rsp_rel" <= (type) "(('s,'t,'\<alpha>) rsp, ('s1,'t1,'\<beta>) rsp) urel"
  (type) "('s,'t,'\<alpha>) rsp_hrel"  <= (type) "(('s, 't, '\<alpha>) rsp, ('s1,'t1,'\<alpha>1) rsp) urel" (* ? *)
  (type) "('s,'t) rdes" <= (type) "('s, 't, unit) rsp_hrel"

text \<open> Shorthand for the non-control alphabet of a stateful reactive process. \<close>

notation srea_vars.more\<^sub>L ("\<^bold>v\<^sub>S")

syntax
  "_svid_srea_alpha"  :: "svid" ("\<^bold>v\<^sub>S")

translations
  "_svid_srea_alpha" => "CONST srea_vars.more\<^sub>L"

text \<open> As a stateful reactive process adds 'st' to the alphabet of a reactive process, we can
  consider the continuation of its reactive alphabet as the sum of 'st' and the continuation of the
stateful reactive alphabet. \<close>
lemma rea_lens_equiv_st_rest: "\<^bold>v\<^sub>R \<approx>\<^sub>L st +\<^sub>L \<^bold>v\<^sub>S"
  by simp

text \<open> Pairing the reactive stateful alphabet with its control variables forms a bijective lens. \<close>
lemma srea_lens_bij: "bij_lens (ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L st +\<^sub>L \<^bold>v\<^sub>S)"
proof -
  have "ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L st +\<^sub>L \<^bold>v\<^sub>S \<approx>\<^sub>L ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L \<^bold>v\<^sub>R"
    by (auto intro!:lens_plus_cong, rule lens_equiv_sym, simp add: rea_lens_equiv_st_rest)
  also have "... \<approx>\<^sub>L 1\<^sub>L"
    using bij_lens_equiv_id[of "ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L \<^bold>v\<^sub>R"]
      by (simp add: rea_lens_bij)
  finally show ?thesis
    by (simp add: bij_lens_equiv_id)
qed

lemma st_qual_alpha [alpha]: "x ;\<^sub>L fst\<^sub>L ;\<^sub>L st \<times>\<^sub>L st = ((st\<^sup><):x)\<^sub>v"
proof -
  have "x ;\<^sub>L fst\<^sub>L ;\<^sub>L st \<times>\<^sub>L st = x ;\<^sub>L fst\<^sub>L ;\<^sub>L (st ;\<^sub>L fst\<^sub>L +\<^sub>L st ;\<^sub>L snd\<^sub>L)"
    by (simp add: prod_as_plus)
  also have "\<dots> =  x ;\<^sub>L (fst\<^sub>L ;\<^sub>L (st ;\<^sub>L fst\<^sub>L +\<^sub>L st ;\<^sub>L snd\<^sub>L))" by (simp add: lens_comp_assoc)
  also have "\<dots> = x ;\<^sub>L (st ;\<^sub>L fst\<^sub>L)" by (simp add: comp_wb_lens fst_lens_plus)
  also have "\<dots> = ((st\<^sup><):x)\<^sub>v" by (simp add: ns_alpha_def) 
  finally show ?thesis .
qed

lemma unrest_st'_neg_RC [unrest]:
  assumes "P is RR" "P is RC"
  shows "$st\<^sup>> \<sharp> P"
proof -
  have "P = (\<not>\<^sub>r (\<not>\<^sub>r P))"
    by (simp add: closure rpred assms)
  also have "... = (\<not>\<^sub>r (\<not>\<^sub>r P) ;; true\<^sub>r)"
    by (metis Healthy_if RC1_def RC_implies_RC1 assms(2) calculation)
  finally have "P = ..." .
  moreover have "$st\<^sup>> \<sharp> ..."
    by pred_auto
  ultimately show "$st\<^sup>> \<sharp> P"
    by simp
qed

lemma ex_st'_RR_closed [closure]: 
  assumes "P is RR"
  shows "(\<Sqinter> s. P\<lbrakk>\<guillemotleft>s\<guillemotright>/st\<^sup>>\<rbrakk>) is RR"
proof -
  have 1: "$ok\<^sup>< \<sharp> P" "$ok\<^sup>> \<sharp> P" "$wait\<^sup>< \<sharp> P" "$wait\<^sup>> \<sharp> P"
    using assms RR_unrests by blast+
  have 2: "$ok\<^sup>< \<sharp> (\<Sqinter> s. P\<lbrakk>\<guillemotleft>s\<guillemotright>/st\<^sup>>\<rbrakk>)" "$ok\<^sup>> \<sharp> (\<Sqinter> s. P\<lbrakk>\<guillemotleft>s\<guillemotright>/st\<^sup>>\<rbrakk>)" "$wait\<^sup>< \<sharp> (\<Sqinter> s. P\<lbrakk>\<guillemotleft>s\<guillemotright>/st\<^sup>>\<rbrakk>)" "$wait\<^sup>> \<sharp> (\<Sqinter> s. P\<lbrakk>\<guillemotleft>s\<guillemotright>/st\<^sup>>\<rbrakk>)"
    by (simp_all add: unrest 1)
  have 3: "P = R2(P)"
    by (simp add: assms Healthy_if RR_implies_R2)
  have 4: "(\<Sqinter> s. P\<lbrakk>\<guillemotleft>s\<guillemotright>/st\<^sup>>\<rbrakk>) is R2"
    by (subst 3; pred_auto)
  from 2 4 show ?thesis
    using RR_R2_intro by blast
qed

lemma unrest_st'_R4 [unrest]:
  "$st\<^sup>> \<sharp> P \<Longrightarrow> $st\<^sup>> \<sharp> R4(P)"
  by pred_auto

lemma unrest_st'_R5 [unrest]:
  "$st\<^sup>> \<sharp> P \<Longrightarrow> $st\<^sup>> \<sharp> R5(P)"
  by pred_auto

subsection \<open> State Lifting \<close>

abbreviation lift_state_rel ("\<lceil>_\<rceil>\<^sub>S") where "\<lceil>P\<rceil>\<^sub>S \<equiv> P \<up> st\<^sup>2"

abbreviation drop_state_rel ("\<lfloor>_\<rfloor>\<^sub>S") where "\<lfloor>P\<rfloor>\<^sub>S \<equiv> P \<down> (\<^bold>v\<^sub>S\<^sup>2)"

syntax "_lift_state_pre" :: "logic \<Rightarrow> logic" ("\<lceil>_\<rceil>\<^sub>S\<^sub><")
translations "_lift_state_pre e" == "\<lceil>(e\<^sup><)\<^sub>e\<rceil>\<^sub>S"

abbreviation drop_state_pre ("\<lfloor>_\<rfloor>\<^sub>S\<^sub><") where "\<lfloor>p\<rfloor>\<^sub>S\<^sub>< \<equiv> (\<lfloor>p\<rfloor>\<^sub>S)\<^sub><"

abbreviation lift_state_post ("\<lceil>_\<rceil>\<^sub>S\<^sub>>") where "\<lceil>p\<rceil>\<^sub>S\<^sub>> \<equiv> \<lceil>p\<^sup>>\<rceil>\<^sub>S"

abbreviation drop_state_post ("\<lfloor>_\<rfloor>\<^sub>S\<^sub>>") where "\<lfloor>p\<rfloor>\<^sub>S\<^sub>> \<equiv> (\<lfloor>p\<rfloor>\<^sub>S)\<^sub>>"

expr_constructor lift_state_rel
expr_constructor drop_state_rel
expr_constructor drop_state_pre
expr_constructor lift_state_post
expr_constructor drop_state_post

lemma st_unrest_state_pre [unrest]: "(unrest \<top>\<^sub>S s) \<Longrightarrow> $st\<^sup>< \<sharp> \<lceil>s\<rceil>\<^sub>S\<^sub><"
  by pred_auto

lemma st'_unrest_st_lift_pred [unrest]:
  "$st\<^sup>> \<sharp> \<lceil>a\<rceil>\<^sub>S\<^sub><"
  by pred_auto

lemma out_alpha_unrest_st_lift_pre [unrest]:
  "out\<alpha> \<sharp> \<lceil>a\<rceil>\<^sub>S\<^sub><"
  by pred_auto

lemma R1_st'_unrest [unrest]: "$st\<^sup>> \<sharp> P \<Longrightarrow> $st\<^sup>> \<sharp> R1(P)"
  by pred_auto

lemma R2c_st'_unrest [unrest]: "$st\<^sup>> \<sharp> P \<Longrightarrow> $st\<^sup>> \<sharp> R2c(P)"
  by pred_auto

lemma unrest_st_rea_rename [unrest]: 
  "$st\<^sup>< \<sharp> P \<Longrightarrow> $st\<^sup>< \<sharp> P\<lparr>f\<rparr>\<^sub>r"
  "$st\<^sup>> \<sharp> P \<Longrightarrow> $st\<^sup>> \<sharp> P\<lparr>f\<rparr>\<^sub>r" 
  by (pred_auto, blast)+

lemma st_lift_R1_true_right: "(\<lceil>b\<rceil>\<^sub>S\<^sub>< ;; R1(true)) = \<lceil>b\<rceil>\<^sub>S\<^sub><"
  by pred_auto

lemma R2c_lift_state_pre: "R2c(\<lceil>b\<rceil>\<^sub>S\<^sub><) = \<lceil>b\<rceil>\<^sub>S\<^sub><"
  by pred_auto

subsection \<open> Reactive Program Operators \<close>

subsubsection \<open> State Substitution \<close>

text \<open> The following two functions lift a predicate substitution to a relational one. \<close>

abbreviation usubst_rel_lift :: "'\<alpha> subst \<Rightarrow> ('\<alpha> \<times> '\<beta>) subst" ("\<lceil>_\<rceil>\<^sub>s") where
"\<lceil>\<sigma>\<rceil>\<^sub>s \<equiv> subst_aext \<sigma> fst\<^sub>L"

abbreviation usubst_rel_drop :: "('\<alpha> \<times> '\<alpha>) subst \<Rightarrow> '\<alpha> subst" ("\<lfloor>_\<rfloor>\<^sub>s") where
"\<lfloor>\<sigma>\<rfloor>\<^sub>s \<equiv> subst_ares \<sigma> fst\<^sub>L"

definition subst_st_lift :: "'s subst \<Rightarrow> (('s,'t::trace,'\<alpha>) rsp \<times> ('s,'t,'\<beta>) rsp) subst" ("\<lceil>_\<rceil>\<^sub>S\<^sub>\<sigma>") where
[pred]: "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> = \<lceil>\<sigma> \<up>\<^sub>s st\<rceil>\<^sub>s"

expr_constructor usubst_rel_lift
expr_constructor usubst_rel_drop
expr_constructor subst_st_lift

abbreviation st_subst :: "'s subst \<Rightarrow> ('s,'t::trace,'\<alpha>,'\<beta>) rsp_rel \<Rightarrow> ('s, 't, '\<alpha>, '\<beta>) rsp_rel" (infixr "\<dagger>\<^sub>S" 80) where
"\<sigma> \<dagger>\<^sub>S P \<equiv> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P"

translations
  "\<sigma> \<dagger>\<^sub>S P" <= "\<lceil>\<sigma> \<up> st\<rceil>\<^sub>S \<dagger> P"
  "\<sigma> \<dagger>\<^sub>S P" <= "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P"

expr_constructor st_subst

lemma st_lift_lemma:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> = (subst_aext \<sigma> (fst\<^sub>L ;\<^sub>L (st \<times>\<^sub>L st)))"
  by pred_auto

lemma unrest_st_lift [unrest]:
  assumes "x \<bowtie> (st\<^sup><)\<^sub>v"
  shows "$x \<sharp>\<^sub>s \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma>"
  by (simp add: subst_st_lift_def unrest alpha usubst assms)

lemma id_st_subst [usubst]: 
  "\<lceil>[\<leadsto>]\<rceil>\<^sub>S\<^sub>\<sigma> = [\<leadsto>]"
  by pred_auto

lemma st_subst_comp [usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<circ>\<^sub>s \<lceil>\<rho>\<rceil>\<^sub>S\<^sub>\<sigma> = \<lceil>\<sigma> \<circ>\<^sub>s \<rho>\<rceil>\<^sub>S\<^sub>\<sigma>"
  by pred_auto

definition lift_cond_srea  where
[pred]: "lift_cond_srea b = \<lceil>b\<rceil>\<^sub>S\<^sub><"

expr_constructor lift_cond_srea

syntax "_lift_cond_srea" :: "logic \<Rightarrow> logic" ("\<lceil>_\<rceil>\<^sub>S\<^sub>\<leftarrow>")
translations "\<lceil>e\<rceil>\<^sub>S\<^sub>\<leftarrow>" == "CONST lift_cond_srea (e)\<^sub>e"

lemma unrest_lift_cond_srea [unrest]:
  "x \<sharp> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<Longrightarrow> x \<sharp> \<lceil>b\<rceil>\<^sub>S\<^sub>\<leftarrow>"
  by (simp add: lift_cond_srea_def)

lemma st_subst_RR_closed [closure]:
  assumes "P is RR"
  shows "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P is RR"
proof -
  have "RR(\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> RR(P)) = \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> RR(P)"
    by pred_auto
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma subst_lift_cond_srea [usubst]: "\<sigma> \<dagger>\<^sub>S \<lceil>P\<rceil>\<^sub>S\<^sub>\<leftarrow> = \<lceil>\<sigma> \<dagger> P\<rceil>\<^sub>S\<^sub>\<leftarrow>"
  by pred_auto

lemma st_subst_rea_not [usubst]: "\<sigma> \<dagger>\<^sub>S (\<not>\<^sub>r P) = (\<not>\<^sub>r \<sigma> \<dagger>\<^sub>S P)"
  by pred_auto

lemma st_subst_seq [usubst]: "\<sigma> \<dagger>\<^sub>S (P ;; Q) = \<sigma> \<dagger>\<^sub>S P ;; Q"
  by pred_auto

lemma st_subst_RC_closed [closure]:
  assumes "P is RC"
  shows "\<sigma> \<dagger>\<^sub>S P is RC"
  apply (rule RC_intro, simp add: closure assms)
  apply (simp add: st_subst_rea_not[THEN sym] st_subst_seq[THEN sym])
  apply (metis Healthy_if RC1_def RC_implies_RC1 assms)
  done

subsubsection \<open> Assignment \<close>

text \<open> An assignment in the stateful reactive \<close>

definition rea_assigns :: "(('s, 's) psubst) \<Rightarrow> ('s, 't::trace, '\<alpha>) rsp_hrel" ("\<langle>_\<rangle>\<^sub>r") where
[pred]: "\<langle>\<sigma>\<rangle>\<^sub>r = ((tr\<^sup>< = tr\<^sup>>)\<^sub>e \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S \<and> (\<^bold>v\<^sub>S\<^sup>< = \<^bold>v\<^sub>S\<^sup>>)\<^sub>e)"

expr_constructor rea_assigns

syntax
  "_rea_assign" :: "svid \<Rightarrow> logic \<Rightarrow> logic" (infix ":=\<^sub>r" 61)

translations
  "_rea_assign x e" == "CONST rea_assigns (CONST subst_upd (CONST subst_id) x (e)\<^sub>e)"
  "_rea_assign (_svid_tuple (_of_svid_list (x +\<^sub>L y))) e" <= "_rea_assign (x +\<^sub>L y) e" 

lemma rea_assigns_RR_closed [closure]: 
  "\<langle>\<sigma>\<rangle>\<^sub>r is RR"
  apply pred_auto using minus_zero_eq by auto

lemma st_subst_assigns_rea [usubst]:
  "\<sigma> \<dagger>\<^sub>S \<langle>\<rho>\<rangle>\<^sub>r = \<langle>\<rho> \<circ>\<^sub>s \<sigma>\<rangle>\<^sub>r"
  by pred_auto

lemma st_subst_rea_skip [usubst]:
  "\<sigma> \<dagger>\<^sub>S II\<^sub>r = \<langle>\<sigma>\<rangle>\<^sub>r"
  by pred_auto

lemma rea_assigns_comp [rpred]:
  assumes "P is RR"
  shows "\<langle>\<sigma>\<rangle>\<^sub>r ;; P = \<sigma> \<dagger>\<^sub>S P"
proof -
  have "\<langle>\<sigma>\<rangle>\<^sub>r ;; (RR P) = \<sigma> \<dagger>\<^sub>S (RR P)"
    by pred_auto
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma rea_assigns_rename [rpred]:
  "renamer f \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>r\<lparr>f\<rparr>\<^sub>r = \<langle>\<sigma>\<rangle>\<^sub>r"
  using minus_zero_eq by pred_auto

lemma st_subst_RR [closure]:
  assumes "P is RR"
  shows "(\<sigma> \<dagger>\<^sub>S P) is RR"
proof -
  have "(\<sigma> \<dagger>\<^sub>S RR(P)) is RR"
    by pred_auto
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma rea_assigns_st_subst [usubst]:
  "\<lceil>\<sigma> \<up>\<^sub>s st\<rceil>\<^sub>s \<dagger> \<langle>\<rho>\<rangle>\<^sub>r = \<langle>\<rho> \<circ>\<^sub>s \<sigma>\<rangle>\<^sub>r"
  by pred_auto

subsubsection \<open> Conditional \<close>

text \<open> We guard the reactive conditional condition so that it can't be simplified by alphabet
  laws unless explicitly simplified. \<close>

(*  ::
  "('s,'t::trace,'\<alpha>,'\<beta>) rsp_rel \<Rightarrow>
  's pred \<Rightarrow>
  ('s,'t,'\<alpha>,'\<beta>) rsp_rel \<Rightarrow>
  ('s,'t,'\<alpha>,'\<beta>) rsp_rel" where *)

syntax
  "_cond_srea" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(3_ \<triangleleft> _ \<triangleright>\<^sub>R/ _)" [52,0,53] 52)

translations
  "_cond_srea P b Q" == "P \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>\<leftarrow> \<triangleright> Q"

lemma st_cond_assigns [rpred]:
  "\<langle>\<sigma>\<rangle>\<^sub>r \<triangleleft> b \<triangleright>\<^sub>R \<langle>\<rho>\<rangle>\<^sub>r = \<langle>\<sigma> \<triangleleft> b \<triangleright> \<rho>\<rangle>\<^sub>r"
  by pred_auto

lemma cond_srea_RR_closed [closure]:
  assumes "P is RR" "Q is RR"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q is RR"
proof -
  have "RR(RR(P) \<triangleleft> b \<triangleright>\<^sub>R RR(Q)) = RR(P) \<triangleleft> b \<triangleright>\<^sub>R RR(Q)"
    by pred_auto
  thus ?thesis
    by (metis Healthy_def' assms(1) assms(2))
qed

lemma cond_srea_RC1_closed:
  assumes "P is RC1" "Q is RC1"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q is RC1"
proof -
  have "RC1(RC1(P) \<triangleleft> b \<triangleright>\<^sub>R RC1(Q)) = RC1(P) \<triangleleft> b \<triangleright>\<^sub>R RC1(Q)"
    by (pred_simp, meson dual_order.refl order.trans)
  thus ?thesis
    by (metis Healthy_def' assms)
qed

lemma cond_srea_RC_closed [closure]:
  assumes "P is RC" "Q is RC"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q is RC"
  by (rule RC_intro', simp_all add: closure cond_srea_RC1_closed RC_implies_RC1 assms)

lemma R4_cond [rpred]: "R4(P \<triangleleft> b \<triangleright>\<^sub>R Q) = ((R4(P)) \<triangleleft> b \<triangleright>\<^sub>R (R4(Q)))"
  by pred_auto

lemma R5_cond [rpred]: "R5(P \<triangleleft> b \<triangleright>\<^sub>R Q) = (R5(P) \<triangleleft> b \<triangleright>\<^sub>R R5(Q))"
  by pred_auto

lemma rea_rename_cond [rpred]: "(P \<triangleleft> b \<triangleright>\<^sub>R Q)\<lparr>f\<rparr>\<^sub>r = P\<lparr>f\<rparr>\<^sub>r \<triangleleft> b \<triangleright>\<^sub>R Q\<lparr>f\<rparr>\<^sub>r"
  by (pred_auto; metis)
  
subsubsection \<open> Assumptions \<close>

definition rea_assume :: "'s pred \<Rightarrow> ('s, 't::trace, '\<alpha>) rsp_hrel" ("[_]\<^sup>\<top>\<^sub>r") where
[pred]: "[b]\<^sup>\<top>\<^sub>r = (II\<^sub>r \<triangleleft> b \<triangleright>\<^sub>R false)"

expr_constructor rea_assume

lemma rea_assume_RR [closure]: "[b]\<^sup>\<top>\<^sub>r is RR"
  by (simp add: rea_assume_def closure)

lemma rea_assume_false [rpred]: "[false]\<^sup>\<top>\<^sub>r = false"
  by pred_auto

lemma rea_assume_true [rpred]: "[true]\<^sup>\<top>\<^sub>r = II\<^sub>r"
  by pred_auto

lemma rea_assume_comp [rpred]: "[b]\<^sup>\<top>\<^sub>r ;; [c]\<^sup>\<top>\<^sub>r = [b \<and> c]\<^sup>\<top>\<^sub>r"
  by pred_auto

subsubsection \<open> State Abstraction \<close>

text \<open> We introduce state abstraction by creating some lens functors that allow us to lift
  a lens on the state-space to one on the whole stateful reactive alphabet. \<close>

definition lmap\<^sub>R :: "('a \<Longrightarrow> 'b) \<Rightarrow> ('t::trace, 'a) rp \<Longrightarrow> ('t, 'b) rp" where
[lens_defs]: "lmap\<^sub>R = lmap[rea_vars]"

text \<open> This construction lens is useful for conversion between a record and its product representation;
  it would be helpful if this could be automatically generated. \<close>

definition rsp_make_lens :: "('\<sigma>, '\<tau>::trace, '\<alpha>) rsp \<Longrightarrow> bool \<times> bool \<times> '\<tau> \<times> '\<sigma> \<times> '\<alpha>" where
[lens_defs]: "rsp_make_lens = \<lparr> lens_get = \<lambda> (ok, wait, tr, st, more). \<lparr> ok\<^sub>v = ok, wait\<^sub>v = wait, tr\<^sub>v = tr, st\<^sub>v = st, \<dots> = more \<rparr>
                              , lens_put = (\<lambda> s v. (ok\<^sub>v v, wait\<^sub>v v, tr\<^sub>v v, st\<^sub>v v, more v)) \<rparr>"

lemma rsp_make_lens_alt: "rsp_make_lens = inv\<^sub>L (ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L st +\<^sub>L srea_vars.more\<^sub>L)"
  by (auto simp add: lens_defs alpha_defs)

lemma make_lens_bij [simp]: "bij_lens rsp_make_lens"
  by (unfold_locales, simp_all add: lens_defs prod.case_eq_if)

text \<open> The following is an intuitive definition of the @{term st} functorial lens, which
  frames all the state space excluding @{term st}, to which another lens @{term l} is
  applied. We do this by splitting the state space into a product, including the application
  of @{term l} to @{term st}, and then invert the product creation lens to reconstruct
  the reactive state space. \<close>

definition map_st_lens ::
  "('\<sigma> \<Longrightarrow> '\<psi>) \<Rightarrow>
   (('\<sigma>, '\<tau>::trace, '\<alpha>) rsp \<Longrightarrow> ('\<psi>, '\<tau>::trace, '\<alpha>) rsp)" ("map'_st\<^sub>L") where
"map_st_lens l = inv\<^sub>L (ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L st +\<^sub>L \<^bold>v\<^sub>S) ;\<^sub>L 
                 (ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L (l ;\<^sub>L st) +\<^sub>L \<^bold>v\<^sub>S)"

text \<open> The above definition is intuitive, but unhelpful in proof automaton. Consequently,
  we the following optimised definition below. \<close>

lemma map_st_lens_alt_def [lens_defs]:
  "map_st_lens l = \<lparr> lens_get = \<lambda> s. \<lparr> ok\<^sub>v = ok\<^sub>v s, wait\<^sub>v = wait\<^sub>v s, tr\<^sub>v = tr\<^sub>v s, st\<^sub>v = get\<^bsub>l\<^esub> (st\<^sub>v s), \<dots> = more s \<rparr>
                  , lens_put = \<lambda> s v. \<lparr> ok\<^sub>v = ok\<^sub>v v, wait\<^sub>v = wait\<^sub>v v, tr\<^sub>v = tr\<^sub>v v, st\<^sub>v = put\<^bsub>l\<^esub> (st\<^sub>v s) (st\<^sub>v v), \<dots> = more v \<rparr> \<rparr>"
  by (auto simp add: map_st_lens_def lens_defs alpha_defs fun_eq_iff)

lemma map_st_vwb [simp]: "vwb_lens X \<Longrightarrow> vwb_lens (map_st\<^sub>L X)"
  by (unfold_locales, auto simp add: lens_defs)

lemma map_st_lens_indep_st [simp]: 
  "a \<bowtie> x \<Longrightarrow> map_st\<^sub>L a \<bowtie> x ;\<^sub>L st"
  by (rule lens_indep.intro, auto simp add: lens_defs alpha_defs lens_indep_comm lens_indep.lens_put_irr2)

lemma map_st_lens_indep_st' [simp]: 
  "x \<bowtie> a \<Longrightarrow> map_st\<^sub>L a \<bowtie> x ;\<^sub>L st"
  by (rule lens_indep.intro, simp_all add: alpha_defs lens_defs lens_indep_comm lens_indep.lens_put_irr2)

syntax
  "_map_st_lens" :: "logic \<Rightarrow> svid" ("map'_st\<^sub>L[_]")

translations
  "_map_st_lens a" => "CONST map_st_lens a"

abbreviation "abs_st\<^sub>L \<equiv> (map_st\<^sub>L 0\<^sub>L) \<times>\<^sub>L (map_st\<^sub>L 0\<^sub>L)"

abbreviation abs_st ("\<langle>_\<rangle>\<^sub>S") where
"abs_st P \<equiv> P \<down> abs_st\<^sub>L"

lemma rea_impl_aext_st [alpha]:
  "(P \<longrightarrow>\<^sub>r Q) \<up> (map_st\<^sub>L[a] \<times> map_st\<^sub>L[a]) = (P \<up>\<^sub>2 map_st\<^sub>L[a] \<longrightarrow>\<^sub>r Q \<up>\<^sub>2 map_st\<^sub>L[a])"
  by (pred_auto)

lemma rea_true_ext_st [alpha]: 
  "true\<^sub>r \<up> abs_st\<^sub>L = true\<^sub>r"
  by pred_auto

subsubsection \<open> Reactive Frames and Extensions \<close>

definition rea_frame :: "('\<alpha> \<Longrightarrow> '\<beta>) \<Rightarrow> ('\<beta>, 't::trace, 'r) rsp_hrel \<Rightarrow> ('\<beta>, 't, 'r) rsp_hrel" where
[pred]: "rea_frame x P = $(ok,wait,tr,st:x,\<^bold>v\<^sub>S):[P]"

definition rea_frame_ext :: "('\<alpha> \<Longrightarrow> '\<beta>) \<Rightarrow> ('\<alpha>, 't::trace, 'r) rsp_hrel \<Rightarrow> ('\<beta>, 't, 'r) rsp_hrel" where
[pred]: "rea_frame_ext a P = rea_frame a (P \<up>\<^sub>2 map_st\<^sub>L[a])"

syntax
  "_rea_frame"     :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]\<^sub>r" [99,0] 100)
  "_rea_frame_ext" :: "svid \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]\<^sub>r\<^sup>+" [99,0] 100)

translations
  "_rea_frame x P" => "CONST rea_frame x P"
  "_rea_frame (_salphaset (_salphamk x)) P" <= "CONST rea_frame x P"
  "_rea_frame_ext x P" => "CONST rea_frame_ext x P"
  "_rea_frame_ext (_salphaset (_salphamk x)) P" <= "CONST rea_frame_ext x P"

lemma rea_frame_R1_closed [closure]:
  assumes "vwb_lens x" "P is R1"
  shows "x:[P]\<^sub>r is R1"
proof -
  from assms(1) have "R1(x:[R1 P]\<^sub>r) = x:[R1 P]\<^sub>r"
    by (pred_auto)
  thus ?thesis
    by (metis Healthy_if Healthy_intro assms(2))
qed

lemma rea_frame_R2_closed [closure]: 
  assumes "vwb_lens x" "P is R2"
  shows "x:[P]\<^sub>r is R2"
proof -
  from assms(1) have "R2(x:[R2 P]\<^sub>r) = x:[R2 P]\<^sub>r"
    by (pred_auto)
  thus ?thesis
    by (metis Healthy_if Healthy_intro assms(2))
qed

lemma rea_frame_RR_closed [closure]: 
  assumes "vwb_lens x" "P is RR"
  shows "x:[P]\<^sub>r is RR"
proof -
  from assms(1) have "RR(x:[RR P]\<^sub>r) = x:[RR P]\<^sub>r"
    by (pred_auto)
  thus ?thesis
    by (metis Healthy_if Healthy_intro assms(2))
qed

lemma rea_aext_R1 [closure]:
  assumes "P is R1"
  shows "P \<up>\<^sub>2 map_st\<^sub>L[x] is R1"
proof -
  have "R1 P \<up>\<^sub>2 map_st\<^sub>L[x] is R1"
    by (pred_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma rea_aext_R2 [closure]:
  assumes "P is R2"
  shows "P \<up>\<^sub>2 map_st\<^sub>L[x] is R2"
proof -
  have "R2 P \<up>\<^sub>2 map_st\<^sub>L[x] is R2"
    by (pred_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma rea_aext_RR [closure]:
  assumes "P is RR"
  shows "P \<up>\<^sub>2 map_st\<^sub>L[x] is RR"
proof -
  have "RR P \<up>\<^sub>2 map_st\<^sub>L[x] is RR"
    by (pred_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma true_rea_map_st [alpha]: "(R1 true \<up>\<^sub>2 map_st\<^sub>L[a]) = R1 true"
  by (pred_auto)

lemma rea_frame_ext_R1_closed [closure]:
  "\<lbrakk> vwb_lens x; P is R1 \<rbrakk> \<Longrightarrow> x:[P]\<^sub>r\<^sup>+ is R1"
  by (simp add: rea_frame_ext_def closure)

lemma rea_frame_ext_R2_closed [closure]:
  "\<lbrakk> vwb_lens x; P is R2 \<rbrakk> \<Longrightarrow> x:[P]\<^sub>r\<^sup>+ is R2"
  by (simp add: rea_frame_ext_def closure)

lemma rea_frame_ext_RR_closed [closure]:
  "\<lbrakk> vwb_lens x; P is RR \<rbrakk> \<Longrightarrow> x:[P]\<^sub>r\<^sup>+ is RR"
  by (simp add: rea_frame_ext_def closure)

lemma rel_aext_st_Instant_closed [closure]:
  "P is Instant \<Longrightarrow> rel_aext P (map_st\<^sub>L x) is Instant"
  by (pred_auto)

lemma rea_frame_ext_false [frame]:
  "vwb_lens x \<Longrightarrow> x:[false]\<^sub>r\<^sup>+ = false"
  by (pred_auto)
  
lemma rea_frame_ext_skip [frame]:
  "vwb_lens x \<Longrightarrow> x:[II\<^sub>r]\<^sub>r\<^sup>+ = II\<^sub>r"
  by (pred_auto)

(*
lemma rea_frame_ext_assigns [frame]:
  "vwb_lens x \<Longrightarrow> x:[\<langle>\<sigma>\<rangle>\<^sub>r]\<^sub>r\<^sup>+ = \<langle>\<sigma> \<up> x\<rangle>\<^sub>r"
  apply (pred_auto)
*)

lemma rea_frame_ext_cond [frame]:
  "vwb_lens x \<Longrightarrow> x:[P \<triangleleft> b \<triangleright>\<^sub>R Q]\<^sub>r\<^sup>+ = x:[P]\<^sub>r\<^sup>+ \<triangleleft> (b \<up> x) \<triangleright>\<^sub>R x:[Q]\<^sub>r\<^sup>+"
  by (pred_auto)

(*
lemma rea_frame_ext_seq [frame]:
  "vwb_lens x \<Longrightarrow> x:[P ;; Q]\<^sub>r\<^sup>+ = x:[P]\<^sub>r\<^sup>+ ;; x:[Q]\<^sub>r\<^sup>+"
  apply (pred_auto)
  apply (simp add: rea_frame_ext_def rea_frame_def alpha frame)
  apply (subst frame_seq)
     apply (simp_all add: plus_vwb_lens closure)
   apply (pred_auto)+
  done

lemma rea_frame_ext_subst_indep [usubst]:
  assumes "x \<bowtie> y" "\<Sigma> \<sharp> v" "P is RR"
  shows "\<sigma>(y \<mapsto>\<^sub>s v) \<dagger>\<^sub>S x:[P]\<^sub>r\<^sup>+ = (\<sigma> \<dagger>\<^sub>S x:[P]\<^sub>r\<^sup>+) ;; y :=\<^sub>r v"
proof -
  from assms(1-2) have "\<sigma>(y \<mapsto>\<^sub>s v) \<dagger>\<^sub>S x:[RR P]\<^sub>r\<^sup>+ = (\<sigma> \<dagger>\<^sub>S x:[RR P]\<^sub>r\<^sup>+) ;; y :=\<^sub>r v"
    by (pred_auto, (metis (no_types, lifting) lens_indep.lens_put_comm lens_indep_get)+)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma rea_frame_ext_subst_within [usubst]:
  assumes "vwb_lens x" "vwb_lens y" "\<Sigma> \<sharp> v" "P is RR"
  shows "\<sigma>(x:y \<mapsto>\<^sub>s v) \<dagger>\<^sub>S x:[P]\<^sub>r\<^sup>+ = (\<sigma> \<dagger>\<^sub>S x:[y :=\<^sub>r (v \<restriction>\<^sub>e x) ;; P]\<^sub>r\<^sup>+)"
proof -
  from assms(1,3) have "\<sigma>(x:y \<mapsto>\<^sub>s v) \<dagger>\<^sub>S x:[RR P]\<^sub>r\<^sup>+ = (\<sigma> \<dagger>\<^sub>S x:[y :=\<^sub>r (v \<restriction>\<^sub>e x) ;; RR(P)]\<^sub>r\<^sup>+)"
    by (pred_auto, metis+)
  thus ?thesis
    by (simp add: assms Healthy_if)
qed
*)

lemma rea_frame_ext_INF_ind [frame]:
  "vwb_lens a \<Longrightarrow> a:[\<Sqinter> x. P x]\<^sub>r\<^sup>+ = (\<Sqinter> x. a:[P x]\<^sub>r\<^sup>+)"
  by (pred_auto)

lemma rea_frame_ext_INF_mem [frame]: 
  "vwb_lens a \<Longrightarrow> a:[\<Sqinter> x\<in>A. P x]\<^sub>r\<^sup>+ = (\<Sqinter> x\<in>A. a:[P x]\<^sub>r\<^sup>+)"
  by (pred_auto)

subsection \<open> Stateful Reactive specifications \<close>

definition rea_st_rel :: "'s hrel \<Rightarrow> ('s,'t::trace,'\<alpha>,'\<beta>) rsp_rel" ("[_]\<^sub>S") where
[pred]: "rea_st_rel b = (\<lceil>(b)\<^sub>e\<rceil>\<^sub>S \<and> (tr\<^sup>> = tr\<^sup><)\<^sub>e)"

definition rea_st_rel' :: "'s hrel \<Rightarrow> ('s,'t::trace,'\<alpha>,'\<beta>) rsp_rel" ("[_]\<^sub>S''") where
[pred]: "rea_st_rel' b = R1(\<lceil>b\<rceil>\<^sub>S)"

definition rea_st_cond :: "'s pred \<Rightarrow> ('s,'t::trace,'\<alpha>,'\<beta>) rsp_rel" where
[pred]: "rea_st_cond b = R1(\<lceil>b\<rceil>\<^sub>S\<^sub><)"

expr_constructor rea_st_cond

syntax "_rea_st_cond" :: "logic \<Rightarrow> logic" ("[_]\<^sub>S\<^sub><")
translations "_rea_st_cond b" == "CONST rea_st_cond (b)\<^sub>e"
syntax_consts "_rea_st_cond" == rea_st_cond

definition rea_st_post :: "'s pred \<Rightarrow> ('s,'t::trace,'\<alpha>,'\<beta>) rsp_rel" where
[pred]: "rea_st_post b = R1(\<lceil>b\<rceil>\<^sub>S\<^sub>>)"

expr_constructor rea_st_post

syntax "_rea_st_post" :: "logic \<Rightarrow> logic" ("[_]\<^sub>S\<^sub>>")
translations "_rea_st_post b" == "CONST rea_st_post (b)\<^sub>e"
syntax_consts "_rea_st_post" == rea_st_post

lemma lift_state_pre_unrest [unrest]: "\<lbrakk> vwb_lens x; x \<bowtie> (st\<^sup><)\<^sub>v \<rbrakk> \<Longrightarrow> $x \<sharp> \<lceil>P\<rceil>\<^sub>S\<^sub><"
  by (pred_auto, expr_simp add: lens_indep_def)

lemma rea_st_rel_unrest [unrest]:
  "\<lbrakk> vwb_lens x; x \<bowtie> (tr\<^sup><)\<^sub>v; x \<bowtie> (tr\<^sup>>)\<^sub>v; x \<bowtie> (st\<^sup><)\<^sub>v; x \<bowtie> (st\<^sup>>)\<^sub>v \<rbrakk> \<Longrightarrow> $x \<sharp> [P]\<^sub>S\<^sub><"
  by (pred_simp, expr_simp add: lens_indep_def)


lemma rea_st_cond_unrest [unrest]:
  "\<lbrakk> vwb_lens x; x \<bowtie> (tr\<^sup><)\<^sub>v; x \<bowtie> (tr\<^sup>>)\<^sub>v; x \<bowtie> (st\<^sup><)\<^sub>v \<rbrakk> \<Longrightarrow> $x \<sharp> [P]\<^sub>S\<^sub><"
  by (pred_simp, expr_simp add: lens_indep_def)

lemma subst_st_cond [usubst]: "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> [P]\<^sub>S\<^sub>< = [\<sigma> \<dagger> P]\<^sub>S\<^sub><"
  by pred_auto

lemma rea_st_cond_R1 [closure]: "[b]\<^sub>S\<^sub>< is R1"
  by pred_auto

lemma rea_st_cond_R2c [closure]: "[b]\<^sub>S\<^sub>< is R2c"
  by pred_auto

lemma rea_st_rel_RR [closure]: "[P]\<^sub>S is RR"
  using minus_zero_eq by pred_auto

lemma rea_st_rel'_RR [closure]: "[P]\<^sub>S' is RR"
  by pred_auto

lemma rea_st_post_RR [closure]: "[b]\<^sub>S\<^sub>> is RR"
  by pred_auto

lemma st_subst_rel [usubst]:
  "\<sigma> \<dagger>\<^sub>S [P]\<^sub>S = [\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> P]\<^sub>S"
  by pred_auto

lemma st_rel_cond [rpred]:
  "[P \<lhd> b \<rhd> Q]\<^sub>S = [P]\<^sub>S \<triangleleft> b \<triangleright>\<^sub>R [Q]\<^sub>S"
  by (pred_auto)

lemma st_rel_false [rpred]: "[false]\<^sub>S = false"
  by pred_auto

lemma st_rel_skip [rpred]: 
  "[II]\<^sub>S = (II\<^sub>r :: ('s, 't::trace) rdes)"
  by pred_auto

lemma st_rel_seq [rpred]:
  "[P ;; Q]\<^sub>S = [P]\<^sub>S ;; [Q]\<^sub>S"
  by pred_auto
  
lemma st_rel_conj [rpred]:
  "([P]\<^sub>S \<and> [Q]\<^sub>S) = [P \<and> Q]\<^sub>S"
   by pred_auto

lemma st_cond_disj [rpred]: 
  "([P]\<^sub>S\<^sub>< \<or> [Q]\<^sub>S\<^sub><) = [P \<or> Q]\<^sub>S\<^sub><"
  by pred_auto

lemma rea_st_cond_RR [closure]: "[b]\<^sub>S\<^sub>< is RR"
  by (rule RR_intro, simp_all add: unrest closure; pred_auto)

lemma rea_st_cond_RC [closure]: "[b]\<^sub>S\<^sub>< is RC"
  by (rule RC_intro, simp add: closure, pred_auto)
    
lemma rea_st_cond_true [rpred]: "[True]\<^sub>S\<^sub>< = true\<^sub>r"
  by pred_auto

lemma rea_st_cond_false [rpred]: "[False]\<^sub>S\<^sub>< = false"
  by pred_auto
    
lemma st_cond_not [rpred]: "(\<not>\<^sub>r [P]\<^sub>S\<^sub><) = [\<not> P]\<^sub>S\<^sub><"
  by pred_auto

lemma st_cond_conj [rpred]: "([P]\<^sub>S\<^sub>< \<and> [Q]\<^sub>S\<^sub><) = [P \<and> Q]\<^sub>S\<^sub><"
  by pred_auto
    
lemma st_rel_assigns [rpred]:
  "[\<langle>\<sigma>\<rangle>\<^sub>a]\<^sub>S = (\<langle>\<sigma>\<rangle>\<^sub>r :: ('\<alpha>, 't::trace) rdes)"
  by pred_auto

lemma cond_st_distr: "(P \<triangleleft> b \<triangleright>\<^sub>R Q) ;; R = (P ;; R \<triangleleft> b \<triangleright>\<^sub>R Q ;; R)"
  by (pred_auto; blast)
        
lemma cond_st_miracle [rpred]: "P is R1 \<Longrightarrow> P \<triangleleft> b \<triangleright>\<^sub>R false = ([b]\<^sub>S\<^sub>< \<and> P)"
  by (pred_auto; blast)

lemma cond_st_true [rpred]: "P \<triangleleft> True \<triangleright>\<^sub>R Q = P"
  by pred_auto
    
lemma cond_st_false [rpred]: "P \<triangleleft> False \<triangleright>\<^sub>R Q = Q"
  by pred_auto
    
lemma st_cond_true_or [rpred]: "P is R1 \<Longrightarrow> (R1 true \<triangleleft> b \<triangleright>\<^sub>R P) = ([b]\<^sub>S\<^sub>< \<or> P)"  
by (pred_auto; blast)
    
lemma st_cond_left_impl_RC_closed [closure]:
  "P is RC \<Longrightarrow> ([b]\<^sub>S\<^sub>< \<longrightarrow>\<^sub>r P) is RC"
  by (simp add: rea_impl_def rpred closure)

end