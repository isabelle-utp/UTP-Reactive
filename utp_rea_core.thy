theory utp_rea_core
  imports "UTP-Designs.utp_des_core" "UTP2.utp" "Shallow-Expressions.Shallow_Expressions"
begin

alphabet 'e rea_vars = des_vars +
  wait :: bool
  tr   :: "'e list"

type_synonym ('t, '\<alpha>) rp = "('t, '\<alpha>) rea_vars_scheme"

type_synonym ('t,'\<alpha>,'\<beta>) rel_rp  = "(('t,'\<alpha>) rea_vars_scheme, ('t,'\<beta>) rea_vars_scheme) urel"

type_synonym ('t, '\<alpha>) hrel_rp = "(('t,'\<alpha>) rea_vars_scheme, ('t,'\<alpha>) rea_vars_scheme) urel"

translations
  (type) "('t,'\<alpha>) rp" <= (type) "('t, '\<alpha>) rea_vars_scheme"
  (type) "('t,'\<alpha>) rp" <= (type) "('t, '\<alpha>) rea_vars_ext"
  (type) "('t,'\<alpha>,'\<beta>) rel_rp" <= (type) "(('t,'\<alpha>) rea_vars_scheme, ('\<gamma>,'\<beta>) rea_vars_scheme) urel"
  (type) "('t,'\<alpha>) hrel_rp"  <= (type) "(('t,'\<alpha>) rea_vars_scheme, ('\<gamma>,'\<beta>) rea_vars_scheme) urel"

notation rea_vars.more\<^sub>L ("\<^bold>v\<^sub>R")

term "\<^bold>v\<^sub>R"


syntax
  "_svid_rea_alpha"  :: "svid" ("\<^bold>v\<^sub>R")

translations
  "_svid_rea_alpha" => "CONST rea_vars.more\<^sub>L"

(*declare zero_list_def [upred_defs]
declare plus_list_def [upred_defs]*)
declare prefixE [elim]

abbreviation wait_f::"('t, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" ("_\<^sub>f" [1000] 1000)
where "wait_f R \<equiv> R\<lbrakk>False/wait\<^sup><\<rbrakk>"

abbreviation wait_t::"('t, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" ("_\<^sub>t" [1000] 1000)
  where "wait_t R \<equiv> R\<lbrakk>True/wait\<^sup><\<rbrakk>"

(*
syntax
  "_wait_f"  :: "logic \<Rightarrow> logic" ("_\<^sub>f" [1000] 1000)
  "_wait_t"  :: "logic \<Rightarrow> logic" ("_\<^sub>t" [1000] 1000)



translations
  "P \<^sub>f" \<rightleftharpoons> "CONST usubst (CONST subst_upd id\<^sub>s (CONST in_var CONST wait) false) P"
  "P \<^sub>t" \<rightleftharpoons> "CONST usubst (CONST subst_upd id\<^sub>s (CONST in_var CONST wait) true) P"
*)

definition lift_rea :: "('\<alpha>, '\<beta>) urel \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" ("\<lceil>_\<rceil>\<^sub>R") where
"\<lceil>P\<rceil>\<^sub>R \<equiv> P \<up> (\<^bold>v\<^sub>R\<^sup>2)"
term "\<lceil>P\<rceil>\<^sub>R"

definition drop_rea :: "('t, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('\<alpha>, '\<beta>) urel" ("\<lfloor>_\<rfloor>\<^sub>R") where
"\<lfloor>P\<rfloor>\<^sub>R \<equiv> P \<down> (\<^bold>v\<^sub>R\<^sup>2)"
term "\<lfloor>P\<rfloor>\<^sub>R"


abbreviation rea_pre_lift :: "('d \<Rightarrow> 'e) \<Rightarrow> ('a, 'b, 'c) rel_rp"  ("\<lceil>_\<rceil>\<^sub>R\<^sub><") where "\<lceil>n\<rceil>\<^sub>R\<^sub>< \<equiv> \<lceil>n\<^sup><\<rceil>\<^sub>R"

lemma unrest_ok_lift_rea [unrest]:
  "$ok\<^sup>< \<sharp> \<lceil>P\<rceil>\<^sub>R" "$ok\<^sup>> \<sharp> \<lceil>P\<rceil>\<^sub>R"
  unfolding lift_rea_def
  apply (simp add: unrest_aext_expr_lens)
  apply (simp add: unrest_aext_expr_lens) 
  done

(*

(*Needs trace algebra*)
definition tcontr :: "'t \<Longrightarrow> ('t, '\<alpha>) rp \<times> ('t, '\<alpha>) rp" ("tt") where
  [lens_defs]:
  "tcontr = \<lparr> lens_get = (\<lambda> s. get\<^bsub>tr\<^sup>>\<^esub> s - get\<^bsub>tr\<^sup><\<^esub> s) , 
              lens_put = (\<lambda> s v. put\<^bsub>tr\<^sup>>\<^esub> s (get\<^bsub>tr\<^sup><\<^esub> s + v)) \<rparr>"

definition itrace :: "'t \<Longrightarrow> ('t, '\<alpha>) rp \<times> ('t, '\<alpha>) rp" ("\<^bold>i\<^bold>t") where
  [lens_defs]:
  "itrace = \<lparr> lens_get = get\<^bsub>tr\<^sup><\<^esub>, 
              lens_put = (\<lambda> s v. put\<^bsub>tr\<^sup>>\<^esub> (put\<^bsub>tr\<^sup><\<^esub> s v) v) \<rparr>"

syntax
  "_svid_tcontr"  :: "svid" ("tt")
  "_svid_itrace"  :: "svid" ("\<^bold>i\<^bold>t")
  "_utr_iter"     :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("iter[_]'(_')")


translations
  "_svid_tcontr" == "CONST tcontr"
  "_svid_itrace" == "CONST itrace"
  "iter[n](P)"   == "CONST uop (CONST tr_iter n) P"
  
*)

(* Added by @MattWindsor91, to be merged into Ziggy's work *)

(* TODO(@MattWindsor91): should be in designs *)
text \<open> Pairing the design alphabet with the 'ok' variable forms a bijective lens. \<close>
lemma des_lens_bij: "bij_lens (ok +\<^sub>L des_vars.more\<^sub>L)" by simp

text \<open> The alphabet of a reactive process less its operational variables can be seen as
the equivalent alphabet of a design augmented with the wait and trace variables. \<close>
lemma des_lens_equiv_wait_tr_rest: "des_vars.more\<^sub>L \<approx>\<^sub>L wait +\<^sub>L tr +\<^sub>L \<^bold>v\<^sub>R" by simp

text \<open> Pairing the reactive alphabet with its control variables forms a bijective lens. \<close>
lemma rea_lens_bij: "bij_lens (ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L \<^bold>v\<^sub>R)"
proof -
  have "ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L \<^bold>v\<^sub>R \<approx>\<^sub>L ok +\<^sub>L des_vars.more\<^sub>L"
    by (auto intro!:lens_plus_cong, rule lens_equiv_sym, simp add: des_lens_equiv_wait_tr_rest)
  also have "... \<approx>\<^sub>L 1\<^sub>L"
    using bij_lens_equiv_id[of "ok +\<^sub>L des_vars.more\<^sub>L"] by (simp add: des_lens_bij)
  finally show ?thesis
    by (simp add: bij_lens_equiv_id)
qed

end
