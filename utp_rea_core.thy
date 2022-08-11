theory utp_rea_core
  imports "UTP-Designs.utp_des_core" "UTP2.utp" "UTP2.utp_pred" "Shallow-Expressions.Shallow_Expressions" "Z_Toolkit.Trace_Algebra"
begin

alphabet 't::trace rea_vars = des_vars +
  wait :: bool
  tr   :: 't

type_synonym ('t, '\<alpha>) rp = "('t, '\<alpha>) rea_vars_scheme"

type_synonym ('t,'\<alpha>,'\<beta>) rel_rp  = "(('t,'\<alpha>) rea_vars_scheme, ('t,'\<beta>) rea_vars_scheme) urel"

type_synonym ('t, '\<alpha>) hrel_rp = "(('t,'\<alpha>) rea_vars_scheme, ('t,'\<alpha>) rea_vars_scheme) urel"

translations
  (type) "('t,'\<alpha>) rp" <= (type) "('t, '\<alpha>) rea_vars_scheme"
  (type) "('t,'\<alpha>) rp" <= (type) "('t, '\<alpha>) rea_vars_ext"
  (type) "('t,'\<alpha>,'\<beta>) rel_rp" <= (type) "(('t,'\<alpha>) rea_vars_scheme, ('\<gamma>,'\<beta>) rea_vars_scheme) urel"
  (type) "('t,'\<alpha>) hrel_rp"  <= (type) "(('t,'\<alpha>) rea_vars_scheme, ('\<gamma>,'\<beta>) rea_vars_scheme) urel"

(* Now denoted as v\<^sub>R rather than \<Sigma>\<^sub>R *)

notation rea_vars.more\<^sub>L ("\<^bold>v\<^sub>R")

term "\<^bold>v\<^sub>R"


syntax
  "_svid_rea_alpha"  :: "svid" ("\<^bold>v\<^sub>R")

translations
  "_svid_rea_alpha" => "CONST rea_vars.more\<^sub>L"

(*declare zero_list_def [upred_defs]
declare plus_list_def [upred_defs]*)
declare prefixE [elim]

abbreviation wait_f::"('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" ("_\<^sub>f" [1000] 1000)
where "wait_f R \<equiv> R\<lbrakk>False/wait\<^sup><\<rbrakk>"

abbreviation wait_t::"('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" ("_\<^sub>t" [1000] 1000)
  where "wait_t R \<equiv> R\<lbrakk>True/wait\<^sup><\<rbrakk>"

(*
syntax
  "_wait_f"  :: "logic \<Rightarrow> logic" ("_\<^sub>f" [1000] 1000)
  "_wait_t"  :: "logic \<Rightarrow> logic" ("_\<^sub>t" [1000] 1000)

translations
  "P \<^sub>f" \<rightleftharpoons> "CONST usubst (CONST subst_upd id\<^sub>s (CONST in_var CONST wait) false) P"
  "P \<^sub>t" \<rightleftharpoons> "CONST usubst (CONST subst_upd id\<^sub>s (CONST in_var CONST wait) true) P"
*)

abbreviation lift_rea :: "('\<alpha>, '\<beta>) urel \<Rightarrow> ('t::trace, '\<alpha>, '\<beta>) rel_rp" ("\<lceil>_\<rceil>\<^sub>R") where
"\<lceil>P\<rceil>\<^sub>R \<equiv> P \<up> (\<^bold>v\<^sub>R\<^sup>2)"

definition drop_rea :: "('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('\<alpha>, '\<beta>) urel" ("\<lfloor>_\<rfloor>\<^sub>R") where
"\<lfloor>P\<rfloor>\<^sub>R \<equiv> P \<down> (\<^bold>v\<^sub>R\<^sup>2)"

(*
abbreviation rea_pre_lift :: "('d \<Rightarrow> 'e) \<Rightarrow> ('a, 'b, 'c) rel_rp"  ("\<lceil>_\<rceil>\<^sub>R\<^sub><") where "\<lceil>n\<rceil>\<^sub>R\<^sub>< \<equiv> \<lceil>n\<^sup><\<rceil>\<^sub>R"

lemma unrest_ok_lift_rea [unrest]:
  "$ok\<^sup>< \<sharp> \<lceil>P\<rceil>\<^sub>R" "$ok\<^sup>> \<sharp> \<lceil>P\<rceil>\<^sub>R"
  unfolding lift_rea_def
  apply (simp add: unrest_aext_expr_lens)
  apply (simp add: unrest_aext_expr_lens) 
  done
*)

subsection \<open> Reactive Lemmas \<close>

lemma des_lens_equiv_wait_tr_rest: "\<^bold>v\<^sub>D \<approx>\<^sub>L (wait +\<^sub>L tr +\<^sub>L \<^bold>v\<^sub>R)"
  by simp

text \<open> Pairing the reactive alphabet with its control variables forms a bijective lens. \<close>
lemma rea_lens_bij: "bij_lens (ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L \<^bold>v\<^sub>R)"
proof -
  have "ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L \<^bold>v\<^sub>R \<approx>\<^sub>L ok +\<^sub>L \<^bold>v\<^sub>D"
    using des_lens_equiv_wait_tr_rest des_vars.indeps lens_equiv_sym lens_plus_eq_right by blast
  also have "... \<approx>\<^sub>L 1\<^sub>L"
    using bij_lens_equiv_id[of "ok +\<^sub>L \<^bold>v\<^sub>D"]
    using des_vars.bij_lenses by blast
  finally show ?thesis
    by (simp add: bij_lens_equiv_id)
qed

lemma seqr_wait_true [usubst]: "(P ;; Q) \<^sub>t = (P \<^sub>t ;; Q)"
  by pred_simp

lemma seqr_wait_false [usubst]: "(P ;; Q) \<^sub>f = (P \<^sub>f ;; Q)"
  by pred_simp

definition tcontr :: "'t::trace \<Longrightarrow> ('t, '\<alpha>) rp \<times> ('t, '\<alpha>) rp" ("tt") where
  [lens_defs]:
  "tcontr = \<lparr> lens_get = (\<lambda> s. get\<^bsub>ns_alpha snd\<^sub>L tr\<^esub> s - get\<^bsub>ns_alpha fst\<^sub>L tr\<^esub> s) , 
              lens_put = (\<lambda> s v. put\<^bsub>ns_alpha snd\<^sub>L tr\<^esub> s (get\<^bsub>ns_alpha fst\<^sub>L tr\<^esub> s + v)) \<rparr>"

definition itrace :: "'t::trace \<Longrightarrow> ('t, '\<alpha>) rp \<times> ('t, '\<alpha>) rp" ("\<^bold>i\<^bold>t") where
  [lens_defs]:
  "itrace = \<lparr> lens_get = get\<^bsub>ns_alpha fst\<^sub>L tr\<^esub>, 
              lens_put = (\<lambda> s v. put\<^bsub>ns_alpha snd\<^sub>L tr\<^esub> (put\<^bsub>ns_alpha fst\<^sub>L tr\<^esub> s v) v) \<rparr>"

syntax
  "_svid_tcontr"  :: "svid" ("tt")
  "_svid_itrace"  :: "svid" ("\<^bold>i\<^bold>t")
  "_utr_iter"     :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("iter[_]'(_')")


translations
  "_svid_tcontr" == "CONST tcontr"
  "_svid_itrace" == "CONST itrace"
  "iter[n](P)"   == "CONST uop (CONST tr_iter n) P"


lemma tcontr_alt_def: "(tt)\<^sub>e = (tr\<^sup>> - tr\<^sup><)"
  by pred_auto

lemma tcontr_alt_def': "var tt = (tr\<^sup>> - tr\<^sup><)"
  by pred_auto

lemma tt_indeps [simp]:
  assumes "x \<bowtie> (ns_alpha fst\<^sub>L tr)" "x \<bowtie> (ns_alpha snd\<^sub>L tr)"
  shows "x \<bowtie> tt" "tt \<bowtie> x"
  using assms
  by (unfold lens_indep_def, safe, simp_all add: tcontr_def)
  
lemma itrace_indeps [simp]:
  assumes "x \<bowtie> (ns_alpha fst\<^sub>L tr)" "x \<bowtie> (ns_alpha snd\<^sub>L tr)"
  shows "x \<bowtie> \<^bold>i\<^bold>t" "\<^bold>i\<^bold>t \<bowtie> x"
  using assms by (unfold lens_indep_def, safe, simp_all add: lens_defs)

(* Thomas: these lemmata are not applicable unless we want to lift trace operations
 * to expressions as in UTP1 *)
(*
text \<open> We lift a few trace properties from the trace class using \emph{transfer}. \<close>

lemma uexpr_diff_zero [simp]:
  fixes a :: "('\<alpha>::trace, 'a) expr"
  shows "a - 0 = a"
  by (simp add: minus_uexpr_def zero_uexpr_def, transfer, auto)

lemma uexpr_add_diff_cancel_left [simp]:
  fixes a b :: "('\<alpha>::trace, 'a) expr"
  shows "(a + b) - a = b"
  by (simp add: minus_uexpr_def plus_uexpr_def, transfer, auto)

lemma iter_0 [simp]: "iter[0](t) = U([])"
  by (transfer, simp)
*)

end
