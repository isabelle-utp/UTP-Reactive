section \<open> Events for Reactive Processes \<close>

theory utp_rea_event
imports "UTP2.utp"
begin

subsection \<open> Events \<close>

text \<open> Events of some type @{typ "'\<theta>"} are just the elements of that type. \<close>

type_synonym '\<theta> event = "'\<theta>"

subsection \<open> Channels \<close>

text \<open>
  Typed channels are modelled as prisms. Below, @{typ "'a"} determines the
  channel type and @{typ "'\<theta>"} the underlying event alphabet type. As with values, it
  is difficult to introduce channels as monomorphic types due to the fact that
  they can have arbitrary parametrisations in term of @{typ "'a"}. Applying a
  channel to an element of its type yields an event, as we may expect. Though
  this is not formalised here, we may also sensibly assume that all channel-
  representing functions are injective.
\<close>

type_synonym ('a, '\<theta>) chan = "'a \<Longrightarrow>\<^sub>\<triangle> '\<theta> event"

text \<open>
  A downside of the approach is that the event type @{typ "'\<theta>"} must be able
  to encode \emph{all} events of a process model, and hence cannot be fixed
  upfront for a single channel or channel set. To do so, we actually require
  a notion of `extensible' datatypes, in analogy to extensible record types.
  Another solution is to encode a notion of channel scoping that namely uses
  @{type sum} types to lift channel types into extensible ones, that is using
  channel-set specific scoping operators. This is a current work in progress.
\<close>

subsubsection \<open> Operators \<close>

text \<open>
  The next lifted function creates an expression that yields a channel event,
  from an expression on the channel type @{typ "'a"}.
\<close>

definition chan_apply ::
  "('a, '\<theta>) chan \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> ('\<theta> event, '\<alpha>) expr"  where
[pred]: "chan_apply c e = build\<^bsub>c\<^esub> \<circ> e"

syntax "_chan_apply" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("'(_\<cdot>/_')\<^sub>u")
translations "(c\<cdot>e)\<^sub>u" == "CONST chan_apply c (e)\<^sub>e"

lemma unrest_chan_apply [unrest]: "x \<sharp> e \<Longrightarrow> x \<sharp> (c\<cdot>e)\<^sub>u"
  by pred_auto

lemma usubst_chan_apply [usubst]: "\<sigma> \<dagger> (c\<cdot>v)\<^sub>u = (c\<cdot>\<sigma> \<dagger> v)\<^sub>u"
  by pred_auto

(* TODO: what should this be added to: [alpha] *)
lemma aext_event: "(c\<cdot>v)\<^sub>u \<up> a = (c\<cdot>v \<up> a)\<^sub>u"
  by pred_auto

end