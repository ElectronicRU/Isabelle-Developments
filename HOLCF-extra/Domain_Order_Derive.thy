theory Domain_Order_Derive
  imports Domain_Order "HOL-Eisbach.Eisbach"
begin

section \<open>Deriving order-class instances of domain-package types\<close>

text \<open>Proof methods packaging the derivation of @{file "Domain_Order.thy"}: for a type \<open>T\<close> defined
  by the domain package, a map rule \<open>P v \<Longrightarrow> P (T_map\<cdot>v)\<close> (one premise per type parameter) is
  proved by fixed-point induction on the map functional, from the package's \<open>T_map_def\<close> and
  \<open>T.iso_rews\<close>; the instance then follows at \<open>v = ID\<close> from \<open>T_map_ID\<close>.  The rules for the
  combinators are collected in named theorem lists, so map rules of earlier types can be
  registered for nested recursion.\<close>

subsection \<open>Fixed-point induction on a map definition\<close>

text \<open>The package defines \<open>T_map \<equiv> \<Lambda> v\<^sub>1 \<dots> v\<^sub>n. \<mu> f. G v\<^sub>1 \<dots> v\<^sub>n f\<close>.  One beta step turns an
  equation \<open>M = (\<Lambda> v. B v)\<close> into \<open>M\<cdot>v = B v\<close>, again an equation of the same shape with one
  \<open>\<Lambda>\<close> fewer; its continuity side condition is a single goal for @{attribute cont2cont}.  After
  \<open>n\<close> steps the equation reads \<open>T_map\<cdot>v\<^sub>1\<cdot>\<dots>\<cdot>v\<^sub>n = \<mu> f. G f\<close>, with the parameters free in \<open>G\<close>,
  and the induction rule below needs nothing more.  The equation is its first premise, for
  @{text erule}; the others come easiest first, ending with the step.\<close>

lemma map_beta_step: "M = (\<Lambda> v. B v) \<Longrightarrow> cont B \<Longrightarrow> M\<cdot>v = B v"
  by simp

lemma map_fix_induct:
  fixes G :: "('a::pcpo \<rightarrow> 'a) \<Rightarrow> 'a \<rightarrow> 'a"
  assumes eq: "m = fix\<cdot>(\<Lambda> f. G f)" and adm: "adm P" and bot: "P \<bottom>"
    and cont: "cont G"
    and step: "\<And>f. P f \<Longrightarrow> P (G f)"
  shows "P m"
  unfolding eq by (rule fix_preserves[OF adm bot], rule preserves_LAM[OF cont], erule step)

text \<open>For a non-recursive type the functional ignores its argument, and the fixed point is the
  body itself; this needs neither admissibility nor the \<open>\<bottom>\<close> case.  The rule only unifies when the
  body does not mention the bound variable.\<close>

lemma map_fix_const: "m = fix\<cdot>(\<Lambda> f. c) \<Longrightarrow> P c \<Longrightarrow> P m"
  by (simp add: fix_const)

subsection \<open>Registries\<close>

text \<open>The classes handled here (bounded completeness, separation, distributivity) are categories
  of domains closed under the domain constructions; the registries are prefixed accordingly.
  Each combinator rule mentions only its own predicate; what a property needs from the others
  (distributivity of \<open>\<otimes>\<close> needs separated, bounded-complete components) is a sort constraint, so
  the classes are derived in dependency order.\<close>

named_theorems domain_category_adm \<open>admissibility of the predicates\<close>
  and domain_category_bottom \<open>the predicates at @{term \<bottom>}\<close>
  and domain_category_iso \<open>transport along an isomorphism, premises in the shape of \<open>T.iso_rews\<close>\<close>
  and domain_category_map \<open>the predicates through the map combinators and registered type maps\<close>
  and domain_category_ID \<open>the predicates at @{term ID}, under class assumptions\<close>
  and domain_category_deflation \<open>each predicate implies @{const deflation}\<close>
  and domain_category_class \<open>class introduction from the predicate at @{term ID}\<close>

lemmas [domain_category_adm] = adm_bounded_complete_defl adm_filter_sum_defl
  adm_separated_sum_defl adm_distributive_defl

lemmas [domain_category_bottom] = bounded_complete_defl_bottom filter_sum_defl_bottom
  separated_sum_defl_bottom distributive_defl_bottom

lemmas [domain_category_iso] = bounded_complete_defl_iso filter_sum_defl_iso
  separated_sum_defl_iso distributive_defl_iso

lemmas [domain_category_map] =
  bounded_complete_defl_u_map bounded_complete_defl_ssum_map bounded_complete_defl_sprod_map
  filter_sum_defl_u_map filter_sum_defl_ssum_map filter_sum_defl_sprod_map
  separated_sum_defl_u_map separated_sum_defl_ssum_map separated_sum_defl_sprod_map
  distributive_defl_u_map distributive_defl_ssum_map distributive_defl_sprod_map

lemmas [domain_category_ID] = bounded_complete_defl_ID filter_sum_defl_ID separated_sum_defl_ID
  distributive_defl_ID deflation_ID

lemmas [domain_category_deflation] = bounded_complete_defl.deflation filter_sum_defl.deflation
  separated_sum_defl.deflation distributive_defl.deflation

lemmas [domain_category_class] = bounded_complete_class_deflI filter_sum_class_deflI
  separated_sum_class_deflI distributive_cpo_class_deflI

subsection \<open>Methods\<close>

text \<open>Each step of a method is a single rule application, mostly out of a registry, and every
  leaf goal is closed under \<open>solves\<close>, so a step can only succeed by doing what it is meant to.
  For a type \<open>T\<close> the per-type inputs are all generated by the domain package (\<open>T_map_def\<close>,
  \<open>T.iso_rews\<close>, \<open>T_map_ID\<close>); no constructor-level lemmas are needed.  A typical use:
  @{theory_text [display]
\<open>lemma distributive_defl_T_map [domain_category_map]:
  "distributive_defl v \<Longrightarrow> distributive_defl w \<Longrightarrow> distributive_defl (T_map\<cdot>v\<cdot>w)"
  by (domain_category_map_rule map_def: T_map_def iso_rews: T.iso_rews)

instance T :: ("{domain, distributive_cpo}", "{domain, distributive_cpo}") distributive_cpo
  by (domain_category_instance map_ID: T_map_ID)\<close>}
  where the \<open>bounded_complete\<close> and \<open>filter_sum\<close> instances of \<open>T\<close> are derived before, if the
  recursion passes through \<open>\<otimes>\<close>.

  \<open>domain_category_map_rule\<close> proceeds as follows.
  \<^item> \<open>T_map_def\<close> is inserted as an equation and beta-reduced one parameter at a time by
    @{thm [source] map_beta_step}, each continuity side goal closed by \<open>intro cont2cont\<close>.  Any
    arity works, including zero.
  \<^item> \<open>erule map_fix_induct\<close> matches the reduced equation and the conclusion \<open>P m\<close> at once, which
    also fixes the parameters left schematic by the beta steps.  \<open>P\<close> comes from higher-order
    unification; a wrong unifier (e.g.\ a constant \<open>P\<close>) cannot pass \<open>solves \<open>rule
    domain_category_adm\<close>\<close>.
  \<^item> For a non-recursive type, \<open>erule map_fix_const\<close> is tried first: it unifies only when the
    functional ignores its argument, and then the predicate needs no admissibility or \<open>\<bottom>\<close> rule.
    So non-admissible predicates (e.g.\ finitary levels) can still be pushed through
    non-recursive types.
  \<^item> The iso rules take the \<open>abs_iso\<close>/\<open>rep_iso\<close> equations of \<open>T.iso_rews\<close> as premises, so the
    registries list source theorems as they are, without \<open>OF\<close> or \<open>rotated\<close>.
  \<^item> \<open>intro domain_category_map domain_category_ID\<close> decomposes the rep type; a combinator rule
    whose sort constraints the component types do not meet simply does not apply.  Side goals
    are closed by the induction hypothesis or by its deflation part.
  \<^item> \<open>declares cont2cont\<close> lets callers add continuity rules.

  \<open>domain_category_instance\<close> rewrites \<open>ID\<close> to \<open>T_map\<cdot>ID\<cdot>\<dots>\<close>, finds the map rule in
  @{attribute domain_category_map}, and closes the parameter premises from
  @{attribute domain_category_ID}.  What the user still decides by hand: the parameter sorts of
  each instance, and the order of the derivations.\<close>

method domain_category_side =
  (assumption | erule domain_category_deflation)

text \<open>Beta-reduce the inserted map definition, one parameter per step.\<close>

method domain_category_beta declares cont2cont =
  ((drule map_beta_step, solves \<open>intro cont2cont\<close>)+)?

method domain_category_map_rule uses map_def iso_rews declares cont2cont =
  (insert map_def[THEN meta_eq_to_obj_eq], (domain_category_beta cont2cont: cont2cont),
   (erule map_fix_const |
    erule map_fix_induct,
     solves \<open>rule domain_category_adm\<close>,
     solves \<open>rule domain_category_bottom\<close>,
     solves \<open>intro cont2cont\<close>),
   rule domain_category_iso, solves \<open>rule iso_rews\<close>, solves \<open>rule iso_rews\<close>,
   intro domain_category_map domain_category_ID, domain_category_side+)

text \<open>Instance from the registered map rule: the class property is the predicate at \<open>ID\<close>, and
  \<open>T_map\<cdot>ID = ID\<close>.\<close>

method domain_category_instance uses map_ID =
  (rule domain_category_class, subst map_ID[symmetric], rule domain_category_map,
   ((intro domain_category_ID)+)?)

subsection \<open>Future work: a derivation command\<close>

text \<open>A command \<open>derive_order_instances T\<close>, for one type or a mutually recursive group, would
  automate the remaining manual choices.
  \<^item> \<^emph>\<open>Package data.\<close>  Read the type constructors, \<open>T_map_def\<close>, \<open>iso_rews\<close>, \<open>T_map_ID\<close> and the
    rep-type functional from the domain package's theory data.
  \<^item> \<^emph>\<open>Variants.\<close>  Walk the functional and collect, per combinator position, the applicable
    rules: the general ones and the registered map rules of nested types.  Sort constraints at
    closed concrete types are decided by \<open>Sign.of_sort\<close>; those at types mentioning parameters
    become requirements on the parameter sorts.
  \<^item> \<^emph>\<open>Order.\<close>  Derive the classes in dependency order (bounded completeness and separation
    before distributivity), registering each instance before the next derivation.
  \<^item> \<^emph>\<open>Arity.\<close>  Each variant at \<open>v = ID\<close> gives a candidate arity; emit the unique minimal one
    (least parameter sorts), or fall back to the all-general variant with a warning.
  \<^item> \<^emph>\<open>Proof.\<close>  Instantiate the stored rules directly, building the closed map equation from the
    known parameters and abstracting \<open>P\<close> over the map term instead of relying on the unifier.
  Mutual recursion runs the fixed-point induction on the tuple of maps, with the predicate
  conjoined componentwise; the registry rules are unchanged.

  Open: there are no rules for \<open>cfun_map\<close> or the powerdomain maps; prior art to mirror is the
  domain package's own \<open>domain_take_proofs.ML\<close>, AFP \<^emph>\<open>Deriving\<close>, and the relator properties of
  Transfer/Lifting.\<close>

end

