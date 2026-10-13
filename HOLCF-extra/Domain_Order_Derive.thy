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
  @{text erule}; the others come easiest first, ending with the step, which is stated for the
  folded left-hand side (the iterate lies below it).\<close>

lemma map_beta_step: "M = (\<Lambda> v. B v) \<Longrightarrow> cont B \<Longrightarrow> M\<cdot>v = B v"
  by simp

lemma map_fix_induct:
  fixes G :: "('a::pcpo \<rightarrow> 'a) \<Rightarrow> 'a \<rightarrow> 'a"
  assumes eq: "m = fix\<cdot>(\<Lambda> f. G f)" and adm: "adm P" and bot: "P \<bottom>"
    and cont: "cont G"
    and step: "\<And>f. f \<sqsubseteq> m \<Longrightarrow> P f \<Longrightarrow> P (G f)"
  shows "P m"
  unfolding eq
proof (rule fix_preserves_below[OF cont adm bot])
  fix f assume "f \<sqsubseteq> fix\<cdot>(\<Lambda> f. G f)" and P: "P f"
  then have "f \<sqsubseteq> m" by (simp only: eq)
  then show "P (G f)" using P by (rule step)
qed

subsection \<open>Registries\<close>

text \<open>The classes handled here (bounded completeness, separation, distributivity) are categories
  of domains closed under the domain constructions; the registries are prefixed accordingly.\<close>

named_theorems domain_category_adm \<open>admissibility of the predicates\<close>
  and domain_category_bottom \<open>the predicates at @{term \<bottom>}\<close>
  and domain_category_iso \<open>transport along an isomorphism, premises in the shape of \<open>T.iso_rews\<close>\<close>
  and domain_category_map \<open>the predicates through the map combinators and registered type maps\<close>
  and domain_category_ID \<open>the predicates at @{term ID}, under class assumptions\<close>
  and domain_category_deflation \<open>each predicate implies @{const deflation}\<close>
  and domain_category_below \<open>antitonicity among deflations, premise \<open>d \<sqsubseteq> e\<close> first\<close>
  and domain_category_class \<open>class introduction from the predicate at @{term ID}\<close>

lemmas [domain_category_adm] = adm_bounded_complete_defl adm_separated_defl adm_downclosed_defl
  adm_distributive_defl adm_separating_defl

lemmas [domain_category_bottom] = bounded_complete_defl_bottom separated_defl_bottom
  downclosed_defl_bottom distributive_defl_bottom separating_defl_bottom

lemmas [domain_category_iso] = bounded_complete_defl_iso separated_defl_iso downclosed_defl_iso
  distributive_defl_iso separating_defl_iso

lemmas [domain_category_map] =
  bounded_complete_defl_u_map bounded_complete_defl_ssum_map bounded_complete_defl_sprod_map
  separated_defl_u_map separated_defl_ssum_map separated_defl_sprod_map
  downclosed_defl_u_map downclosed_defl_ssum_map downclosed_defl_sprod_map
  distributive_defl_u_map distributive_defl_ssum_map distributive_defl_sprod_map
  separating_defl_u_map separating_defl_ssum_map separating_defl_sprod_map
  separating_defl_flat

lemmas [domain_category_ID] = bounded_complete_defl_ID separated_defl_ID downclosed_defl_ID
  distributive_defl_ID separating_defl_ID deflation_ID

lemmas [domain_category_deflation] = bounded_complete_defl.deflation separated_defl.deflation
  downclosed_defl.deflation distributive_defl.deflation separating_defl.deflation

lemmas [domain_category_below] = bounded_complete_defl_below separated_defl_below
  separating_defl_below

lemmas [domain_category_class] = bounded_complete_class_deflI separated_po_class_deflI
  distributive_cpo_class_deflI

subsection \<open>Methods\<close>

text \<open>Side goals left by the combinator rules: the hypothesis on the iterate or on the parameter,
  or their deflation part.  Another predicate \<open>Q\<close> on the iterate \<open>f\<close> (e.g. separation, needed
  when recursion passes through \<open>\<otimes>\<close>) is transferred from the fixed point: @{text erule} on
  @{attribute domain_category_below} matches the goal \<open>Q f\<close> and the step's hypothesis \<open>f \<sqsubseteq> M\<cdot>v\<close>
  at once, leaving \<open>Q (M\<cdot>v)\<close>, which must be one of the \<open>fix_facts\<close> — the type's own map rules
  for \<open>Q\<close>, derived beforehand.\<close>

method domain_category_side uses fix_facts =
  (assumption
   | erule domain_category_deflation
   | (erule domain_category_below, rule fix_facts))

text \<open>Beta-reduce the inserted map definition, one parameter per step.\<close>

method domain_category_beta declares cont2cont =
  ((drule map_beta_step, solves \<open>intro cont2cont\<close>)+)?

method domain_category_map_rule uses map_def iso_rews fix_facts declares cont2cont =
  (insert map_def[THEN meta_eq_to_obj_eq], (domain_category_beta cont2cont: cont2cont),
   (erule map_fix_induct,
     solves \<open>rule domain_category_adm\<close>,
     solves \<open>rule domain_category_bottom\<close>,
     solves \<open>intro cont2cont\<close>),
   rule domain_category_iso, solves \<open>rule iso_rews\<close>, solves \<open>rule iso_rews\<close>,
   intro domain_category_map domain_category_ID, (domain_category_side fix_facts: fix_facts)+)

text \<open>Instance from the registered map rule: the class property is the predicate at \<open>ID\<close>, and
  \<open>T_map\<cdot>ID = ID\<close>.\<close>

method domain_category_instance uses map_ID =
  (rule domain_category_class, subst map_ID[symmetric], rule domain_category_map,
   ((intro domain_category_ID)+)?)

end

