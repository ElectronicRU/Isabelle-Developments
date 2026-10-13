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
  and the induction rule below needs nothing more.  Its step is stated for the folded left-hand
  side (the iterate lies below it), and its continuity premise comes last.\<close>

lemma defl_beta_step: "M = (\<Lambda> v. B v) \<Longrightarrow> cont B \<Longrightarrow> M\<cdot>v = B v"
  by simp

lemma defl_fix_induct:
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

lemma distributive_defl_deflation: "distributive_defl d \<Longrightarrow> deflation d"
  by (rule bounded_complete_defl.axioms(1)[OF distributive_defl.axioms(1)])

subsection \<open>Registries\<close>

named_theorems defl_adm \<open>admissibility of the predicates\<close>
  and defl_bottom \<open>the predicates at @{term \<bottom>}\<close>
  and defl_iso \<open>transport along an isomorphism, premises in the shape of \<open>T.iso_rews\<close>\<close>
  and defl_map \<open>the predicates through the map combinators and registered type maps\<close>
  and defl_ID \<open>the predicates at @{term ID}, under class assumptions\<close>
  and defl_deflation \<open>each predicate implies @{const deflation}\<close>
  and defl_below \<open>antitonicity among deflations, premise \<open>d \<sqsubseteq> e\<close> first\<close>
  and defl_class \<open>class introduction from the predicate at @{term ID}\<close>

lemmas [defl_adm] = adm_bounded_complete_defl adm_separated_defl adm_downclosed_defl
  adm_distributive_defl adm_separating_defl

lemmas [defl_bottom] = bounded_complete_defl_bottom separated_defl_bottom downclosed_defl_bottom
  distributive_defl_bottom separating_defl_bottom

lemmas [defl_iso] =
  bounded_complete_defl_iso[OF iso.intro] separated_defl_iso[OF iso.intro]
  downclosed_defl_iso[OF iso.intro] distributive_defl_iso[OF iso.intro]
  separating_defl_iso[OF iso.intro]

lemmas [defl_map] =
  bounded_complete_defl_u_map bounded_complete_defl_ssum_map bounded_complete_defl_sprod_map
  separated_defl_u_map separated_defl_ssum_map separated_defl_sprod_map
  downclosed_defl_u_map downclosed_defl_ssum_map downclosed_defl_sprod_map
  distributive_defl_u_map distributive_defl_ssum_map distributive_defl_sprod_map
  separating_defl_u_map separating_defl_ssum_map separating_defl_sprod_map
  separating_defl_flat

lemmas [defl_ID] = bounded_complete_defl_ID separated_defl_ID downclosed_defl_ID
  distributive_defl_ID separating_defl_ID deflation_ID

lemmas [defl_deflation] = bounded_complete_defl.axioms(1) separated_defl.axioms(1)
  downclosed_defl.axioms(1) separating_defl.axioms(1) distributive_defl_deflation

lemmas [defl_below] = bounded_complete_defl_below[rotated 2] separated_defl_below[rotated 2]
  separating_defl_below[rotated 2]

lemmas [defl_class] = bounded_complete_class_deflI separated_po_class_deflI
  distributive_cpo_class_deflI

subsection \<open>Methods\<close>

text \<open>Side goals left by the combinator rules: the hypothesis on the iterate or on the parameter,
  or their deflation part.  Another predicate \<open>Q\<close> on the iterate \<open>f\<close> (e.g. separation, needed
  when recursion passes through \<open>\<otimes>\<close>) is transferred from the fixed point: @{text erule} on
  @{attribute defl_below} matches the goal \<open>Q f\<close> and the step's hypothesis \<open>f \<sqsubseteq> M\<cdot>v\<close> at once,
  leaving \<open>Q (M\<cdot>v)\<close>, which must be one of the \<open>fix_facts\<close> — the type's own map rules for \<open>Q\<close>,
  derived beforehand.\<close>

method defl_side uses fix_facts =
  (assumption
   | erule defl_deflation
   | (erule defl_below, rule fix_facts))

text \<open>Beta-reduce the inserted map definition, one parameter per step.\<close>

method defl_beta declares cont2cont = ((drule defl_beta_step, solves \<open>intro cont2cont\<close>)+)?

method defl_map_rule uses map_def iso_rews fix_facts declares cont2cont =
  (insert map_def[THEN meta_eq_to_obj_eq], (defl_beta cont2cont: cont2cont),
   (erule defl_fix_induct,
     solves \<open>rule defl_adm\<close>,
     solves \<open>rule defl_bottom\<close>,
     solves \<open>intro cont2cont\<close>),
   rule defl_iso, solves \<open>rule iso_rews\<close>, solves \<open>rule iso_rews\<close>,
   intro defl_map defl_ID, (defl_side fix_facts: fix_facts)+)

text \<open>Instance from the registered map rule: the class property is the predicate at \<open>ID\<close>, and
  \<open>T_map\<cdot>ID = ID\<close>.\<close>

method defl_instance uses map_ID =
  (rule defl_class, subst map_ID[symmetric], rule defl_map, ((intro defl_ID)+)?)

end

