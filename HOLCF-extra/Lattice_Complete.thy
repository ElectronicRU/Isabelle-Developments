theory Lattice_Complete imports Distributive begin

section ‹Bounded-complete domains with a top›

text ‹A bounded-complete pcpo with a top element is a complete lattice under its information
  order: every set is bounded, hence has a lub.  The lattice laws are stated as facts and then
  interpreted globally, rather than as a sublocale (see @{thm [source] below_order}), so that the
  join and meet of @{class bounded_complete} serve as the lattice operations, without joinability
  side conditions.›

class lattice_complete = bounded_complete +
  assumes ex_top: "∃t. ∀x. x ⊑ t"

definition lattice_top :: "'a::lattice_complete" where
  "lattice_top = lub UNIV"

definition Glb :: "'a::lattice_complete set ⇒ 'a" where
  "Glb S = lub {x. ∀y∈S. x ⊑ y}"

lemma below_lattice_top [simp]: "x ⊑ (lattice_top :: 'a::lattice_complete)"
proof -
  obtain t :: 'a where "∀x. x ⊑ t" using ex_top by blast
  then have "UNIV <| t" by (simp add: is_ub_def)
  then have "UNIV <<| lub (UNIV :: 'a set)" by (rule ex_bound_lub)
  then show ?thesis unfolding lattice_top_def by (blast dest: is_lubD1 is_ubD)
qed

lemma is_ub_lattice_top [simp]: "S <| (lattice_top :: 'a::lattice_complete)"
  by (simp add: is_ub_def)

lemma lub_is_lub: "S <<| lub (S :: 'a::lattice_complete set)"
  by (rule ex_bound_lub[OF is_ub_lattice_top])

lemma joinable_lattice [simp]: "(a :: 'a::lattice_complete) ⇑ b"
  by (rule joinableI[OF below_lattice_top below_lattice_top])

lemma below_lub: "x ∈ S ⟹ x ⊑ lub (S :: 'a::lattice_complete set)"
  by (rule is_ubD[OF is_lubD1[OF lub_is_lub]])

lemma lub_below: "S <| b ⟹ lub (S :: 'a::lattice_complete set) ⊑ b"
  by (rule is_lubD2[OF lub_is_lub])

lemma Glb_lower: "x ∈ S ⟹ Glb (S :: 'a::lattice_complete set) ⊑ x"
  unfolding Glb_def by (rule lub_below) (auto simp: is_ub_def)

lemma Glb_greatest: "(⋀y. y ∈ S ⟹ b ⊑ y) ⟹ b ⊑ Glb (S :: 'a::lattice_complete set)"
  unfolding Glb_def by (rule below_lub) simp

theorem complete_lattice_below:
  "class.complete_lattice Glb lub (⊓) (⊑) (⊏) (⊔) ⊥ (lattice_top :: 'a::lattice_complete)"
proof (rule class.complete_lattice.intro[OF class.lattice.intro[OF semilattice_meet]])
  show "class.semilattice_sup (⊔) (⊑) ((⊏) :: 'a ⇒ _)"
    by (rule class.semilattice_sup.intro[OF below_order])
      (unfold_locales, simp_all add: joinableD join_belowI)
  show "class.complete_lattice_axioms Glb lub (⊑) ⊥ (lattice_top :: 'a)"
  proof
    show "lub {} = (⊥ :: 'a)" by (rule lub_eqI) simp
  qed (simp_all add: Glb_lower Glb_greatest below_lub lub_below is_ub_def,
       simp add: Glb_def lattice_top_def)
qed

global_interpretation lattice_complete: complete_lattice
  "Glb :: 'a::lattice_complete set ⇒ 'a" lub "(⊓)" "(⊑)" "(⊏)" "(⊔)" ⊥ lattice_top
  by (fact complete_lattice_below)

theorem distrib_lattice_below:
  "class.distrib_lattice (⊓) (⊑) (⊏) ((⊔) :: 'a::{lattice_complete, distributive_cpo} ⇒ _)"
  by (rule class.distrib_lattice.intro[OF class.complete_lattice.axioms(1)[OF complete_lattice_below]])
    (unfold_locales, simp add: join_meet_distrib)

global_interpretation lattice_complete_distrib: distrib_lattice
  "(⊓) :: 'a::{lattice_complete, distributive_cpo} ⇒ _" "(⊑)" "(⊏)" "(⊔)"
  by (fact distrib_lattice_below)

end
