theory Lattice_Complete imports Distributive begin

section \<open>Bounded-complete domains with a top\<close>

text \<open>A bounded-complete pcpo with a top element is a complete lattice under its information
  order: every set is bounded, hence has a lub.  The lattice laws are stated as facts, with the
  join and meet of @{class bounded_complete} as the lattice operations and no joinability side
  conditions.  They are deliberately not interpreted globally: an interpretation copies HOL's
  classical rules into the claset, restated at sort \<open>lattice_complete\<close>, and since
  @{method blast} ignores sorts during search it then tries them at every type (the copy of
  \<open>order_refl [iff]\<close> made an unrelated @{class pcpo}-level blast search for over 1400 s).
  Interpret them in a \<open>context\<close> instead and re-export the lemmas needed.\<close>

class lattice_complete = bounded_complete +
  assumes ex_top: "\<exists>t. \<forall>x. x \<sqsubseteq> t"

definition lattice_top :: "'a::lattice_complete" where
  "lattice_top = lub UNIV"

lemma below_lattice_top [simp]: "x \<sqsubseteq> (lattice_top :: 'a::lattice_complete)"
proof -
  obtain t :: 'a where "\<forall>x. x \<sqsubseteq> t" using ex_top by blast
  then have "UNIV <| t" by (simp add: is_ub_def)
  then have "UNIV <<| lub (UNIV :: 'a set)" by (rule ex_bound_lub)
  then show ?thesis unfolding lattice_top_def by (blast dest: is_lubD1 is_ubD)
qed

lemma is_ub_lattice_top [simp]: "S <| (lattice_top :: 'a::lattice_complete)"
  by (simp add: is_ub_def)

lemma lattice_is_lub: "S <<| lub (S :: 'a::lattice_complete set)"
  by (rule ex_bound_lub[OF is_ub_lattice_top])

lemma joinable_lattice [simp]: "(a :: 'a::lattice_complete) \<Up> b"
  by (rule joinableI[OF below_lattice_top below_lattice_top])

lemma lattice_lub_upper: "x \<in> S \<Longrightarrow> x \<sqsubseteq> lub (S :: 'a::lattice_complete set)"
  by (rule is_ubD[OF is_lubD1[OF lattice_is_lub]])

lemma lattice_lub_least: "S <| b \<Longrightarrow> lub (S :: 'a::lattice_complete set) \<sqsubseteq> b"
  by (rule is_lubD2[OF lattice_is_lub])

text \<open>Every set has a glb, the lub of its lower bounds (also for \<open>{}\<close>, unlike @{thm glb_eq_lub}).\<close>

lemma lattice_is_glb: "is_glb S (lub {x. \<forall>y\<in>S. x \<sqsubseteq> y} :: 'a::lattice_complete)"
  by (rule is_glbI) (auto intro: lattice_lub_least lattice_lub_upper simp: is_ub_def)

lemma lattice_glb_eq_lub: "glb S = lub {x. \<forall>y\<in>S. x \<sqsubseteq> (y :: 'a::lattice_complete)}"
  by (rule glb_eqI[OF lattice_is_glb])

lemma lattice_glb_greatest: "(\<And>y. y \<in> S \<Longrightarrow> b \<sqsubseteq> y) \<Longrightarrow> b \<sqsubseteq> glb (S :: 'a::lattice_complete set)"
  unfolding lattice_glb_eq_lub by (rule lattice_lub_upper) simp

theorem complete_lattice_below:
  "class.complete_lattice glb lub (\<sqinter>) (\<sqsubseteq>) (\<sqsubset>) (\<squnion>) \<bottom> (lattice_top :: 'a::lattice_complete)"
proof (rule class.complete_lattice.intro[OF class.lattice.intro[OF semilattice_meet]])
  show "class.semilattice_sup (\<squnion>) (\<sqsubseteq>) ((\<sqsubset>) :: 'a \<Rightarrow> _)"
    by (rule class.semilattice_sup.intro[OF below_order])
      (unfold_locales, simp_all add: joinableD join_belowI)
  show "class.complete_lattice_axioms glb lub (\<sqsubseteq>) \<bottom> (lattice_top :: 'a)"
  proof
    show "lub {} = (\<bottom> :: 'a)" by (rule lub_eqI) simp
  qed (simp_all add: glb_below lattice_glb_greatest lattice_lub_upper lattice_lub_least is_ub_def,
       simp add: lattice_glb_eq_lub lattice_top_def)
qed

theorem distrib_lattice_below:
  "class.distrib_lattice (\<sqinter>) (\<sqsubseteq>) (\<sqsubset>) ((\<squnion>) :: 'a::{lattice_complete, distributive_cpo} \<Rightarrow> _)"
  by (rule class.distrib_lattice.intro[OF class.complete_lattice.axioms(1)[OF complete_lattice_below]])
    (unfold_locales, simp add: join_meet_distrib)

text \<open>Adjoining a top to a bounded-complete domain makes it a complete lattice.\<close>

instance top :: (bounded_complete) lattice_complete
  by intro_classes (rule exI[of _ Top], simp)

end
