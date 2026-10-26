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

text \<open>The lattice laws needed elsewhere, re-exported from local interpretations under
  \<open>lattice_\<close> names (the interpretations themselves stay local, see above).\<close>

context
begin

interpretation lc: complete_lattice "glb :: 'a::lattice_complete set \<Rightarrow> 'a" lub "(\<sqinter>)" "(\<sqsubseteq>)" "(\<sqsubset>)" "(\<squnion>)" \<bottom> lattice_top
  by (fact complete_lattice_below)

lemmas lattice_join_assoc = lc.sup_assoc
  and lattice_join_commute = lc.sup_commute
  and lattice_join_left_commute = lc.sup_left_commute
  and lattice_join_ge1 = lc.sup_ge1
  and lattice_join_ge2 = lc.sup_ge2
  and lattice_join_least = lc.sup_least
  and lattice_join_mono = lc.sup_mono
  and lattice_join_absorb1 = lc.sup_absorb1
  and lattice_join_absorb2 = lc.sup_absorb2
  and lattice_join_bot_left = lc.sup_bot_left
  and lattice_join_bot_right = lc.sup_bot_right
  and lattice_meet_assoc = lc.inf_assoc
  and lattice_meet_commute = lc.inf_commute
  and lattice_meet_left_commute = lc.inf_left_commute
  and lattice_meet_le1 = lc.inf_le1
  and lattice_meet_le2 = lc.inf_le2
  and lattice_meet_greatest = lc.inf_greatest
  and lattice_meet_mono = lc.inf_mono
  and lattice_meet_absorb1 = lc.inf_absorb1
  and lattice_meet_absorb2 = lc.inf_absorb2
  and lattice_meet_idem = lc.inf_idem
  and lattice_meet_left_idem = lc.inf_left_idem
  and lattice_meet_bot_left = lc.inf_bot_left
  and lattice_meet_bot_right = lc.inf_bot_right
  and lattice_meet_top_left = lc.inf_top_left
  and lattice_meet_join_absorb = lc.inf_sup_absorb
  and lattice_join_meet_absorb = lc.sup_inf_absorb
  and lattice_lub_bot_conv = lc.Sup_bot_conv
  and lattice_join_ac = lc.sup_aci
  and lattice_meet_ac = lc.inf_aci

end

context
begin

interpretation lcd: distrib_lattice "(\<sqinter>)" "(\<sqsubseteq>)" "(\<sqsubset>)" "(\<squnion>) :: 'a::{lattice_complete, distributive_cpo} \<Rightarrow> _"
  by (fact distrib_lattice_below)

lemmas lattice_meet_join_distrib1 = lcd.inf_sup_distrib1
  and lattice_meet_join_distrib2 = lcd.inf_sup_distrib2
  and lattice_join_meet_distrib1 = lcd.sup_inf_distrib1
  and lattice_join_meet_distrib2 = lcd.sup_inf_distrib2

end

text \<open>Adjoining a top to a bounded-complete domain makes it a complete lattice.\<close>

instance top :: (bounded_complete) lattice_complete
  by intro_classes (rule exI[of _ Top], simp)

instance "fun" :: (type, lattice_complete) lattice_complete
  by intro_classes (rule exI[of _ "\<lambda>_. lattice_top"], simp add: fun_below_iff)

instance prod :: (lattice_complete, lattice_complete) lattice_complete
  by intro_classes (rule exI[of _ "(lattice_top, lattice_top)"], simp add: below_prod_def)

lemma lattice_top_prod: "lattice_top = (lattice_top :: 'a::lattice_complete, lattice_top :: 'b::lattice_complete)"
  by (rule below_antisym) (simp add: below_prod_def, rule below_lattice_top)

lemma lattice_join_prod: "x \<squnion> y = (fst x \<squnion> fst y, snd x \<squnion> snd y)"
  for x y :: "'a::lattice_complete \<times> 'b::lattice_complete"
  by (rule prod_join[OF joinable_lattice])

lemma lattice_top_fun: "lattice_top = (\<lambda>_. lattice_top :: 'b::lattice_complete)"
  by (rule below_antisym) (simp add: fun_below_iff, rule below_lattice_top)

lemma fold_join_ge_init: "b \<sqsubseteq> fold (\<squnion>) xs (b::'a::lattice_complete)"
  by (induct xs arbitrary: b) (simp_all, metis lattice_join_ge2 below_trans)

lemma fold_join_upper: "x \<in> set xs \<Longrightarrow> x \<sqsubseteq> fold (\<squnion>) xs (b::'a::lattice_complete)"
proof (induct xs arbitrary: b)
  case (Cons y xs)
  show ?case
  proof (cases "x = y")
    case True
    have "x \<sqsubseteq> x \<squnion> b" by (rule lattice_join_ge1)
    also have "\<dots> \<sqsubseteq> fold (\<squnion>) xs (x \<squnion> b)" by (rule fold_join_ge_init)
    finally show ?thesis using True by simp
  next
    case False
    with Cons show ?thesis by simp
  qed
qed simp

end
