theory LOD
  imports Row "HOLCF-extra.Filter_Sum" "HOLCF-extra.Domain_Order_Derive" Algebraic_Semi_Factor
    "HOL-Library.FSet"
begin

section \<open>Finitary semi-factors and locally finitely detailed domains\<close>

text \<open>A semi-factor is \<^emph>\<open>finitary\<close> when all its elements are compact (equivalently, as a
  subdomain it has finite height): its projection takes every element, however large, to a
  compact one.  Finitary semi-factors are closed under meets (intersection), joins (pointwise
  joins of compacts) and contain the bottom semi-factor.\<close>


default_sort "{bifinite, distributive_cpo}"

text \<open>A domain is \<^emph>\<open>locally finitely detailed\<close> when every compact element lives at some finite
  level of detail, i.e.\ lies in a finitary semi-factor: every finite piece of information has a
  finite, self-contained level.  This is the semi-factor analogue of property I of dI-domains
  (for stable subdomains the least one containing a compact \<open>k\<close> is \<open>\<down>k\<close>, and a distributive lattice of
  finite height is finite), and strictly stronger.  (Compare also Libkin's requirement that the
  compact elements -- the storable objects -- form an ideal.)\<close>

default_sort type

definition finitary :: "('a::pcpo \<rightarrow> 'a) \<Rightarrow> bool" where
  "finitary d \<longleftrightarrow> (\<forall>x. compact (d\<cdot>x))"

definition faithful :: "('a::pcpo \<rightarrow> 'a) \<Rightarrow> bool" where
  "faithful d \<longleftrightarrow> (\<forall>x. d\<cdot>x = \<bottom> \<longrightarrow> x = \<bottom>)"

lemma finitary_bottom: "finitary \<bottom>"
  by (simp add: finitary_def)

text \<open>Over a locally finitely detailed domain with principals the compact semi-factors, which are the levels of
  detail, are finitary (\<open>compact_semi_factor_proj\<close> below).  The constructions act on
  the deflations; @{const semi_factor_of_defl} turns the result back into a semi-factor.\<close>

definition finitary_semi_factor :: "'a::{bifinite, distributive_cpo} semi_factor \<Rightarrow> bool" where
  "finitary_semi_factor F \<longleftrightarrow> finitary (semi_factor_p F)"

lemma ex_finitary_semi_factor_iff:
  fixes k :: "'a::{bifinite, distributive_cpo}"
  shows "(\<exists>F. finitary_semi_factor F \<and> k \<downharpoonright> F = k) \<longleftrightarrow> (\<exists>e. semi_factor_defl e \<and> finitary e \<and> e\<cdot>k = k)"
proof
  assume "\<exists>F. finitary_semi_factor F \<and> k \<downharpoonright> F = k"
  then obtain F where "finitary_semi_factor F" "k \<downharpoonright> F = k" by blast
  then show "\<exists>e. semi_factor_defl e \<and> finitary e \<and> e\<cdot>k = k"
    by (intro exI[of _ "semi_factor_p F"])
      (simp add: semi_factor_defl_semi_factor_p finitary_semi_factor_def)
next
  assume "\<exists>e. semi_factor_defl e \<and> finitary e \<and> e\<cdot>k = k"
  then obtain e where "semi_factor_defl e" "finitary e" "e\<cdot>k = k" by blast
  then show "\<exists>F. finitary_semi_factor F \<and> k \<downharpoonright> F = k"
    by (intro exI[of _ "semi_factor_of_defl e"])
      (simp add: finitary_semi_factor_def semi_factor_p_of_defl)
qed

class locally_finitely_detailed = bifinite + distributive_cpo +
  assumes compact_level: "compact k \<Longrightarrow> \<exists>F. finitary_semi_factor F \<and> k \<downharpoonright> F = k"

text \<open>The domains of rows and keys: locally finitely detailed, with principal semi-factors of
  compacts, hence algebraic semi-factors (@{class principal_semifactor}; dI-domains have them).\<close>

class lod_domain = principal_semifactor + locally_finitely_detailed

subsection \<open>Levels through the constructions\<close>


lemma semi_factor_defl_u_map:
  assumes f: "semi_factor_defl (f :: 'a::{bifinite, distributive_cpo} \<rightarrow> 'a)"
  shows "semi_factor_defl (u_map\<cdot>f)"
proof (rule semi_factor_deflI)
  show "stable_defl (u_map\<cdot>f)" by (rule stable_defl_u_map[OF semi_factor_defl.axioms(1)[OF f]])
  fix x y :: "'a u" assume y: "u_map\<cdot>f\<cdot>y = y" and le: "u_map\<cdot>f\<cdot>x \<sqsubseteq> y"
  show "x \<Up> y"
  proof (cases x)
    case bottom then show ?thesis by (simp add: bottom_joinable)
  next
    case (up a)
    with le obtain b where b: "y = up\<cdot>b" "f\<cdot>a \<sqsubseteq> b" by (cases y) auto
    with y have "f\<cdot>b = b" by simp
    from semi_factor_defl.slide[OF f this b(2)] up b(1) show ?thesis
      by (simp add: cfun_arg_joinable)
  qed
qed

lemma finitary_u_map:
  assumes "finitary f" shows "finitary (u_map\<cdot>f)"
  unfolding finitary_def
proof
  fix x show "compact (u_map\<cdot>f\<cdot>x)"
    using assms unfolding finitary_def by (cases x) (simp_all add: compact_up)
qed

lemma semi_factor_defl_ssum_map:
  assumes f: "semi_factor_defl f" "faithful f" and g: "semi_factor_defl g" "faithful g"
  shows "semi_factor_defl (ssum_map\<cdot>f\<cdot>g)"
proof (rule semi_factor_deflI)
  show "stable_defl (ssum_map\<cdot>f\<cdot>g)"
    by (rule stable_defl_ssum_map[OF semi_factor_defl.axioms(1)[OF f(1)]
          semi_factor_defl.axioms(1)[OF g(1)]])
  fix x y assume y: "ssum_map\<cdot>f\<cdot>g\<cdot>y = y" and le: "ssum_map\<cdot>f\<cdot>g\<cdot>x \<sqsubseteq> y"
  show "x \<Up> y"
  proof (cases x)
    case bottom then show ?thesis by (simp add: bottom_joinable)
  next
    case (sinl a)
    with f(2) have fa: "f\<cdot>a \<noteq> \<bottom>" unfolding faithful_def by blast
    from le sinl fa obtain b where b: "y = sinl\<cdot>b" "b \<noteq> \<bottom>" "f\<cdot>a \<sqsubseteq> b" by (cases y) auto
    with y have "f\<cdot>b = b" by simp
    from semi_factor_defl.slide[OF f(1) this b(3)] sinl b(1) show ?thesis
      by (simp add: cfun_arg_joinable)
  next
    case (sinr a)
    with g(2) have ga: "g\<cdot>a \<noteq> \<bottom>" unfolding faithful_def by blast
    from le sinr ga obtain b where b: "y = sinr\<cdot>b" "b \<noteq> \<bottom>" "g\<cdot>a \<sqsubseteq> b" by (cases y) auto
    with y have "g\<cdot>b = b" by simp
    from semi_factor_defl.slide[OF g(1) this b(3)] sinr b(1) show ?thesis
      by (simp add: cfun_arg_joinable)
  qed
qed

lemma finitary_ssum_map:
  assumes "finitary f" "finitary g" shows "finitary (ssum_map\<cdot>f\<cdot>g)"
  unfolding finitary_def
proof
  fix x show "compact (ssum_map\<cdot>f\<cdot>g\<cdot>x)"
    using assms unfolding finitary_def by (cases x) (simp_all add: compact_sinl compact_sinr)
qed

lemma semi_factor_defl_sprod_map:
  fixes f :: "'a::{bifinite, distributive_cpo, filter_sum} \<rightarrow> 'a"
    and g :: "'b::{bifinite, distributive_cpo, filter_sum} \<rightarrow> 'b"
  assumes f: "semi_factor_defl f" "faithful f" and g: "semi_factor_defl g" "faithful g"
  shows "semi_factor_defl (sprod_map\<cdot>f\<cdot>g)"
proof (rule semi_factor_deflI)
  show "stable_defl (sprod_map\<cdot>f\<cdot>g)"
    by (rule stable_defl_sprod_map[OF semi_factor_defl.axioms(1)[OF f(1)]
          semi_factor_defl.axioms(1)[OF g(1)]])
  fix x y assume y: "sprod_map\<cdot>f\<cdot>g\<cdot>y = y" and le: "sprod_map\<cdot>f\<cdot>g\<cdot>x \<sqsubseteq> y"
  show "x \<Up> y"
  proof (cases x)
    case bottom then show ?thesis by (simp add: bottom_joinable)
  next
    case (spair a b)
    have fa: "f\<cdot>a \<noteq> \<bottom>" "g\<cdot>b \<noteq> \<bottom>" using f(2) g(2) spair unfolding faithful_def by blast+
    from le spair fa obtain c e where c: "y = (:c, e:)" "c \<noteq> \<bottom>" "e \<noteq> \<bottom>" "f\<cdot>a \<sqsubseteq> c" "g\<cdot>b \<sqsubseteq> e"
      by (cases y) (auto simp: spair_below_iff)
    with y have "f\<cdot>c = c" "g\<cdot>e = e" by (auto simp: spair_eq_iff)
    with c have "a \<Up> c" "b \<Up> e"
      by (auto intro: semi_factor_defl.slide[OF f(1)] semi_factor_defl.slide[OF g(1)])
    with spair c show ?thesis by (simp add: spair_joinable_iff)
  qed
qed

lemma finitary_sprod_map:
  assumes "finitary f" "finitary g" shows "finitary (sprod_map\<cdot>f\<cdot>g)"
  unfolding finitary_def
proof
  fix x show "compact (sprod_map\<cdot>f\<cdot>g\<cdot>x)"
    using assms unfolding finitary_def by (cases x) (simp_all add: compact_spair)
qed


subsection \<open>Levels through isomorphisms\<close>

lemma semi_factor_defl_iso:
  fixes abs :: "'r::{bifinite, distributive_cpo} \<rightarrow> 't::{bifinite, distributive_cpo}" and rep
  assumes iso_abs: "\<And>x. rep\<cdot>(abs\<cdot>x) = x" and iso_rep: "\<And>y. abs\<cdot>(rep\<cdot>y) = y"
    and f: "semi_factor_defl f"
  shows "semi_factor_defl (abs oo f oo rep)"
proof (rule semi_factor_deflI)
  have iso: "iso abs rep" by (rule iso.intro[OF iso_abs iso_rep])
  interpret iso abs rep by (fact iso)
  show "stable_defl (abs oo f oo rep)"
    by (rule stable_defl_iso[OF iso_abs iso_rep semi_factor_defl.axioms(1)[OF f]])
  fix x y assume y: "(abs oo f oo rep)\<cdot>y = y" and le: "(abs oo f oo rep)\<cdot>x \<sqsubseteq> y"
  have "rep\<cdot>(abs\<cdot>(f\<cdot>(rep\<cdot>y))) = rep\<cdot>y" using y by simp
  then have fy: "f\<cdot>(rep\<cdot>y) = rep\<cdot>y" by simp
  have "rep\<cdot>((abs oo f oo rep)\<cdot>x) \<sqsubseteq> rep\<cdot>y" using le by (rule monofun_cfun_arg)
  then have "f\<cdot>(rep\<cdot>x) \<sqsubseteq> rep\<cdot>y" by simp
  then have "rep\<cdot>x \<Up> rep\<cdot>y" by (rule semi_factor_defl.slide[OF f fy])
  then show "x \<Up> y" by (simp add: iso_rep_joinable_iff[OF iso])
qed

lemma finitary_iso:
  fixes abs :: "'r::pcpo \<rightarrow> 't::pcpo" and rep
  assumes iso_abs: "\<And>x. rep\<cdot>(abs\<cdot>x) = x" and iso_rep: "\<And>y. abs\<cdot>(rep\<cdot>y) = y"
    and f: "finitary f"
  shows "finitary (abs oo f oo rep)"
proof -
  interpret iso abs rep by (rule iso.intro[OF iso_abs iso_rep])
  show ?thesis using f unfolding finitary_def by (simp add: compact_abs)
qed

text \<open>Finitary deflations are not admissible (the \<open>take\<close> functions converge to \<open>ID\<close>), so they
  get no fixed-point rule; the map and iso rules still derive them through non-recursive types
  (@{thm [source] map_fix_const}).\<close>

lemmas [domain_category_map] = finitary_u_map finitary_ssum_map finitary_sprod_map
lemmas [domain_category_iso] = finitary_iso


subsection \<open>Discriminator for separated sums\<close>

text \<open>In a separated sum every nonbottom element lies above a unique atom.  The discriminator
  sends it there: it is the lub of the step functions \<open>stepfn a a\<close> at the atoms, which are
  compact.  It is a faithful finitary semi-factor deflation, whose image is \<open>\<bottom>\<close> and the atoms.\<close>


definition discriminator :: "'a::{bifinite, bounded_complete, separated_sum} \<rightarrow> 'a"
  where "discriminator = lub {stepfn a a |a. atom a}"

lemma discriminator_bound:
  "{stepfn a a |a. atom a} <| (ID :: 'a::{bifinite, bounded_complete, separated_sum} \<rightarrow> 'a)"
  by (auto intro!: is_ubI simp: stepfn_below_iff atom_compact)

lemma discriminator_app:
  "discriminator\<cdot>x = lub ((\<lambda>a. if a \<sqsubseteq> x then a else \<bottom>) ` {a. atom a})"
proof -
  have S: "{stepfn a a |a. atom a} = (\<lambda>a. stepfn a a) ` {a. atom a}" by blast
  have "(\<lambda>f. f\<cdot>x) ` {stepfn a a |a. atom a} = (\<lambda>a. stepfn a a\<cdot>x) ` {a. atom a}"
    unfolding S image_image ..
  also have "\<dots> = (\<lambda>a. if a \<sqsubseteq> x then a else \<bottom>) ` {a. atom a}"
    by (rule image_cong[OF refl]) (simp add: stepfn_beta[OF atom_compact])
  finally have "(\<lambda>f. f\<cdot>x) ` {stepfn a a |a. atom a} = (\<lambda>a. if a \<sqsubseteq> x then a else \<bottom>) ` {a. atom a}" .
  then show ?thesis
    unfolding discriminator_def cfun_lub[OF discriminator_bound] by simp
qed

lemma discriminator_eq:
  assumes a: "atom a" and ax: "a \<sqsubseteq> x"
  shows "discriminator\<cdot>x = a"
  unfolding discriminator_app
proof (rule lub_eqI, rule is_lubI)
  show "(\<lambda>a. if a \<sqsubseteq> x then a else \<bottom>) ` {a. atom a} <| a"
    by (auto intro!: is_ubI dest: atom_unique[OF _ a _ ax])
next
  fix u assume "(\<lambda>a. if a \<sqsubseteq> x then a else \<bottom>) ` {a. atom a} <| u"
  moreover have "a \<in> (\<lambda>a. if a \<sqsubseteq> x then a else \<bottom>) ` {a. atom a}"
    using a ax by (auto intro!: image_eqI[of _ _ a])
  ultimately show "a \<sqsubseteq> u" by (rule is_ubD)
qed

lemma discriminator_strict [simp]: "discriminator\<cdot>\<bottom> = \<bottom>"
  unfolding discriminator_app
  by (rule lub_eqI) (auto intro!: is_lubI is_ubI dest: atom_nonbottom)

lemma discriminator_atom:
  assumes "x \<noteq> \<bottom>" shows "atom (discriminator\<cdot>x)" and "discriminator\<cdot>x \<sqsubseteq> x"
proof -
  obtain a where "atom a" "a \<sqsubseteq> x" using assms by (rule atom_below)
  then show "atom (discriminator\<cdot>x)" "discriminator\<cdot>x \<sqsubseteq> x" by (simp_all add: discriminator_eq)
qed


lemma discriminator_below: "discriminator\<cdot>x \<sqsubseteq> x"
  by (cases "x = \<bottom>") (simp_all add: discriminator_atom)

lemma discriminator_fixes: "discriminator\<cdot>x = x \<longleftrightarrow> x = \<bottom> \<or> atom x"
  by (metis discriminator_atom(1) discriminator_eq below_refl discriminator_strict)

lemma discriminator_faithful: "faithful discriminator"
  unfolding faithful_def using discriminator_atom atom_nonbottom by blast

lemma discriminator_finitary: "finitary discriminator"
  unfolding finitary_def
  by (metis atom_compact compact_bottom discriminator_atom discriminator_strict)

lemma stable_discriminator: "stable_defl discriminator"
proof standard
  fix x show "discriminator\<cdot>(discriminator\<cdot>x) = discriminator\<cdot>x"
    by (cases "x = \<bottom>") (simp_all add: discriminator_atom discriminator_eq)
next
  fix x show "discriminator\<cdot>x \<sqsubseteq> x" by (rule discriminator_below)
next
  fix x y assume "discriminator\<cdot>y = y" and "x \<sqsubseteq> y"
  then show "discriminator\<cdot>x = x" by (auto simp: discriminator_fixes dest: atomD)
qed

lemma discriminator_semi_factor:
  "semi_factor_defl (discriminator :: 'a::{bifinite, distributive_cpo, separated_sum} \<rightarrow> 'a)"
proof (rule semi_factor_deflI[OF stable_discriminator])
  fix x y :: 'a assume y: "discriminator\<cdot>y = y" and le: "discriminator\<cdot>x \<sqsubseteq> y"
  show "x \<Up> y"
  proof (cases "x = \<bottom>")
    case True then show ?thesis by (simp add: bottom_joinable)
  next
    case False
    note a = discriminator_atom[OF False]
    have "y \<noteq> \<bottom>" using le atom_nonbottom[OF a(1)] by (metis below_bottom_iff)
    with y have "atom y" by (simp add: discriminator_fixes)
    with a(1) le have "discriminator\<cdot>x = y" using atomD atom_nonbottom by blast
    with a(2) have "y \<sqsubseteq> x" by simp
    then show ?thesis by (rule joinableI[OF below_refl])
  qed
qed

lemma discriminator_deflation: "deflation discriminator"
  by (rule stable_defl.deflation[OF stable_discriminator])

text \<open>In a separated sum every nonbottom semi-factor is faithful: an element sent to \<open>\<bottom>\<close> is
  joinable with every image element (slide rule), hence shares an atom with a nonbottom one; the
  atom is in the image (stability), and below the element, so it is sent to \<open>\<bottom>\<close> as well.\<close>

lemma semi_factor_defl_faithful:
  fixes d :: "'a::{bifinite, distributive_cpo, separated_sum} \<rightarrow> 'a"
  assumes d: "semi_factor_defl d" and a: "d\<cdot>a = a" "a \<noteq> \<bottom>"
  shows "faithful d"
  unfolding faithful_def
proof (intro allI impI, rule ccontr)
  interpret D: semi_factor_defl d by (rule d)
  fix x assume dx: "d\<cdot>x = \<bottom>" and x: "x \<noteq> \<bottom>"
  have xa: "x \<Up> a" using a(1) by (rule D.slide) (simp add: dx)
  obtain l where l: "atom l" "l \<sqsubseteq> x" "l \<sqsubseteq> a"
    using separated_sum[OF x a(2) joinableD(1)[OF xa] joinableD(2)[OF xa]] by blast
  have "d\<cdot>l = l" using a(1) l(3) by (rule D.downclosed)
  moreover have "d\<cdot>l \<sqsubseteq> d\<cdot>x" using l(2) by (rule monofun_cfun_arg)
  ultimately have "l = \<bottom>" using dx by simp
  with atom_nonbottom[OF l(1)] show False by contradiction
qed


subsection \<open>Finitary and faithful deflations under joins\<close>

lemma finitary_join:
  fixes p q :: "'a::bounded_complete \<rightarrow> 'a"
  assumes p: "deflation p" and q: "deflation q" and "finitary p" "finitary q"
  shows "finitary (p \<squnion> q)"
  using assms(3,4)
  unfolding finitary_def cfun_join[OF deflation_joinable[OF p q]]
  by (blast intro: compact_join joinableI deflation.below[OF p] deflation.below[OF q])

text \<open>Faithfulness is upward closed, so it passes to joins.\<close>

lemma faithful_mono: "faithful p \<Longrightarrow> p \<sqsubseteq> q \<Longrightarrow> faithful q"
  unfolding faithful_def by (metis monofun_cfun_fun below_bottom_iff)

lemma faithful_joinI1:
  fixes p q :: "'a::bounded_complete \<rightarrow> 'a"
  shows "deflation p \<Longrightarrow> deflation q \<Longrightarrow> faithful p \<Longrightarrow> faithful (p \<squnion> q)"
  by (erule faithful_mono[OF _ joinableD(1)[OF deflation_joinable]])

lemma faithful_joinI2:
  fixes p q :: "'a::bounded_complete \<rightarrow> 'a"
  shows "deflation p \<Longrightarrow> deflation q \<Longrightarrow> faithful q \<Longrightarrow> faithful (p \<squnion> q)"
  by (erule faithful_mono[OF _ joinableD(2)[OF deflation_joinable]])

text \<open>In a separated sum, the faithful deflations are exactly those above the discriminator.\<close>

lemma faithful_iff_discriminator_below:
  fixes d :: "'a::{bifinite, bounded_complete, separated_sum} \<rightarrow> 'a"
  assumes d: "deflation d"
  shows "faithful d \<longleftrightarrow> discriminator \<sqsubseteq> d"
proof
  assume f: "faithful d"
  show "discriminator \<sqsubseteq> d"
  proof (rule cfun_belowI)
    fix x show "discriminator\<cdot>x \<sqsubseteq> d\<cdot>x"
    proof (cases "x = \<bottom>")
      case False
      with f have "d\<cdot>x \<noteq> \<bottom>" unfolding faithful_def by blast
      then obtain a where a: "atom a" "a \<sqsubseteq> d\<cdot>x" by (rule atom_below)
      have "a \<sqsubseteq> x" using a(2) deflation.below[OF d] by (rule below_trans)
      with a show ?thesis by (simp add: discriminator_eq)
    qed simp
  qed
next
  assume "discriminator \<sqsubseteq> d"
  with discriminator_faithful show "faithful d" by (rule faithful_mono)
qed

text \<open>Hence the discriminator lies below every nonbottom semi-factor: it is the only atom of the
  lattice of semi-factors.\<close>

lemma discriminator_below_semi_factor_defl:
  fixes d :: "'a::{bifinite, distributive_cpo, separated_sum} \<rightarrow> 'a"
  assumes d: "semi_factor_defl d" and nz: "d \<noteq> \<bottom>"
  shows "discriminator \<sqsubseteq> d"
proof -
  interpret D: semi_factor_defl d by (rule d)
  from nz obtain x where x: "d\<cdot>x \<noteq> \<bottom>" using cfun_eqI[of d \<bottom>] by auto
  have "faithful d" by (rule semi_factor_defl_faithful[OF d D.idem x])
  then show ?thesis by (simp add: faithful_iff_discriminator_below[OF D.deflation])
qed



subsection \<open>Local finite detail as a deflation predicate\<close>

text \<open>Every compact element of the image is fixed by a finitary level of the whole type.  The
  level is not relative to the image, which makes the predicate admissible for free: a compact
  element fixed by the limit of a chain is fixed at some finite stage.  At \<open>ID\<close> it is
  @{class locally_finitely_detailed}.  The strict combinators need faithful levels of their
  components; these come from the components being separated sums, as a sort constraint.
  Lifting needs nothing.\<close>

locale locally_finitely_detailed_defl = deflation d for d :: "'a::{bifinite, distributive_cpo} \<rightarrow> 'a" +
  assumes level_image: "compact k \<Longrightarrow> d\<cdot>k = k \<Longrightarrow> \<exists>F. finitary_semi_factor F \<and> k \<downharpoonright> F = k"

lemma (in locally_finitely_detailed_defl) deflation: "deflation d" by (fact deflation_axioms)

lemmas (in locally_finitely_detailed_defl) level_image_defl =
  level_image[unfolded ex_finitary_semi_factor_iff]

text \<open>The introduction rule asks for the levels as deflations, which is the form the
  constructions produce.\<close>

lemma locally_finitely_detailed_deflI:
  assumes "deflation d"
    and "\<And>k. compact k \<Longrightarrow> d\<cdot>k = k \<Longrightarrow> \<exists>e. semi_factor_defl e \<and> finitary e \<and> e\<cdot>k = k"
  shows "locally_finitely_detailed_defl d"
  using assms
  by (simp add: locally_finitely_detailed_defl_def locally_finitely_detailed_defl_axioms_def
      ex_finitary_semi_factor_iff)

lemma locally_finitely_detailed_defl_bottom:
  "locally_finitely_detailed_defl (\<bottom> :: 'a::{bifinite, distributive_cpo} \<rightarrow> 'a)"
  by (rule locally_finitely_detailed_deflI[OF deflation_bottom])
    (use semi_factor_defl_bottom finitary_bottom in auto)

lemma locally_finitely_detailed_defl_ID:
  "locally_finitely_detailed_defl (ID :: 'a::locally_finitely_detailed \<rightarrow> 'a)"
  by (rule locally_finitely_detailed_deflI[OF deflation_ID])
    (rule compact_level[unfolded ex_finitary_semi_factor_iff]; simp)

lemma locally_finitely_detailed_class_deflI:
  assumes d: "locally_finitely_detailed_defl (ID :: 'a::{bifinite, distributive_cpo} \<rightarrow> 'a)"
  shows "OFCLASS('a, locally_finitely_detailed_class)"
  by intro_classes
    (rule locally_finitely_detailed_defl.level_image[OF d]; simp)

lemma adm_locally_finitely_detailed_defl:
  "adm (locally_finitely_detailed_defl :: ('a::{bifinite, distributive_cpo} \<rightarrow> 'a) \<Rightarrow> bool)"
proof (rule admI)
  fix Y :: "nat \<Rightarrow> 'a \<rightarrow> 'a" assume Y: "chain Y" and P: "\<forall>i. locally_finitely_detailed_defl (Y i)"
  show "locally_finitely_detailed_defl (\<Squnion>i. Y i)"
  proof (rule locally_finitely_detailed_deflI)
    show "deflation (\<Squnion>i. Y i)"
      by (rule admD[OF adm_deflation Y]) (use P in \<open>simp add: locally_finitely_detailed_defl_def\<close>)
    fix k assume k: "compact k" and fk: "(\<Squnion>i. Y i)\<cdot>k = k"
    have chk: "chain (\<lambda>i. Y i\<cdot>k)" by (rule ch2ch_Rep_cfunL[OF Y])
    have "k \<sqsubseteq> (\<Squnion>i. Y i\<cdot>k)" using fk by (simp add: contlub_cfun_fun[OF Y])
    then obtain n where "k \<sqsubseteq> Y n\<cdot>k" using compactD2[OF k chk] by blast
    then have "Y n\<cdot>k = k"
      using deflation.below[OF locally_finitely_detailed_defl.deflation[OF P[rule_format]]]
      by (rule below_antisym[rotated])
    then show "\<exists>e. semi_factor_defl e \<and> finitary e \<and> e\<cdot>k = k"
      by (rule locally_finitely_detailed_defl.level_image_defl[OF P[rule_format] k])
  qed
qed

lemma locally_finitely_detailed_defl_u_map:
  assumes f: "locally_finitely_detailed_defl (f :: 'a::{bifinite, distributive_cpo} \<rightarrow> 'a)"
  shows "locally_finitely_detailed_defl (u_map\<cdot>f)"
proof (rule locally_finitely_detailed_deflI)
  show "deflation (u_map\<cdot>f)"
    by (rule deflation_u_map[OF locally_finitely_detailed_defl.deflation[OF f]])
  fix k :: "'a u" assume k: "compact k" and fk: "u_map\<cdot>f\<cdot>k = k"
  show "\<exists>e. semi_factor_defl e \<and> finitary e \<and> e\<cdot>k = k"
  proof (cases k)
    case bottom
    then show ?thesis using semi_factor_defl_bottom finitary_bottom by (intro exI[of _ \<bottom>]) simp
  next
    case (up k')
    with k fk have "compact k'" "f\<cdot>k' = k'" by simp_all
    from locally_finitely_detailed_defl.level_image_defl[OF f this] obtain e
      where e: "semi_factor_defl e" "finitary e" "e\<cdot>k' = k'" by blast
    with up show ?thesis
      by (intro exI[of _ "u_map\<cdot>e"]) (simp add: semi_factor_defl_u_map finitary_u_map)
  qed
qed

text \<open>The strict combinators need faithful levels of their components.  A level fixing a
  nonbottom element of a separated sum is faithful (@{thm [source] semi_factor_defl_faithful});
  the branch of a sum not containing the element gets the discriminator.\<close>

lemma locally_finitely_detailed_defl_ssum_map:
  assumes f: "locally_finitely_detailed_defl (f :: 'a::{bifinite, distributive_cpo, separated_sum} \<rightarrow> 'a)"
    and g: "locally_finitely_detailed_defl (g :: 'b::{bifinite, distributive_cpo, separated_sum} \<rightarrow> 'b)"
  shows "locally_finitely_detailed_defl (ssum_map\<cdot>f\<cdot>g)"
proof (rule locally_finitely_detailed_deflI)
  note df = locally_finitely_detailed_defl.deflation[OF f]
    and dg = locally_finitely_detailed_defl.deflation[OF g]
  show "deflation (ssum_map\<cdot>f\<cdot>g)" by (rule deflation_ssum_map[OF df dg])
  note d = discriminator_semi_factor discriminator_finitary discriminator_faithful
  fix k :: "'a \<oplus> 'b" assume k: "compact k" and fk: "ssum_map\<cdot>f\<cdot>g\<cdot>k = k"
  show "\<exists>e. semi_factor_defl e \<and> finitary e \<and> e\<cdot>k = k"
  proof (cases k)
    case bottom
    then show ?thesis using semi_factor_defl_bottom finitary_bottom by (intro exI[of _ \<bottom>]) simp
  next
    case (sinl a)
    with k fk have "compact a" "f\<cdot>a = a" by (simp_all add: deflation_strict[OF df])
    from locally_finitely_detailed_defl.level_image_defl[OF f this] obtain e
      where e: "semi_factor_defl e" "finitary e" "e\<cdot>a = a" by blast
    have "faithful e" using e(1,3) sinl(2) by (rule semi_factor_defl_faithful)
    with sinl e show ?thesis
      by (intro exI[of _ "ssum_map\<cdot>e\<cdot>discriminator"] conjI
          semi_factor_defl_ssum_map finitary_ssum_map d) simp_all
  next
    case (sinr b)
    with k fk have "compact b" "g\<cdot>b = b" by (simp_all add: deflation_strict[OF dg])
    from locally_finitely_detailed_defl.level_image_defl[OF g this] obtain e
      where e: "semi_factor_defl e" "finitary e" "e\<cdot>b = b" by blast
    have "faithful e" using e(1,3) sinr(2) by (rule semi_factor_defl_faithful)
    with sinr e show ?thesis
      by (intro exI[of _ "ssum_map\<cdot>discriminator\<cdot>e"] conjI
          semi_factor_defl_ssum_map finitary_ssum_map d) simp_all
  qed
qed

lemma locally_finitely_detailed_defl_sprod_map:
  assumes f: "locally_finitely_detailed_defl (f :: 'a::{bifinite, distributive_cpo, separated_sum} \<rightarrow> 'a)"
    and g: "locally_finitely_detailed_defl (g :: 'b::{bifinite, distributive_cpo, separated_sum} \<rightarrow> 'b)"
  shows "locally_finitely_detailed_defl (sprod_map\<cdot>f\<cdot>g)"
proof (rule locally_finitely_detailed_deflI)
  note df = locally_finitely_detailed_defl.deflation[OF f]
    and dg = locally_finitely_detailed_defl.deflation[OF g]
  show "deflation (sprod_map\<cdot>f\<cdot>g)" by (rule deflation_sprod_map[OF df dg])
  fix k :: "'a \<otimes> 'b" assume k: "compact k" and fk: "sprod_map\<cdot>f\<cdot>g\<cdot>k = k"
  obtain a b where ab: "k = (:a, b:)" "compact a" "compact b" "f\<cdot>a = a" "g\<cdot>b = b"
  proof (cases k)
    case bottom
    with deflation_strict[OF df] deflation_strict[OF dg] show thesis
      by (intro that[of \<bottom> \<bottom>]) simp_all
  next
    case (spair a b)
    with k fk show thesis
      by (intro that[of a b]) (simp_all add: compact_spair_iff spair_eq_iff
          deflation_strict[OF df] deflation_strict[OF dg])
  qed
  from locally_finitely_detailed_defl.level_image_defl[OF f ab(2,4)] obtain e
    where e: "semi_factor_defl e" "finitary e" "e\<cdot>a = a" by blast
  from locally_finitely_detailed_defl.level_image_defl[OF g ab(3,5)] obtain e'
    where e': "semi_factor_defl e'" "finitary e'" "e'\<cdot>b = b" by blast
  show "\<exists>e. semi_factor_defl e \<and> finitary e \<and> e\<cdot>k = k"
  proof (cases "a = \<bottom> \<or> b = \<bottom>")
    case True
    then have "k = \<bottom>" using ab(1) by auto
    then show ?thesis using semi_factor_defl_bottom finitary_bottom by (intro exI[of _ \<bottom>]) simp
  next
    case False
    then have "faithful e" "faithful e'"
      using semi_factor_defl_faithful[OF e(1,3)] semi_factor_defl_faithful[OF e'(1,3)] by blast+
    with False ab(1) e e' show ?thesis
      by (intro exI[of _ "sprod_map\<cdot>e\<cdot>e'"]) (simp add: semi_factor_defl_sprod_map finitary_sprod_map)
  qed
qed

lemma locally_finitely_detailed_defl_iso:
  fixes abs :: "'r::{bifinite, distributive_cpo} \<rightarrow> 't::{bifinite, distributive_cpo}" and rep
  assumes iso_abs: "\<And>x. rep\<cdot>(abs\<cdot>x) = x" and iso_rep: "\<And>y. abs\<cdot>(rep\<cdot>y) = y"
    and f: "locally_finitely_detailed_defl f"
  shows "locally_finitely_detailed_defl (abs oo f oo rep)"
proof (rule locally_finitely_detailed_deflI)
  have iso: "iso abs rep" by (rule iso.intro[OF iso_abs iso_rep])
  interpret iso abs rep by (fact iso)
  show "deflation (abs oo f oo rep)"
    by (rule deflation_abs_rep[OF abs_iso rep_iso locally_finitely_detailed_defl.deflation[OF f]])
  fix k assume k: "compact k" and fk: "(abs oo f oo rep)\<cdot>k = k"
  have "compact (rep\<cdot>k)" using k by (rule compact_rep)
  moreover have "f\<cdot>(rep\<cdot>k) = rep\<cdot>k"
  proof -
    have "rep\<cdot>(abs\<cdot>(f\<cdot>(rep\<cdot>k))) = rep\<cdot>k" using fk by simp
    then show ?thesis by simp
  qed
  ultimately obtain e where e: "semi_factor_defl e" "finitary e" "e\<cdot>(rep\<cdot>k) = rep\<cdot>k"
    using locally_finitely_detailed_defl.level_image_defl[OF f] by blast
  show "\<exists>e. semi_factor_defl e \<and> finitary e \<and> e\<cdot>k = k"
    using e by (intro exI[of _ "abs oo e oo rep"])
      (simp add: semi_factor_defl_iso[OF iso_abs iso_rep] finitary_iso[OF iso_abs iso_rep])
qed

lemmas [domain_category_adm] = adm_locally_finitely_detailed_defl
lemmas [domain_category_bottom] = locally_finitely_detailed_defl_bottom
lemmas [domain_category_iso] = locally_finitely_detailed_defl_iso
lemmas [domain_category_map] = locally_finitely_detailed_defl_u_map
  locally_finitely_detailed_defl_ssum_map locally_finitely_detailed_defl_sprod_map
lemmas [domain_category_ID] = locally_finitely_detailed_defl_ID
lemmas [domain_category_deflation] = locally_finitely_detailed_defl.deflation
lemmas [domain_category_class] = locally_finitely_detailed_class_deflI

text \<open>The class instances of the strict combinators, from the map rules at \<open>ID\<close>.\<close>

instance ssum :: ("{locally_finitely_detailed, separated_sum}", "{locally_finitely_detailed, separated_sum}")
  locally_finitely_detailed
  by (rule locally_finitely_detailed_class_deflI, subst ssum_map_ID[symmetric],
      rule locally_finitely_detailed_defl_ssum_map; rule locally_finitely_detailed_defl_ID)

instance sprod :: ("{locally_finitely_detailed, separated_sum}", "{locally_finitely_detailed, separated_sum}")
  locally_finitely_detailed
  by (rule locally_finitely_detailed_class_deflI, subst sprod_map_ID[symmetric],
      rule locally_finitely_detailed_defl_sprod_map; rule locally_finitely_detailed_defl_ID)

instance u :: (locally_finitely_detailed) locally_finitely_detailed
  by (rule locally_finitely_detailed_class_deflI, subst u_map_ID[symmetric],
      rule locally_finitely_detailed_defl_u_map, rule locally_finitely_detailed_defl_ID)

text \<open>With finite height the whole domain is a finitary level of detail.  This cannot be a
  subclass statement (\<open>chfin\<close> and \<open>flat\<close> do not entail \<open>bifinite\<close>), but it makes every bifinite
  flat type locally finitely detailed in one line.\<close>

lemma chfin_locally_finitely_detailedI:
  "OFCLASS('a::{chfin, bifinite, distributive_cpo}, locally_finitely_detailed_class)"
  by intro_classes (unfold ex_finitary_semi_factor_iff,
      intro exI[of _ ID], simp add: semi_factor_defl_ID finitary_def)

instance lift :: (countable) locally_finitely_detailed
  by (rule chfin_locally_finitely_detailedI)

subsection \<open>Tuples\<close>

text \<open>Under the isomorphism with families of semi-factors, the finitary semi-factors of the tuples
  are the finitely supported families of finitary semi-factors.\<close>

lemma finitary_semi_factor_of_family:
  fixes F :: "'d::countable \<Rightarrow> 'v::{bifinite, distributive_cpo} semi_factor"
  shows "finitary_semi_factor (semi_factor_of_family F) \<longleftrightarrow>
    finite {d. F d \<noteq> \<bottom>} \<and> (\<forall>d. finitary_semi_factor (F d))"
proof safe
  assume fin: "finitary_semi_factor (semi_factor_of_family F)"
  then have cpt: "compact (t \<downharpoonright> semi_factor_of_family F)" for t
    by (simp add: finitary_semi_factor_def finitary_def)
  show "finitary_semi_factor (F d)" for d
    unfolding finitary_semi_factor_def finitary_def
  proof
    fix x
    have "compact ((tupd d\<cdot>\<bottom>\<cdot>x \<downharpoonright> semi_factor_of_family F)\<langle>d\<rangle>)" by (rule compact_tget[OF cpt])
    then show "compact (x \<downharpoonright> F d)" by (simp add: tupd_bot_tget)
  qed
  show "finite {d. F d \<noteq> \<bottom>}"
  proof (rule ccontr)
    assume inf: "infinite {d. F d \<noteq> \<bottom>}"
    have "\<exists>x. x \<downharpoonright> F d \<noteq> \<bottom>" if "F d \<noteq> \<bottom>" for d
    proof (rule ccontr)
      assume "\<nexists>x. x \<downharpoonright> F d \<noteq> \<bottom>"
      then have "semi_factor_p (F d) = semi_factor_p \<bottom>" by (simp add: cfun_eq_iff semi_factor_p_bot)
      with that show False by (simp add: semi_factor_p_inject)
    qed
    then obtain x where x: "\<And>d. F d \<noteq> \<bottom> \<Longrightarrow> x d \<downharpoonright> F d \<noteq> \<bottom>" by metis
    define t :: "('d, 'v) tuple" where "t = Abs_tuple x"
    have "{d. F d \<noteq> \<bottom>} \<subseteq> tsupp (t \<downharpoonright> semi_factor_of_family F)"
      using x by (auto simp: tsupp_def t_def Abs_tuple_inverse')
    with inf compact_finite_tsupp[OF cpt] show False by (metis finite_subset)
  qed
next
  assume fin: "finite {d. F d \<noteq> \<bottom>}" and F: "\<forall>d. finitary_semi_factor (F d)"
  show "finitary_semi_factor (semi_factor_of_family F)"
    unfolding finitary_semi_factor_def finitary_def
  proof
    fix t show "compact (t \<downharpoonright> semi_factor_of_family F)"
    proof (rule compact_tupleI)
      have "tsupp (t \<downharpoonright> semi_factor_of_family F) \<subseteq> {d. F d \<noteq> \<bottom>}"
        by (auto simp: tsupp_def semi_factor_p_bot)
      then show "finite (tsupp (t \<downharpoonright> semi_factor_of_family F))" using fin by (rule finite_subset)
      show "compact ((t \<downharpoonright> semi_factor_of_family F)\<langle>d\<rangle>)" for d
        using F by (simp add: finitary_semi_factor_def finitary_def)
    qed
  qed
qed

text \<open>A compact tuple has finite support and compact components.  A finitary level containing
  it is the family of finitary levels containing the components on its support, and \<open>\<bottom>\<close>
  elsewhere.\<close>

instance tuple :: (countable, locally_finitely_detailed) locally_finitely_detailed
proof
  fix K :: "('a, 'b) tuple" assume K: "compact K"
  define F where "F d = (if d \<in> tsupp K
      then (SOME G. finitary_semi_factor G \<and> K\<langle>d\<rangle> \<downharpoonright> G = K\<langle>d\<rangle>) else \<bottom>)" for d
  have F: "finitary_semi_factor (F d) \<and> K\<langle>d\<rangle> \<downharpoonright> F d = K\<langle>d\<rangle>" for d
  proof (cases "d \<in> tsupp K")
    case True
    then show ?thesis using someI_ex[OF compact_level[OF compact_tget[OF K, of d]]]
      by (simp add: F_def)
  next
    case False
    then show ?thesis
      by (simp add: F_def tsupp_def finitary_semi_factor_def finitary_def semi_factor_p_bot)
  qed
  have "{d. F d \<noteq> \<bottom>} \<subseteq> tsupp K" by (auto simp: F_def)
  then have "finite {d. F d \<noteq> \<bottom>}" using compact_finite_tsupp[OF K] by (rule finite_subset)
  with F have "finitary_semi_factor (semi_factor_of_family F)"
    by (simp add: finitary_semi_factor_of_family)
  moreover have "K \<downharpoonright> semi_factor_of_family F = K" using F by (simp add: tuple_eq_iff)
  ultimately show "\<exists>G. finitary_semi_factor G \<and> K \<downharpoonright> G = K" by blast
qed

section \<open>Projections onto semi-factors\<close>

text \<open>Levels of detail are compact semi-factors of the key domain, acting on keys by projection;
  masks are arbitrary semi-factors.  The facts are stated for all semi-factors, with compactness
  of the semi-factor (and keys of class @{class lod_domain}) where compactness of keys is needed.
  (They took over the names of the facts of the retired locale \<open>lod_space\<close>.)\<close>

abbreviation proj :: "'k::{bifinite, distributive_cpo} semi_factor \<Rightarrow> 'k \<rightarrow> 'k" where
  "proj \<equiv> semi_factor_p"

subsection \<open>Compact semi-factors project to compact keys\<close>

text \<open>With principal semi-factors every compact semi-factor is a finite join of principals of compacts
  (@{thm [source] compact_semi_factor_finite_join}).  Over a locally finitely detailed one the
  principal of a compact lies below a semi-factor all of whose elements are compact, and finite
  joins keep that property.  So compact semi-factors project every key to a compact one.
  (Without local finite detail this fails: in the separated sum of the powerset of the naturals
  and a point, the principal of the point is the whole domain.)  Projections of compact keys are
  compact as well: a compact key lives at its principal, whose projections are compact.\<close>

lemma compact_finite_lub:
  fixes u :: "'a::cpo"
  assumes fin: "finite C" and comp: "\<And>c. c \<in> C \<Longrightarrow> compact c" and lub: "C <<| u"
  shows "compact u"
proof (rule compactI2)
  fix Y :: "nat \<Rightarrow> 'a" assume Y: "chain Y" and uY: "u \<sqsubseteq> (\<Squnion>i. Y i)"
  have "\<exists>i. c \<sqsubseteq> Y i" if "c \<in> C" for c
    by (rule compactD2[OF comp[OF that] Y])
      (rule below_trans[OF is_ubD[OF is_lubD1[OF lub] that] uY])
  then obtain f where f: "\<And>c. c \<in> C \<Longrightarrow> c \<sqsubseteq> Y (f c)" by metis
  let ?n = "Max (insert 0 (f ` C))"
  have "c \<sqsubseteq> Y ?n" if "c \<in> C" for c
    by (rule below_trans[OF f[OF that] chain_mono[OF Y]]) (simp add: fin that)
  then have "u \<sqsubseteq> Y ?n" by (intro is_lubD2[OF lub] is_ubI)
  then show "\<exists>i. u \<sqsubseteq> Y i" by blast
qed

lemma compact_proj_below:
  assumes "F \<sqsubseteq> G" and "\<And>y. compact (y \<downharpoonright> G)"
  shows "compact (x \<downharpoonright> F)"
  by (metis assms semi_factor_p_mono stable_defl.lower_fixed[OF stable_defl_semi_factor_p])

lemma compact_proj_lub:
  assumes "finite \<A>" and "\<And>F y. F \<in> \<A> \<Longrightarrow> compact (y \<downharpoonright> F)"
  shows "compact (x \<downharpoonright> lub \<A>)"
  by (rule compact_finite_lub[OF _ _ semi_factor_p_lub_is_lub]) (use assms in auto)

lemma compact_proj_principal:
  fixes k :: "'a::lod_domain"
  assumes "compact k"
  shows "compact (x \<downharpoonright> semi_factor_principal k)"
proof -
  obtain F where F: "finitary_semi_factor F" "k \<downharpoonright> F = k" using compact_level[OF assms] by blast
  have "semi_factor_principal k \<sqsubseteq> F" using F(2) by (simp add: semi_factor_principal_below_iff)
  then show ?thesis
    by (rule compact_proj_below) (use F(1) in \<open>simp add: finitary_semi_factor_def finitary_def\<close>)
qed

theorem compact_semi_factor_proj:
  fixes K :: "'a::lod_domain semi_factor"
  assumes "compact K"
  shows "compact (x \<downharpoonright> K)"
proof -
  obtain A where A: "finite A" "A \<subseteq> {k. compact k}" "K = lub (semi_factor_principal ` A)"
    using compact_semi_factor_finite_join[OF assms] by blast
  show ?thesis unfolding A(3)
    by (rule compact_proj_lub) (use A(1,2) in \<open>auto intro: compact_proj_principal\<close>)
qed

lemma compact_proj_compact:
  fixes F :: "'a::lod_domain semi_factor"
  assumes k: "compact k"
  shows "compact (k \<downharpoonright> F)"
proof -
  let ?P = "semi_factor_principal k"
  have "k \<downharpoonright> F = (k \<downharpoonright> ?P) \<downharpoonright> F" by (simp only: semi_factor_principal_self)
  also have "\<dots> = k \<downharpoonright> (?P \<sqinter> F)" by (rule semi_factor_proj_comp)
  finally show ?thesis
    by (simp only:) (rule compact_proj_below[OF lattice_meet_le1 compact_proj_principal[OF k]])
qed

lemma proj_inf: "proj (a \<sqinter> b)\<cdot>k = proj a\<cdot>(proj b\<cdot>k)"
  by (simp add: semi_factor_proj_comp lattice_meet_commute)

lemma proj_sup: "proj (a \<squnion> b)\<cdot>k = proj a\<cdot>k \<squnion> proj b\<cdot>k"
  by (rule semi_factor_p_sup)

lemma proj_bot: "proj \<bottom> = \<bottom>"
  by (rule semi_factor_p_bot)

lemma compact_semi_factor_sup:
  "compact a \<Longrightarrow> compact b \<Longrightarrow> compact (a \<squnion> b :: 'k::{bifinite, distributive_cpo} semi_factor)"
  by (simp add: compact_join)

lemma compact_fold_sup:
  "(\<And>x. x \<in> set xs \<Longrightarrow> compact x) \<Longrightarrow> compact b
    \<Longrightarrow> compact (fold (\<squnion>) xs b :: 'k::{bifinite, distributive_cpo} semi_factor)"
  by (induct xs arbitrary: b) (simp_all add: compact_semi_factor_sup)

lemma proj_defl: "deflation (proj a)"
  by (rule deflation_semi_factor_p)

lemma proj_slide: "proj a\<cdot>y = y \<Longrightarrow> proj a\<cdot>x \<sqsubseteq> y \<Longrightarrow> x \<Up> y"
  by (rule semi_factor_defl.slide[OF semi_factor_defl_semi_factor_p])

lemma proj_compact: "compact a \<Longrightarrow> compact (proj a\<cdot>k)"
  for a :: "'k::lod_domain semi_factor"
  by (rule compact_semi_factor_proj)

lemma compact_lives: "compact k \<Longrightarrow> \<exists>c. compact c \<and> proj c\<cdot>k = k" for k :: "'k::principal_semifactor"
  by (blast intro: compact_semi_factor_principal semi_factor_principal_self)

lemma proj_join: "x \<Up> y \<Longrightarrow> proj a\<cdot>(x \<squnion> y) = proj a\<cdot>x \<squnion> proj a\<cdot>y"
  by (rule stable_defl_image_join[OF stable_defl_semi_factor_p])

lemma proj_downclosed: "proj a\<cdot>y = y \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> proj a\<cdot>x = x"
  by (rule stable_defl.downclosed[OF stable_defl_semi_factor_p])


lemma proj_below: "proj a\<cdot>k \<sqsubseteq> k"
  by (rule deflation.below[OF proj_defl])

lemma proj_idem [simp]: "proj a\<cdot>(proj a\<cdot>k) = proj a\<cdot>k"
  by (rule deflation.idem[OF proj_defl])

lemma proj_commute: "proj a\<cdot>(proj b\<cdot>k) = proj b\<cdot>(proj a\<cdot>k)"
  by (simp only: proj_inf[symmetric] lattice_meet_commute)

lemma proj_le: "a \<sqsubseteq> b \<Longrightarrow> proj a\<cdot>(proj b\<cdot>k) = proj a\<cdot>k"
  by (simp only: proj_inf[symmetric] lattice_meet_absorb1)

lemma proj_mono: "a \<sqsubseteq> b \<Longrightarrow> proj a\<cdot>k \<sqsubseteq> proj b\<cdot>k"
  by (metis proj_le proj_below)

subsection \<open>Where a key lives\<close>

definition lives_at :: "'k::{bifinite, distributive_cpo} semi_factor \<Rightarrow> 'k \<Rightarrow> bool" where
  "lives_at c k \<longleftrightarrow> proj c\<cdot>k = k"

text \<open>The LODs a key lives at form a filter, non-empty exactly for compact keys.\<close>

definition lods_of :: "'k::{bifinite, distributive_cpo} \<Rightarrow> 'k semi_factor set" where
  "lods_of k = {c. lives_at c k}"

lemma lives_at_up: "lives_at c k \<Longrightarrow> c \<sqsubseteq> c' \<Longrightarrow> lives_at c' k"
  unfolding lives_at_def by (metis proj_le proj_commute)

lemma lives_at_inf: "lives_at c k \<Longrightarrow> lives_at c' k \<Longrightarrow> lives_at (c \<sqinter> c') k"
  unfolding lives_at_def by (simp add: proj_inf)

lemma lives_at_proj: "lives_at a (proj a\<cdot>k)"
  unfolding lives_at_def by simp

lemma compact_iff_lives: "compact k \<longleftrightarrow> (\<exists>c. compact c \<and> lives_at c k)"
  for k :: "'k::lod_domain"
  unfolding lives_at_def by (metis compact_lives proj_compact)

lemma lods_of_nonempty: "compact k \<Longrightarrow> lods_of k \<noteq> {}" for k :: "'k::principal_semifactor"
  unfolding lods_of_def lives_at_def using compact_lives by blast

text \<open>Projection keeps maximal keys maximal among the keys living at the LOD.\<close>

lemma proj_maximal:
  assumes max: "\<And>y. x \<sqsubseteq> y \<Longrightarrow> y = x" and t: "lives_at a t" and le: "proj a\<cdot>x \<sqsubseteq> t"
  shows "t \<sqsubseteq> proj a\<cdot>x"
proof -
  from t have tt: "proj a\<cdot>t = t" by (simp add: lives_at_def)
  from proj_slide[OF tt le] have j: "x \<Up> t" .
  then have "x \<squnion> t = x" by (intro max) (rule joinableD(1))
  then have "t \<sqsubseteq> x" using joinableD(2)[OF j] by simp
  then have "proj a\<cdot>t \<sqsubseteq> proj a\<cdot>x" by (rule monofun_cfun_arg)
  then show ?thesis by (simp add: tt)
qed

subsection \<open>Keys maximal at an LOD\<close>

definition maximal_at :: "'k::{bifinite, distributive_cpo} semi_factor \<Rightarrow> 'k \<Rightarrow> bool" where
  "maximal_at c k \<longleftrightarrow> proj c\<cdot>k = k \<and> (\<forall>t. proj c\<cdot>t = t \<longrightarrow> k \<sqsubseteq> t \<longrightarrow> t = k)"

text \<open>Maximality passes down to coarser LODs: anything above the projection at the coarser LOD
  slides into a join with the key, which lives at the finer LOD and so cannot exceed it.\<close>

lemma maximal_at_proj:
  assumes ab: "a \<sqsubseteq> b" and k: "maximal_at b k"
  shows "maximal_at a (proj a\<cdot>k)"
  unfolding maximal_at_def
proof (intro conjI allI impI)
  show "proj a\<cdot>(proj a\<cdot>k) = proj a\<cdot>k" by simp
  fix t assume t: "proj a\<cdot>t = t" and le: "proj a\<cdot>k \<sqsubseteq> t"
  have kb: "proj b\<cdot>k = k" using k by (simp add: maximal_at_def)
  have tb: "proj b\<cdot>t = t" using t lives_at_up[OF _ ab] by (simp add: lives_at_def)
  have j: "k \<Up> t" by (rule proj_slide[OF t le])
  have "proj b\<cdot>(k \<squnion> t) = k \<squnion> t" by (simp add: proj_join[OF j] kb tb)
  then have "k \<squnion> t = k" using k joinableD(1)[OF j] by (simp add: maximal_at_def)
  then have "t \<sqsubseteq> k" using joinableD(2)[OF j] by simp
  then have "t \<sqsubseteq> proj a\<cdot>k" using monofun_cfun_arg[of t k "proj a"] by (simp add: t)
  with le show "t = proj a\<cdot>k" by (rule below_antisym[rotated])
qed

lemma maximal_at_lives: "maximal_at c k \<Longrightarrow> proj c\<cdot>k = k"
  by (simp add: maximal_at_def)

lemma maximal_at_compact: "maximal_at c k \<Longrightarrow> compact c \<Longrightarrow> compact k"
  for c :: "'k::lod_domain semi_factor"
  by (metis maximal_at_lives proj_compact)

text \<open>A key below one living at the same LOD is that key, when it is maximal there.\<close>

lemma maximal_at_eq: "maximal_at c k \<Longrightarrow> proj c\<cdot>t = t \<Longrightarrow> k \<sqsubseteq> t \<Longrightarrow> t = k"
  by (simp add: maximal_at_def)

text \<open>Joins of compatible maximal keys are maximal at the join of their LODs.\<close>

lemma maximal_at_join:
  assumes a: "maximal_at A a" and b: "maximal_at B b" and j: "a \<Up> b"
  shows "maximal_at (A \<squnion> B) (a \<squnion> b)"
  unfolding maximal_at_def
proof (intro conjI allI impI)
  have aA: "proj A\<cdot>a = a" and bB: "proj B\<cdot>b = b" using a b by (simp_all add: maximal_at_def)
  have pa: "proj A\<cdot>(a \<squnion> b) = a"
  proof -
    have "proj A\<cdot>a \<sqsubseteq> proj A\<cdot>(a \<squnion> b)" using joinableD(1)[OF j] by (rule monofun_cfun_arg)
    then have "a \<sqsubseteq> proj A\<cdot>(a \<squnion> b)" by (simp only: aA)
    then show ?thesis using a by (simp add: maximal_at_def)
  qed
  have pb: "proj B\<cdot>(a \<squnion> b) = b"
  proof -
    have "proj B\<cdot>b \<sqsubseteq> proj B\<cdot>(a \<squnion> b)" using joinableD(2)[OF j] by (rule monofun_cfun_arg)
    then have "b \<sqsubseteq> proj B\<cdot>(a \<squnion> b)" by (simp only: bB)
    then show ?thesis using b by (simp add: maximal_at_def)
  qed
  show "proj (A \<squnion> B)\<cdot>(a \<squnion> b) = a \<squnion> b" by (simp only: proj_sup pa pb)
  fix t assume t: "proj (A \<squnion> B)\<cdot>t = t" and le: "a \<squnion> b \<sqsubseteq> t"
  have at: "a \<sqsubseteq> t" and bt: "b \<sqsubseteq> t" using le joinableD[OF j] by (blast intro: below_trans)+
  have "proj A\<cdot>t = a"
  proof -
    have "a \<sqsubseteq> proj A\<cdot>t" using monofun_cfun_arg[OF at, of "proj A"] by (simp add: aA)
    then show ?thesis using a by (simp add: maximal_at_def)
  qed
  moreover have "proj B\<cdot>t = b"
  proof -
    have "b \<sqsubseteq> proj B\<cdot>t" using monofun_cfun_arg[OF bt, of "proj B"] by (simp add: bB)
    then show ?thesis using b by (simp add: maximal_at_def)
  qed
  ultimately show "t = a \<squnion> b" using t by (simp add: proj_sup)
qed

text \<open>A key maximal at \<open>a\<close> that has a common upper bound with \<open>K\<close> lies above the projection of
  \<open>K\<close>: the projection of their join is above the key, hence equal to it.  (Under a pinning slicer,
  conformity provides the common upper bound.)\<close>

lemma proj_below_maximal:
  assumes K1: "maximal_at a K1" and KK2: "K \<sqsubseteq> K2" and K1K2: "K1 \<sqsubseteq> K2"
  shows "proj a\<cdot>K \<sqsubseteq> K1"
proof -
  have j: "K \<Up> K1" by (rule joinableI[OF KK2 K1K2])
  have "proj a\<cdot>K1 \<sqsubseteq> proj a\<cdot>(K \<squnion> K1)" using joinableD(2)[OF j] by (rule monofun_cfun_arg)
  then have "K1 \<sqsubseteq> proj a\<cdot>(K \<squnion> K1)" using K1 by (simp add: maximal_at_def)
  then have eq: "proj a\<cdot>(K \<squnion> K1) = K1" using K1 by (simp add: maximal_at_def)
  have "proj a\<cdot>K \<sqsubseteq> proj a\<cdot>(K \<squnion> K1)" using joinableD(1)[OF j] by (rule monofun_cfun_arg)
  then show ?thesis by (simp only: eq)
qed

text \<open>Round trip between two LODs that agree up to the LOD of a pinned key: from a key \<open>K1\<close> at
  \<open>a\<close> compatible with the pin, go to \<open>a'\<close> through the join with the pin, and back.\<close>

lemma proj_round_trip:
  assumes aL: "a \<squnion> L = a' \<squnion> L" and K: "maximal_at L K"
    and K1: "proj a\<cdot>K1 = K1" and le: "proj a\<cdot>K \<sqsubseteq> K1"
  shows "proj a\<cdot>(proj a'\<cdot>(K1 \<squnion> K) \<squnion> K) = K1"
proof -
  have j: "K1 \<Up> K" using proj_slide[OF K1 le] by (simp add: joinable_sym)
  let ?J = "K1 \<squnion> K"
  have JK: "K \<sqsubseteq> ?J" using j by (rule joinableD)
  have jJ: "proj a'\<cdot>?J \<Up> K" by (rule joinableI[OF proj_below JK])
  have KL: "proj L\<cdot>K = K" using K by (simp add: maximal_at_def)
  have LJ: "proj L\<cdot>?J = K"
  proof -
    have "proj L\<cdot>K \<sqsubseteq> proj L\<cdot>?J" using JK by (rule monofun_cfun_arg)
    then have "K \<sqsubseteq> proj L\<cdot>?J" by (simp only: KL)
    then show ?thesis using K by (simp add: maximal_at_def)
  qed
  have a_split: "a = (a \<sqinter> a') \<squnion> (a \<sqinter> L)"
    by (metis aL lattice_meet_join_absorb lattice_meet_join_distrib1)
  have "proj a\<cdot>?J = proj (a \<sqinter> a')\<cdot>?J \<squnion> proj a\<cdot>K"
    by (subst a_split) (simp add: proj_sup proj_inf LJ)
  moreover have "proj a\<cdot>?J = K1"
    by (simp add: proj_join[OF j] K1 join_absorb2[OF le])
  ultimately have "K1 = proj (a \<sqinter> a')\<cdot>?J \<squnion> proj a\<cdot>K" by simp
  then show ?thesis by (simp add: proj_join[OF jJ] proj_inf)
qed


subsection \<open>Masks\<close>

text \<open>A \<^emph>\<open>mask\<close> is a semi-factor, possibly non-compact, acting on LODs by meet: truncating an LOD
  to a mask keeps the part of it within the mask.  (This replaces an abstract type of
  truncations, i.e. of maps obeying \<open>\<tau> (x \<sqinter> y) = x \<sqinter> \<tau> y\<close>, which on a complete lattice
  are exactly the meets with a fixed element.)\<close>

lemma truncate_inf: "\<tau> \<sqinter> (x \<sqinter> y) = x \<sqinter> (\<tau> \<sqinter> y)" for \<tau> :: "'l::lattice_complete"
  by (rule lattice_meet_left_commute)

context
  fixes \<tau> :: "'l::{lattice_complete, distributive_cpo}"
begin

lemma truncate_below: "(\<tau> \<sqinter> x) \<sqsubseteq> x"
  by (rule lattice_meet_le2)

lemma truncate_idem: "(\<tau> \<sqinter> (\<tau> \<sqinter> x)) = (\<tau> \<sqinter> x)"
  by (rule lattice_meet_left_idem)

lemma truncate_mono: "x \<sqsubseteq> y \<Longrightarrow> (\<tau> \<sqinter> x) \<sqsubseteq> (\<tau> \<sqinter> y)"
  by (rule lattice_meet_mono[OF below_refl])

lemma truncate_inf_hom: "(\<tau> \<sqinter> (x \<sqinter> y)) = (\<tau> \<sqinter> x) \<sqinter> (\<tau> \<sqinter> y)"
  by (simp add: lattice_meet_ac)

lemma truncate_sup: "(\<tau> \<sqinter> (x \<squnion> y)) = (\<tau> \<sqinter> x) \<squnion> (\<tau> \<sqinter> y)"
  by (rule lattice_meet_join_distrib1)

lemma truncate_bot: "(\<tau> \<sqinter> \<bottom>) = \<bottom>"
  by (rule lattice_meet_bot_right)

lemma truncate_fix_down: "(\<tau> \<sqinter> c) = c \<Longrightarrow> d \<sqsubseteq> c \<Longrightarrow> (\<tau> \<sqinter> d) = d"
  by (metis lattice_meet_absorb2 lattice_meet_le1 below_trans)

lemma truncate_fix_sup: "(\<tau> \<sqinter> c) = c \<Longrightarrow> (\<tau> \<sqinter> d) = d \<Longrightarrow> (\<tau> \<sqinter> (c \<squnion> d)) = c \<squnion> d"
  by (simp add: truncate_sup)

lemma truncate_greatest: "(\<tau> \<sqinter> c) = c \<Longrightarrow> c \<sqsubseteq> x \<Longrightarrow> c \<sqsubseteq> (\<tau> \<sqinter> x)"
  by (metis truncate_mono)

text \<open>Within \<open>a\<close>, truncating more than \<open>a\<close> is truncating \<open>a\<close>.\<close>

lemma truncate_inf_sup: "(\<tau> \<sqinter> (a \<squnion> b)) \<sqinter> a = (\<tau> \<sqinter> a)"
  by (metis lattice_meet_assoc lattice_meet_commute lattice_meet_join_absorb)

end

lemma truncate_inf_comp: "(\<rho> \<sqinter> \<tau>) \<sqinter> x = \<rho> \<sqinter> (\<tau> \<sqinter> x)" for x :: "'l::lattice_complete"
  by (rule lattice_meet_assoc)

lemma truncate_top: "lattice_top \<sqinter> x = x" for x :: "'l::lattice_complete"
  by (rule lattice_meet_top_left)

lemma truncate_bot_trunc: "\<bottom> \<sqinter> x = \<bottom>" for x :: "'l::lattice_complete"
  by (rule lattice_meet_bot_left)

subsection \<open>Masks acting on keys\<close>

text \<open>A mask acts on keys by projection, through any LOD the key lives at.\<close>

lemma truncate_proj_irrelevant:
  assumes c: "lives_at c k" and c': "lives_at c' k"
  shows "proj ((\<tau> \<sqinter> c))\<cdot>k = proj ((\<tau> \<sqinter> c'))\<cdot>k"
proof -
  have e: "(\<tau> \<sqinter> c) \<sqinter> c' = (\<tau> \<sqinter> c') \<sqinter> c" by (metis truncate_inf lattice_meet_commute)
  have "proj ((\<tau> \<sqinter> c))\<cdot>k = proj ((\<tau> \<sqinter> c))\<cdot>(proj c'\<cdot>k)" using c' by (simp add: lives_at_def)
  also have "\<dots> = proj ((\<tau> \<sqinter> c) \<sqinter> c')\<cdot>k" by (simp only: proj_inf)
  also have "\<dots> = proj ((\<tau> \<sqinter> c') \<sqinter> c)\<cdot>k" by (simp only: e)
  also have "\<dots> = proj ((\<tau> \<sqinter> c'))\<cdot>(proj c\<cdot>k)" by (simp only: proj_inf)
  also have "\<dots> = proj ((\<tau> \<sqinter> c'))\<cdot>k" using c by (simp add: lives_at_def)
  finally show ?thesis .
qed

definition truncate_key :: "'k::{bifinite, distributive_cpo} semi_factor \<Rightarrow> 'k \<Rightarrow> 'k" where
  "truncate_key \<tau> k = proj \<tau>\<cdot>k"

lemma truncate_key_eq:
  assumes c: "lives_at c k"
  shows "truncate_key \<tau> k = proj ((\<tau> \<sqinter> c))\<cdot>k"
  using c by (simp add: truncate_key_def proj_inf lives_at_def)

subsection \<open>Compact maps\<close>

text \<open>A map into a pcpo is compact in the pointwise order exactly when it has finite support and
  compact values.\<close>

lemma compact_fun_iff:
  fixes f :: "'a \<Rightarrow> 'b::pcpo"
  shows "compact f \<longleftrightarrow> finite {x. f x \<noteq> \<bottom>} \<and> (\<forall>x. compact (f x))"
proof
  assume c: "compact f"
  have "compact (f x)" for x
  proof (rule compactI2)
    fix C :: "nat \<Rightarrow> 'b" assume C: "chain C" and le: "f x \<sqsubseteq> (\<Squnion>i. C i)"
    let ?Y = "\<lambda>i. f(x := C i)"
    have Y: "chain ?Y" by (rule chainI, rule fun_belowI) (simp add: chainE[OF C])
    have "f \<sqsubseteq> (\<Squnion>i. ?Y i)"
    proof (rule fun_belowI)
      fix y show "f y \<sqsubseteq> (\<Squnion>i. ?Y i) y" by (cases "y = x") (simp_all add: lub_fun[OF Y] le)
    qed
    then obtain i where "f \<sqsubseteq> ?Y i" using compactD2[OF c Y] by blast
    then show "\<exists>i. f x \<sqsubseteq> C i" by (metis fun_belowD fun_upd_same)
  qed
  moreover have "finite {x. f x \<noteq> \<bottom>}"
  proof (rule ccontr)
    assume "infinite {x. f x \<noteq> \<bottom>}"
    then obtain g :: "nat \<Rightarrow> 'a" where g: "inj g" "range g \<subseteq> {x. f x \<noteq> \<bottom>}"
      using infinite_countable_subset by blast
    let ?Y = "\<lambda>n y. if y \<in> g ` {n..} then \<bottom> else f y"
    have Y: "chain ?Y"
    proof (rule chainI, rule fun_belowI)
      fix n y show "?Y n y \<sqsubseteq> ?Y (Suc n) y" by (cases "y \<in> g ` {n..}") auto
    qed
    have "f \<sqsubseteq> (\<Squnion>n. ?Y n)"
    proof (rule fun_belowI)
      fix y
      obtain n where n: "y \<notin> g ` {n..}"
      proof (cases "y \<in> range g")
        case True
        then obtain k where "y = g k" by blast
        then have "y \<notin> g ` {Suc k..}" using g(1) by (auto simp: inj_eq)
        then show ?thesis by (rule that)
      next
        case False
        then show ?thesis by (intro that[of 0]) auto
      qed
      then have "f y = ?Y n y" by simp
      also have "\<dots> \<sqsubseteq> (\<Squnion>n. ?Y n y)" by (rule is_ub_thelub[OF ch2ch_fun[OF Y]])
      finally show "f y \<sqsubseteq> (\<Squnion>n. ?Y n) y" by (simp add: lub_fun[OF Y])
    qed
    then obtain n where "f \<sqsubseteq> ?Y n" using compactD2[OF c Y] by blast
    then have "f (g n) \<sqsubseteq> \<bottom>" using fun_belowD[of f "?Y n" "g n"] by simp
    then have "f (g n) = \<bottom>" by (rule bottomI)
    with g(2) show False by blast
  qed
  ultimately show "finite {x. f x \<noteq> \<bottom>} \<and> (\<forall>x. compact (f x))" by blast
next
  assume "finite {x. f x \<noteq> \<bottom>} \<and> (\<forall>x. compact (f x))"
  then have fin: "finite {x. f x \<noteq> \<bottom>}" and comp: "\<And>x. compact (f x)" by blast+
  show "compact f"
  proof (rule compactI2)
    fix Y :: "nat \<Rightarrow> 'a \<Rightarrow> 'b" assume Y: "chain Y" and le: "f \<sqsubseteq> (\<Squnion>i. Y i)"
    have "\<exists>i. f x \<sqsubseteq> Y i x" for x
    proof -
      have "f x \<sqsubseteq> (\<Squnion>i. Y i x)" using fun_belowD[OF le, of x] by (simp add: lub_fun[OF Y])
      then show ?thesis by (rule compactD2[OF comp ch2ch_fun[OF Y]])
    qed
    then obtain h where h: "\<And>x. f x \<sqsubseteq> Y (h x) x" by metis
    let ?n = "Max (insert 0 (h ` {x. f x \<noteq> \<bottom>}))"
    have "f x \<sqsubseteq> Y ?n x" for x
    proof (cases "f x = \<bottom>")
      case True then show ?thesis by simp
    next
      case False
      then have "h x \<le> ?n" by (intro Max_ge) (use fin in auto)
      then show ?thesis by (rule below_trans[OF h fun_belowD[OF chain_mono[OF Y]]])
    qed
    then show "\<exists>i. f \<sqsubseteq> Y i" by (blast intro: fun_belowI)
  qed
qed

subsection \<open>Levels of detail\<close>

text \<open>LODs are the compact semi-factors of the keys; the synonym only shortens the type.\<close>

type_synonym 'k lod = "'k semi_factor"

end
