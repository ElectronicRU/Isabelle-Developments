theory LOD
  imports LOD_Factor "HOL-Library.FSet"
begin

section \<open>Projections onto semi-factors\<close>

text \<open>Levels of detail are compact semi-factors of the key domain, acting on keys by projection;
  masks are arbitrary semi-factors.  The facts are stated for all semi-factors, with compactness
  of the semi-factor (and locally finitely detailed dI keys) where compactness of keys is needed.
  (They took over the names of the facts of the retired locale \<open>lod_space\<close>.)\<close>

abbreviation proj :: "'k::{bifinite, distributive_cpo} semi_factor \<Rightarrow> 'k \<rightarrow> 'k" where
  "proj \<equiv> semi_factor_p"

subsection \<open>Compact semi-factors project to compact keys\<close>

text \<open>Over a dI-domain every compact semi-factor is a finite join of principals of compacts
  (@{thm [source] compact_semi_factor_finite_join}).  Over a locally finitely detailed one the
  principal of a compact lies below a semi-factor all of whose elements are compact, and finite
  joins keep that property.  So compact semi-factors project every key to a compact one.
  (Without local finite detail this fails: in the separated sum of the powerset of the naturals
  and a point, the principal of the point is the whole domain.)  Projections of compact keys are
  compact over any dI-domain, everything below a compact element being compact.\<close>

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
  fixes k :: "'a::{dI, locally_finitely_detailed}"
  assumes "compact k"
  shows "compact (x \<downharpoonright> semi_factor_principal k)"
proof -
  obtain F where F: "finitary_semi_factor F" "k \<downharpoonright> F = k" using compact_level[OF assms] by blast
  have "semi_factor_principal k \<sqsubseteq> F" using F(2) by (simp add: semi_factor_principal_below_iff)
  then show ?thesis
    by (rule compact_proj_below) (use F(1) in \<open>simp add: finitary_semi_factor_def finitary_def\<close>)
qed

theorem compact_semi_factor_proj:
  fixes K :: "'a::{dI, locally_finitely_detailed} semi_factor"
  assumes "compact K"
  shows "compact (x \<downharpoonright> K)"
proof -
  obtain A where A: "finite A" "A \<subseteq> {k. compact k}" "K = lub (semi_factor_principal ` A)"
    using compact_semi_factor_finite_join[OF assms] by blast
  show ?thesis unfolding A(3)
    by (rule compact_proj_lub) (use A(1,2) in \<open>auto intro: compact_proj_principal\<close>)
qed

lemma compact_proj_compact: "compact k \<Longrightarrow> compact (k \<downharpoonright> (F :: 'a::dI semi_factor))"
  by (rule compact_below_compact[OF _ deflation.below[OF deflation_semi_factor_p]])

lemma proj_inf: "proj (inf a b)\<cdot>k = proj a\<cdot>(proj b\<cdot>k)"
  by (simp add: semi_factor_proj_comp inf_commute)

lemma proj_sup: "proj (sup a b)\<cdot>k = proj a\<cdot>k \<squnion> proj b\<cdot>k"
  by (simp add: semi_factor_p_sup)

lemma proj_bot: "proj bot = \<bottom>"
  by (simp add: semi_factor_p_bot)

lemma semi_factor_bot_bottom: "(bot :: 'k::{bifinite, distributive_cpo} semi_factor) = \<bottom>"
  by (rule bottomI) (simp add: below_semi_factor_iff_le)

lemma compact_semi_factor_bot [simp]: "compact (bot :: 'k::{bifinite, distributive_cpo} semi_factor)"
  by (simp add: semi_factor_bot_bottom)

lemma compact_semi_factor_sup:
  "compact a \<Longrightarrow> compact b \<Longrightarrow> compact (sup a b :: 'k::{bifinite, distributive_cpo} semi_factor)"
  by (simp add: join_semi_factor[symmetric] compact_join)

lemma compact_fold_sup:
  "(\<And>x. x \<in> set xs \<Longrightarrow> compact x) \<Longrightarrow> compact b
    \<Longrightarrow> compact (fold sup xs b :: 'k::{bifinite, distributive_cpo} semi_factor)"
  by (induct xs arbitrary: b) (simp_all add: compact_semi_factor_sup)

lemma proj_defl: "deflation (proj a)"
  by (rule deflation_semi_factor_p)

lemma proj_slide: "proj a\<cdot>y = y \<Longrightarrow> proj a\<cdot>x \<sqsubseteq> y \<Longrightarrow> x \<Up> y"
  by (rule semi_factor_defl.slide[OF semi_factor_defl_semi_factor_p])

lemma proj_compact: "compact a \<Longrightarrow> compact (proj a\<cdot>k)"
  for a :: "'k::{dI, locally_finitely_detailed} semi_factor"
  by (rule compact_semi_factor_proj)

lemma compact_lives: "compact k \<Longrightarrow> \<exists>c. compact c \<and> proj c\<cdot>k = k" for k :: "'k::dI"
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
  by (simp only: proj_inf[symmetric] inf_commute)

lemma proj_le: "a \<le> b \<Longrightarrow> proj a\<cdot>(proj b\<cdot>k) = proj a\<cdot>k"
  by (simp only: proj_inf[symmetric] inf_absorb1)

lemma proj_mono: "a \<le> b \<Longrightarrow> proj a\<cdot>k \<sqsubseteq> proj b\<cdot>k"
  by (metis proj_le proj_below)

subsection \<open>Where a key lives\<close>

definition lives_at :: "'k::{bifinite, distributive_cpo} semi_factor \<Rightarrow> 'k \<Rightarrow> bool" where
  "lives_at c k \<longleftrightarrow> proj c\<cdot>k = k"

text \<open>The LODs a key lives at form a filter, non-empty exactly for compact keys.\<close>

definition lods_of :: "'k::{bifinite, distributive_cpo} \<Rightarrow> 'k semi_factor set" where
  "lods_of k = {c. lives_at c k}"

lemma lives_at_up: "lives_at c k \<Longrightarrow> c \<le> c' \<Longrightarrow> lives_at c' k"
  unfolding lives_at_def by (metis proj_le proj_commute)

lemma lives_at_inf: "lives_at c k \<Longrightarrow> lives_at c' k \<Longrightarrow> lives_at (inf c c') k"
  unfolding lives_at_def by (simp add: proj_inf)

lemma lives_at_proj: "lives_at a (proj a\<cdot>k)"
  unfolding lives_at_def by simp

lemma compact_iff_lives: "compact k \<longleftrightarrow> (\<exists>c. compact c \<and> lives_at c k)"
  for k :: "'k::{dI, locally_finitely_detailed}"
  unfolding lives_at_def by (metis compact_lives proj_compact)

lemma lods_of_nonempty: "compact k \<Longrightarrow> lods_of k \<noteq> {}" for k :: "'k::dI"
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
  assumes ab: "a \<le> b" and k: "maximal_at b k"
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
  for c :: "'k::{dI, locally_finitely_detailed} semi_factor"
  by (metis maximal_at_lives proj_compact)

text \<open>A key below one living at the same LOD is that key, when it is maximal there.\<close>

lemma maximal_at_eq: "maximal_at c k \<Longrightarrow> proj c\<cdot>t = t \<Longrightarrow> k \<sqsubseteq> t \<Longrightarrow> t = k"
  by (simp add: maximal_at_def)

text \<open>Joins of compatible maximal keys are maximal at the join of their LODs.\<close>

lemma maximal_at_join:
  assumes a: "maximal_at A a" and b: "maximal_at B b" and j: "a \<Up> b"
  shows "maximal_at (sup A B) (a \<squnion> b)"
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
  show "proj (sup A B)\<cdot>(a \<squnion> b) = a \<squnion> b" by (simp only: proj_sup pa pb)
  fix t assume t: "proj (sup A B)\<cdot>t = t" and le: "a \<squnion> b \<sqsubseteq> t"
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
  assumes aL: "sup a L = sup a' L" and K: "maximal_at L K"
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
  have a_split: "a = sup (inf a a') (inf a L)"
    by (metis aL inf_sup_absorb inf_sup_distrib1)
  have "proj a\<cdot>?J = proj (inf a a')\<cdot>?J \<squnion> proj a\<cdot>K"
    by (subst a_split) (simp add: proj_sup proj_inf LJ)
  moreover have "proj a\<cdot>?J = K1"
    by (simp add: proj_join[OF j] K1 join_absorb2[OF le])
  ultimately have "K1 = proj (inf a a')\<cdot>?J \<squnion> proj a\<cdot>K" by simp
  then show ?thesis by (simp add: proj_join[OF jJ] proj_inf)
qed


subsection \<open>Masks\<close>

text \<open>A \<^emph>\<open>mask\<close> is a semi-factor, possibly non-compact, acting on LODs by meet: truncating an LOD
  to a mask keeps the part of it within the mask.  (This replaces an abstract type of
  truncations, i.e. of maps obeying \<open>\<tau> (inf x y) = inf x (\<tau> y)\<close>, which on a complete lattice
  are exactly the meets with a fixed element.)\<close>

abbreviation truncate :: "'l::lattice \<Rightarrow> 'l \<Rightarrow> 'l" where
  "truncate m x \<equiv> inf m x"

lemma truncate_inf: "truncate \<tau> (inf x y) = inf x (truncate \<tau> y)"
  by (simp add: inf_left_commute)

context
  fixes \<tau> :: "'l::{distrib_lattice, bounded_lattice_bot}"
begin

lemma truncate_below: "truncate \<tau> x \<le> x"
  by simp

lemma truncate_idem: "truncate \<tau> (truncate \<tau> x) = truncate \<tau> x"
  by simp

lemma truncate_mono: "x \<le> y \<Longrightarrow> truncate \<tau> x \<le> truncate \<tau> y"
  by (rule inf_mono[OF order_refl])

lemma truncate_inf_hom: "truncate \<tau> (inf x y) = inf (truncate \<tau> x) (truncate \<tau> y)"
  by (simp add: inf_aci)

lemma truncate_sup: "truncate \<tau> (sup x y) = sup (truncate \<tau> x) (truncate \<tau> y)"
  by (rule inf_sup_distrib1)

lemma truncate_bot: "truncate \<tau> bot = bot"
  by simp

lemma truncate_fix_down: "truncate \<tau> c = c \<Longrightarrow> d \<le> c \<Longrightarrow> truncate \<tau> d = d"
  by (metis inf_absorb2 inf_le1 order_trans)

lemma truncate_fix_sup: "truncate \<tau> c = c \<Longrightarrow> truncate \<tau> d = d \<Longrightarrow> truncate \<tau> (sup c d) = sup c d"
  by (simp add: truncate_sup)

lemma truncate_greatest: "truncate \<tau> c = c \<Longrightarrow> c \<le> x \<Longrightarrow> c \<le> truncate \<tau> x"
  by (metis truncate_mono)

text \<open>Within \<open>a\<close>, truncating more than \<open>a\<close> is truncating \<open>a\<close>.\<close>

lemma truncate_inf_sup: "inf (truncate \<tau> (sup a b)) a = truncate \<tau> a"
  by (metis inf_assoc inf_commute inf_sup_absorb)

end

lemma truncate_inf_comp: "truncate (inf \<rho> \<tau>) x = truncate \<rho> (truncate \<tau> x)"
  by (simp add: inf_assoc)

lemma truncate_top: "truncate top x = x" for x :: "'l::bounded_lattice"
  by simp

lemma truncate_bot_trunc: "truncate bot x = bot" for x :: "'l::bounded_lattice_bot"
  by simp

subsection \<open>Masks acting on keys\<close>

text \<open>A mask acts on keys by projection, through any LOD the key lives at.\<close>

lemma truncate_proj_irrelevant:
  assumes c: "lives_at c k" and c': "lives_at c' k"
  shows "proj (truncate \<tau> c)\<cdot>k = proj (truncate \<tau> c')\<cdot>k"
proof -
  have e: "inf (truncate \<tau> c) c' = inf (truncate \<tau> c') c" by (metis truncate_inf inf_commute)
  have "proj (truncate \<tau> c)\<cdot>k = proj (truncate \<tau> c)\<cdot>(proj c'\<cdot>k)" using c' by (simp add: lives_at_def)
  also have "\<dots> = proj (inf (truncate \<tau> c) c')\<cdot>k" by (simp only: proj_inf)
  also have "\<dots> = proj (inf (truncate \<tau> c') c)\<cdot>k" by (simp only: e)
  also have "\<dots> = proj (truncate \<tau> c')\<cdot>(proj c\<cdot>k)" by (simp only: proj_inf)
  also have "\<dots> = proj (truncate \<tau> c')\<cdot>k" using c by (simp add: lives_at_def)
  finally show ?thesis .
qed

definition truncate_key :: "'k::{bifinite, distributive_cpo} semi_factor \<Rightarrow> 'k \<Rightarrow> 'k" where
  "truncate_key \<tau> k = proj \<tau>\<cdot>k"

lemma truncate_key_eq:
  assumes c: "lives_at c k"
  shows "truncate_key \<tau> k = proj (truncate \<tau> c)\<cdot>k"
  using c by (simp add: truncate_key_def proj_inf lives_at_def)

subsection \<open>Levels of detail\<close>

text \<open>LODs are the compact semi-factors of the keys; the synonym only shortens the type.\<close>

type_synonym 'k lod = "'k semi_factor"

end
