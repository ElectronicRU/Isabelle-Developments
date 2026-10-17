theory LOD
  imports LOD_Factor "HOL-Library.FSet"
begin

section \<open>Level-of-detail spaces\<close>

text \<open>A \<^emph>\<open>level of detail\<close> (LOD) acts on keys by projection.  LODs form a distributive lattice
  with a bottom but no top: every LOD is \<^emph>\<open>finite\<close>, in that it projects every key, however
  large, to a compact one.  Meets compose projections and joins join them; each projection is a
  deflation obeying the slide rule (what it keeps is joinable with anything projecting below
  it), so that projection preserves maximality.  Every compact key lives at some LOD.\<close>

locale lod_space =
  fixes proj :: "'l::{distrib_lattice, bounded_lattice_bot} \<Rightarrow> 'k::bounded_complete \<rightarrow> 'k"
  assumes proj_inf: "proj (inf a b)\<cdot>k = proj a\<cdot>(proj b\<cdot>k)"
    and proj_sup: "proj (sup a b)\<cdot>k = proj a\<cdot>k \<squnion> proj b\<cdot>k"
    and proj_bot: "proj bot = \<bottom>"
    and proj_defl: "deflation (proj a)"
    and proj_slide: "proj a\<cdot>y = y \<Longrightarrow> proj a\<cdot>x \<sqsubseteq> y \<Longrightarrow> x \<Up> y"
    and proj_compact: "compact (proj a\<cdot>k)"
    and compact_lives: "compact k \<Longrightarrow> \<exists>c. proj c\<cdot>k = k"
    and proj_join: "x \<Up> y \<Longrightarrow> proj a\<cdot>(x \<squnion> y) = proj a\<cdot>x \<squnion> proj a\<cdot>y"
    and proj_downclosed: "proj a\<cdot>y = y \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> proj a\<cdot>x = x"
begin

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

definition lives_at :: "'l \<Rightarrow> 'k \<Rightarrow> bool" where
  "lives_at c k \<longleftrightarrow> proj c\<cdot>k = k"

text \<open>The LODs a key lives at form a filter, non-empty exactly for compact keys.\<close>

definition lods_of :: "'k \<Rightarrow> 'l set" where
  "lods_of k = {c. lives_at c k}"

lemma lives_at_up: "lives_at c k \<Longrightarrow> c \<le> c' \<Longrightarrow> lives_at c' k"
  unfolding lives_at_def by (metis proj_le proj_commute)

lemma lives_at_inf: "lives_at c k \<Longrightarrow> lives_at c' k \<Longrightarrow> lives_at (inf c c') k"
  unfolding lives_at_def by (simp add: proj_inf)

lemma lives_at_proj: "lives_at a (proj a\<cdot>k)"
  unfolding lives_at_def by simp

lemma compact_iff_lives: "compact k \<longleftrightarrow> (\<exists>c. lives_at c k)"
  unfolding lives_at_def by (metis compact_lives proj_compact)

lemma lods_of_nonempty: "compact k \<Longrightarrow> lods_of k \<noteq> {}"
  unfolding lods_of_def using compact_iff_lives by blast

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

definition maximal_at :: "'l \<Rightarrow> 'k \<Rightarrow> bool" where
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

lemma maximal_at_compact: "maximal_at c k \<Longrightarrow> compact k"
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

end

subsection \<open>Truncations\<close>

text \<open>A \<^emph>\<open>truncation\<close> is the action of meeting with a (possibly non-compact) LOD.  It is
  captured by a single module law; everything else follows in a distributive lattice.  Its
  fixed points form an ideal, and the truncation takes each LOD to the largest fixed point
  below it.\<close>

typedef ('l::distrib_lattice) trunc = "{\<tau> :: 'l \<Rightarrow> 'l. \<forall>x y. \<tau> (inf x y) = inf x (\<tau> y)}"
  morphisms truncate Abs_trunc
  by (rule exI[of _ id]) simp

setup_lifting type_definition_trunc

lemma truncate_inf: "truncate \<tau> (inf x y) = inf x (truncate \<tau> y)"
  using truncate[of \<tau>] by simp

context
  fixes \<tau> :: "'l::{distrib_lattice, bounded_lattice_bot} trunc"
begin

lemma truncate_below: "truncate \<tau> x \<le> x"
  by (metis truncate_inf inf_idem inf_le1)

lemma truncate_idem [simp]: "truncate \<tau> (truncate \<tau> x) = truncate \<tau> x"
  by (metis truncate_inf truncate_below inf_absorb1 inf_idem)

lemma truncate_mono: "x \<le> y \<Longrightarrow> truncate \<tau> x \<le> truncate \<tau> y"
  by (metis truncate_inf inf_absorb1 inf_le2)

lemma truncate_inf_hom: "truncate \<tau> (inf x y) = inf (truncate \<tau> x) (truncate \<tau> y)"
  by (metis truncate_inf truncate_idem inf_commute)

lemma truncate_sup: "truncate \<tau> (sup x y) = sup (truncate \<tau> x) (truncate \<tau> y)"
proof -
  have a: "inf x (truncate \<tau> (sup x y)) = truncate \<tau> x"
    by (simp only: truncate_inf[symmetric] inf_sup_absorb)
  have b: "inf y (truncate \<tau> (sup x y)) = truncate \<tau> y"
    by (simp only: sup_commute[of x y] truncate_inf[symmetric] inf_sup_absorb)
  have "truncate \<tau> (sup x y) = inf (sup x y) (truncate \<tau> (sup x y))"
    by (simp add: inf_absorb2 truncate_below)
  also have "\<dots> = sup (truncate \<tau> x) (truncate \<tau> y)" by (simp only: inf_sup_distrib2 a b)
  finally show ?thesis .
qed

lemma truncate_bot [simp]: "truncate \<tau> bot = bot"
  using truncate_below[of bot] by (simp add: bot_unique)

lemma truncate_fix_down: "truncate \<tau> c = c \<Longrightarrow> d \<le> c \<Longrightarrow> truncate \<tau> d = d"
  by (metis truncate_inf inf_absorb1)

lemma truncate_fix_sup: "truncate \<tau> c = c \<Longrightarrow> truncate \<tau> d = d \<Longrightarrow> truncate \<tau> (sup c d) = sup c d"
  by (simp add: truncate_sup)

lemma truncate_greatest: "truncate \<tau> c = c \<Longrightarrow> c \<le> x \<Longrightarrow> c \<le> truncate \<tau> x"
  by (metis truncate_mono)

text \<open>Within \<open>a\<close>, truncating more than \<open>a\<close> is truncating \<open>a\<close>.\<close>

lemma truncate_inf_sup: "inf (truncate \<tau> (sup a b)) a = truncate \<tau> a"
proof -
  have "inf (truncate \<tau> (sup a b)) a = sup (inf (truncate \<tau> a) a) (inf (truncate \<tau> b) a)"
    by (simp add: truncate_sup inf_sup_distrib2)
  also have "inf (truncate \<tau> a) a = truncate \<tau> a" by (simp add: inf_absorb1 truncate_below)
  also have "inf (truncate \<tau> b) a = truncate \<tau> (inf a b)" by (simp add: truncate_inf inf_commute)
  also have "sup (truncate \<tau> a) (truncate \<tau> (inf a b)) = truncate \<tau> a"
    by (simp add: sup_absorb1 truncate_mono)
  finally show ?thesis .
qed

end

text \<open>Meeting with any LOD is a truncation.\<close>

lift_definition trunc_at :: "'l::distrib_lattice \<Rightarrow> 'l trunc" is inf
  by (simp add: inf_left_commute)

lemma truncate_trunc_at [simp]: "truncate (trunc_at g) x = inf g x"
  by transfer simp

text \<open>Truncations form a distributive lattice under the pointwise order; meet is composition,
  the identity is the top and the constant \<open>\<bottom>\<close> the bottom.\<close>

instantiation trunc :: ("{distrib_lattice, bounded_lattice_bot}") "{distrib_lattice, bounded_lattice}"
begin

lift_definition less_eq_trunc :: "'a trunc \<Rightarrow> 'a trunc \<Rightarrow> bool" is "\<lambda>f g. \<forall>x. f x \<le> g x" .

definition less_trunc :: "'a trunc \<Rightarrow> 'a trunc \<Rightarrow> bool" where
  "less_trunc \<rho> \<tau> \<longleftrightarrow> \<rho> \<le> \<tau> \<and> \<not> \<tau> \<le> \<rho>"

lift_definition inf_trunc :: "'a trunc \<Rightarrow> 'a trunc \<Rightarrow> 'a trunc" is "\<lambda>f g x. inf (f x) (g x)"
  by (simp add: inf_aci)

lift_definition sup_trunc :: "'a trunc \<Rightarrow> 'a trunc \<Rightarrow> 'a trunc" is "\<lambda>f g x. sup (f x) (g x)"
  by (simp add: inf_sup_distrib1)

lift_definition bot_trunc :: "'a trunc" is "\<lambda>_. bot"
  by simp

lift_definition top_trunc :: "'a trunc" is id
  by simp

instance
proof
  show "\<rho> < \<tau> \<longleftrightarrow> \<rho> \<le> \<tau> \<and> \<not> \<tau> \<le> \<rho>" for \<rho> \<tau> :: "'a trunc" by (fact less_trunc_def)
  show "\<rho> \<le> \<rho>" for \<rho> :: "'a trunc" by transfer simp
  show "\<rho> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<tau> \<Longrightarrow> \<rho> \<le> \<tau>" for \<rho> \<sigma> \<tau> :: "'a trunc" by transfer (blast intro: order_trans)
  show "\<rho> \<le> \<tau> \<Longrightarrow> \<tau> \<le> \<rho> \<Longrightarrow> \<rho> = \<tau>" for \<rho> \<tau> :: "'a trunc"
    by transfer (blast intro: antisym)
  show "inf \<rho> \<tau> \<le> \<rho>" "inf \<rho> \<tau> \<le> \<tau>" for \<rho> \<tau> :: "'a trunc" by (transfer, simp)+
  show "\<rho> \<le> \<sigma> \<Longrightarrow> \<rho> \<le> \<tau> \<Longrightarrow> \<rho> \<le> inf \<sigma> \<tau>" for \<rho> \<sigma> \<tau> :: "'a trunc" by transfer simp
  show "\<rho> \<le> sup \<rho> \<tau>" "\<tau> \<le> sup \<rho> \<tau>" for \<rho> \<tau> :: "'a trunc" by (transfer, simp)+
  show "\<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<le> \<rho> \<Longrightarrow> sup \<sigma> \<tau> \<le> \<rho>" for \<rho> \<sigma> \<tau> :: "'a trunc" by transfer simp
  show "sup \<rho> (inf \<sigma> \<tau>) = inf (sup \<rho> \<sigma>) (sup \<rho> \<tau>)" for \<rho> \<sigma> \<tau> :: "'a trunc"
    by transfer (simp add: sup_inf_distrib1)
  show "bot \<le> \<rho>" for \<rho> :: "'a trunc" by transfer simp
  show "\<rho> \<le> top" for \<rho> :: "'a trunc"
    by transfer (metis id_apply inf_idem inf_le1)
qed

end

lemma truncate_inf_comp: "truncate (inf \<rho> \<tau>) x = truncate \<rho> (truncate \<tau> x)"
proof -
  have "truncate \<rho> (truncate \<tau> x) = truncate \<rho> (inf (truncate \<tau> x) x)"
    by (simp add: inf_absorb1 truncate_below)
  also have "\<dots> = inf (truncate \<tau> x) (truncate \<rho> x)" by (rule truncate_inf)
  finally show ?thesis by transfer (simp add: inf_commute)
qed

lemma truncate_top [simp]: "truncate top x = x"
  by transfer simp

lemma truncate_bot_trunc [simp]: "truncate bot x = bot"
  by transfer simp

subsection \<open>Truncations acting on keys\<close>

context lod_space
begin

text \<open>A truncation acts on a key through any LOD the key lives at; the choice is irrelevant.\<close>

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

definition truncate_key :: "'l trunc \<Rightarrow> 'k \<Rightarrow> 'k" where
  "truncate_key \<tau> k = (THE k'. \<exists>c. lives_at c k \<and> k' = proj (truncate \<tau> c)\<cdot>k)"

lemma truncate_key_eq:
  assumes c: "lives_at c k"
  shows "truncate_key \<tau> k = proj (truncate \<tau> c)\<cdot>k"
  unfolding truncate_key_def
proof (rule the_equality)
  show "\<exists>c'. lives_at c' k \<and> proj (truncate \<tau> c)\<cdot>k = proj (truncate \<tau> c')\<cdot>k" using c by blast
  show "k' = proj (truncate \<tau> c)\<cdot>k" if "\<exists>c'. lives_at c' k \<and> k' = proj (truncate \<tau> c')\<cdot>k" for k'
    using that truncate_proj_irrelevant[OF _ c] by blast
qed

end

subsection \<open>Dropping dimensions\<close>

text \<open>On tuples, an LOD can drop a set of dimensions.  Dropping is a truncation, not a meet with
  an LOD: what is left after dropping is the meet with a non-finitary "negative" level, which is
  not itself an LOD.  Its action on keys is cutting away the dropped dimensions after projecting,
  which continues the dimension-set interpretation below.\<close>

locale lod_tuple_space = lod_space proj
  for proj :: "'l::{distrib_lattice, bounded_lattice_bot} \<Rightarrow> ('d, 'v::bounded_complete) tuple \<rightarrow> ('d, 'v) tuple" +
  fixes drop :: "'d set \<Rightarrow> 'l trunc"
  assumes proj_drop: "proj (truncate (drop D) c)\<cdot>k = tcut (- D)\<cdot>(proj c\<cdot>k)"
begin

lemma drop_below: "truncate (drop D) c \<le> c"
  by (rule truncate_below)

lemma drop_mono: "c \<le> c' \<Longrightarrow> truncate (drop D) c \<le> truncate (drop D) c'"
  by (rule truncate_mono)

lemma proj_drop_empty: "proj (truncate (drop {}) c)\<cdot>k = proj c\<cdot>k"
  by (simp add: proj_drop tcut_beta tget_inverse)

lemma proj_drop_Un:
  "proj (truncate (drop (D \<union> E)) c)\<cdot>k = proj (truncate (drop D) (truncate (drop E) c))\<cdot>k"
  by (simp add: proj_drop tcut_compose Int_commute)

lemma proj_drop_antimono: "D \<subseteq> E \<Longrightarrow> proj (truncate (drop E) c)\<cdot>k \<sqsubseteq> proj (truncate (drop D) c)\<cdot>k"
  by (simp add: proj_drop tcut_mono_set)

lemma proj_drop_commute:
  "proj (truncate (drop D) (truncate (drop E) c))\<cdot>k = proj (truncate (drop E) (truncate (drop D) c))\<cdot>k"
  by (simp add: proj_drop tcut_compose Int_commute)

end

section \<open>Dimension sets\<close>

text \<open>Finite dimension sets acting on tuples of flat-ish values by cutting.\<close>

lemma tcut_slide:
  fixes x y :: "('d, 'v::bounded_complete) tuple"
  assumes y: "tcut A\<cdot>y = y" and xy: "tcut A\<cdot>x \<sqsubseteq> y"
  shows "x \<Up> y"
proof (rule joinableI)
  let ?z = "Abs_tuple (\<lambda>d. if d \<in> A then y\<langle>d\<rangle> else x\<langle>d\<rangle>) :: ('d, 'v) tuple"
  have xy': "x\<langle>d\<rangle> \<sqsubseteq> y\<langle>d\<rangle>" if "d \<in> A" for d
    using xy that unfolding below_tuple_def fun_below_iff by (metis tcut_mem)
  have y': "y\<langle>d\<rangle> = \<bottom>" if "d \<notin> A" for d
    using that by (metis y tcut_nomem)
  show "x \<sqsubseteq> ?z" unfolding below_tuple_def fun_below_iff by (simp add: Abs_tuple_inverse' xy')
  show "y \<sqsubseteq> ?z" unfolding below_tuple_def fun_below_iff by (simp add: Abs_tuple_inverse' y')
qed

lemma tcut_fset_inf: "tcut (fset (inf a b))\<cdot>k = tcut (fset a)\<cdot>(tcut (fset b)\<cdot>k)"
  by (simp add: tcut_compose inf_fset.rep_eq Int_commute)

lemma tcut_fset_sup:
  fixes k :: "('d, 'v::bounded_complete) tuple"
  shows "tcut (fset (sup a b))\<cdot>k = tcut (fset a)\<cdot>k \<squnion> tcut (fset b)\<cdot>k"
  by (simp add: tcut_join sup_fset.rep_eq)

lemma tcut_fset_bot: "tcut (fset bot) = \<bottom>"
  by simp

lemma tcut_join_arg:
  fixes x y :: "('d, 'v::bounded_complete) tuple"
  assumes j: "x \<Up> y"
  shows "tcut A\<cdot>(x \<squnion> y) = tcut A\<cdot>x \<squnion> tcut A\<cdot>y"
proof -
  have j': "tcut A\<cdot>x \<Up> tcut A\<cdot>y"
    by (rule joinableI[OF monofun_cfun_arg[OF joinableD(1)[OF j]] monofun_cfun_arg[OF joinableD(2)[OF j]]])
  show ?thesis
    by (rule tuple_eqI) (simp add: tget_join[OF j] tget_join[OF j'] tcut_tget)
qed

lemma tcut_downclosed:
  fixes x y :: "('d, 'v::pcpo) tuple"
  assumes y: "tcut A\<cdot>y = y" and xy: "x \<sqsubseteq> y"
  shows "tcut A\<cdot>x = x"
proof (rule tuple_eqI)
  fix d
  show "(tcut A\<cdot>x)\<langle>d\<rangle> = x\<langle>d\<rangle>"
  proof (cases "d \<in> A")
    case False
    have "x\<langle>d\<rangle> \<sqsubseteq> y\<langle>d\<rangle>" using xy by (simp add: below_tuple_def fun_below_iff)
    also have "y\<langle>d\<rangle> = \<bottom>" using False by (metis y tcut_nomem)
    finally have "x\<langle>d\<rangle> = \<bottom>" by (rule bottomI)
    then show ?thesis using False by (simp add: tcut_tget)
  qed (simp add: tcut_tget)
qed

lemma deflation_tcut: "deflation (tcut A)"
  by (rule deflation.intro) (simp_all add: tcut_compose tcut_below)

lemma tcut_fset_compact:
  fixes k :: "('d, 'v::{pcpo, chfin}) tuple"
  shows "compact (tcut (fset a)\<cdot>k)"
  by (rule compact_tcut) simp

lemma compact_lives_fset:
  fixes k :: "('d, 'v::pcpo) tuple"
  assumes "compact k" shows "\<exists>c. tcut (fset c)\<cdot>k = k"
proof (intro exI)
  show "tcut (fset (Abs_fset (tsupp k)))\<cdot>k = k"
    using compact_finite_tsupp[OF assms] by (simp add: Abs_fset_inverse tcut_tsupp)
qed

interpretation dims: lod_space "\<lambda>A. tcut (fset A) :: ('d, 'v::{bounded_complete, chfin}) tuple \<rightarrow> _"
  by unfold_locales (fact tcut_fset_inf tcut_fset_sup tcut_fset_bot deflation_tcut tcut_slide
      tcut_fset_compact compact_lives_fset tcut_join_arg tcut_downclosed)+

text \<open>Dropping from a dimension set is set difference.\<close>

lift_definition fdrop :: "'d set \<Rightarrow> 'd fset trunc" is "\<lambda>D A. ffilter (\<lambda>d. d \<notin> D) A"
  by auto

lemma truncate_fdrop [simp]: "truncate (fdrop D) A = ffilter (\<lambda>d. d \<notin> D) A"
  by transfer simp

interpretation dims: lod_tuple_space "\<lambda>A. tcut (fset A) :: ('d, 'v::{bounded_complete, chfin}) tuple \<rightarrow> _"
  fdrop
  by unfold_locales (simp_all add: tcut_compose Int_commute Collect_conj_eq Compl_eq)

section \<open>The type of levels of detail\<close>

text \<open>Levels of detail are the finitary semi-factors.  They are closed under meets (composition
  of a compact-valued deflation), binary joins (joins of compacts) and \<open>\<bottom>\<close>.\<close>

lemma finitary_semi_factor_inf:
  "finitary_semi_factor F \<Longrightarrow> finitary_semi_factor G \<Longrightarrow> finitary_semi_factor (inf F G)"
  by (simp add: finitary_semi_factor_def finitary_def semi_factor_p.rep_eq inf_semi_factor.rep_eq
      p_inf)

lemma finitary_semi_factor_sup:
  "finitary_semi_factor F \<Longrightarrow> finitary_semi_factor G \<Longrightarrow> finitary_semi_factor (sup F G)"
  by (simp add: finitary_semi_factor_def finitary_def semi_factor_p.rep_eq sup_semi_factor.rep_eq
      p_sup_join compact_join)

lemma finitary_semi_factor_bot: "finitary_semi_factor bot"
  by (simp add: finitary_semi_factor_def finitary_def semi_factor_p.rep_eq bot_semi_factor.rep_eq
      p_bot_stable_subdom)

typedef (overloaded) 'a lod =
  "{F :: 'a::{bifinite, distributive_cpo} semi_factor. finitary_semi_factor F}"
  morphisms semi_factor_of_lod lod_of_semi_factor
  using finitary_semi_factor_bot by blast

setup_lifting type_definition_lod

instantiation lod :: ("{bifinite, distributive_cpo}") "{distrib_lattice, bounded_lattice_bot}"
begin

lift_definition less_eq_lod :: "'a lod \<Rightarrow> 'a lod \<Rightarrow> bool" is "(\<le>)" .
lift_definition less_lod :: "'a lod \<Rightarrow> 'a lod \<Rightarrow> bool" is "(<)" .
lift_definition inf_lod :: "'a lod \<Rightarrow> 'a lod \<Rightarrow> 'a lod" is inf by (rule finitary_semi_factor_inf)
lift_definition sup_lod :: "'a lod \<Rightarrow> 'a lod \<Rightarrow> 'a lod" is sup by (rule finitary_semi_factor_sup)
lift_definition bot_lod :: "'a lod" is bot by (rule finitary_semi_factor_bot)

instance
  apply (standard; transfer; simp add: less_le_not_le)
  apply (standard; transfer)
  apply (simp_all add: less_le_not_le)
  by (rule sup_inf_distrib1)

end

interpretation lod: lod_space "\<lambda>L. semi_factor_p (semi_factor_of_lod L) :: 'a::locally_finitely_detailed \<rightarrow> 'a"
proof unfold_locales
  fix a b :: "'a lod" and k x y :: 'a
  note sf = semi_factor_defl_semi_factor_p[of "semi_factor_of_lod a"]
  show "k \<downharpoonright> semi_factor_of_lod (inf a b) = k \<downharpoonright> semi_factor_of_lod b \<downharpoonright> semi_factor_of_lod a"
    by (simp add: inf_lod.rep_eq semi_factor_proj_comp inf_commute)
  show "k \<downharpoonright> semi_factor_of_lod (sup a b) = k \<downharpoonright> semi_factor_of_lod a \<squnion> k \<downharpoonright> semi_factor_of_lod b"
    by (simp add: sup_lod.rep_eq semi_factor_p_sup)
  show "semi_factor_p (semi_factor_of_lod bot) = \<bottom>"
    by (simp add: bot_lod.rep_eq semi_factor_p_bot)
  show "x \<Up> y" if "y \<downharpoonright> semi_factor_of_lod a = y" "x \<downharpoonright> semi_factor_of_lod a \<sqsubseteq> y"
    using that by (rule semi_factor_defl.slide[OF sf])
  show "compact (k \<downharpoonright> semi_factor_of_lod a)"
    using semi_factor_of_lod[of a] by (simp add: finitary_semi_factor_def finitary_def)
  show "(x \<squnion> y) \<downharpoonright> semi_factor_of_lod a = x \<downharpoonright> semi_factor_of_lod a \<squnion> y \<downharpoonright> semi_factor_of_lod a"
    if "x \<Up> y"
    using semi_factor_defl.axioms(1)[OF sf] that by (rule stable_defl_image_join)
  show "x \<downharpoonright> semi_factor_of_lod a = x" if "y \<downharpoonright> semi_factor_of_lod a = y" "x \<sqsubseteq> y"
    using that by (rule stable_defl.downclosed[OF semi_factor_defl.axioms(1)[OF sf]])
next
  fix k :: 'a assume "compact k"
  then obtain F where F: "finitary_semi_factor F" "k \<downharpoonright> F = k" using compact_level by blast
  then show "\<exists>c. k \<downharpoonright> semi_factor_of_lod c = k"
    by (intro exI[of _ "lod_of_semi_factor F"]) (simp add: lod_of_semi_factor_inverse)
qed

end
