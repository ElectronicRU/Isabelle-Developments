theory LOD
  imports ValsetBase "HOL-Library.FSet"
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

subsection \<open>LOD transformers\<close>

text \<open>A \<^emph>\<open>transformer\<close> is the action of meeting with a (possibly non-compact) LOD.  It is
  captured by a single module law; everything else follows in a distributive lattice.  Its
  fixed points form an ideal, and the transformer takes each LOD to the largest fixed point
  below it.\<close>

definition lod_tf :: "('l::distrib_lattice \<Rightarrow> 'l) \<Rightarrow> bool" where
  "lod_tf \<tau> \<longleftrightarrow> (\<forall>x y. \<tau> (inf x y) = inf x (\<tau> y))"

context
  fixes \<tau> :: "'l::{distrib_lattice, bounded_lattice_bot} \<Rightarrow> 'l"
  assumes tf: "lod_tf \<tau>"
begin

lemma tf_module: "\<tau> (inf x y) = inf x (\<tau> y)"
  using tf by (simp add: lod_tf_def)

lemma tf_below: "\<tau> x \<le> x"
  by (metis tf_module inf_idem inf_le1)

lemma tf_idem [simp]: "\<tau> (\<tau> x) = \<tau> x"
  by (metis tf_module tf_below inf_absorb1 inf_idem)

lemma tf_mono: "x \<le> y \<Longrightarrow> \<tau> x \<le> \<tau> y"
  by (metis tf_module inf_absorb1 inf_le2)

lemma tf_inf: "\<tau> (inf x y) = inf (\<tau> x) (\<tau> y)"
  by (metis tf_module tf_idem inf_commute)

lemma tf_sup: "\<tau> (sup x y) = sup (\<tau> x) (\<tau> y)"
proof -
  have a: "inf x (\<tau> (sup x y)) = \<tau> x" by (simp only: tf_module[symmetric] inf_sup_absorb)
  have b: "inf y (\<tau> (sup x y)) = \<tau> y" by (simp only: sup_commute[of x y] tf_module[symmetric] inf_sup_absorb)
  have "\<tau> (sup x y) = inf (sup x y) (\<tau> (sup x y))" by (simp add: inf_absorb2 tf_below)
  also have "\<dots> = sup (\<tau> x) (\<tau> y)" by (simp only: inf_sup_distrib2 a b)
  finally show ?thesis .
qed

lemma tf_bot [simp]: "\<tau> bot = bot"
  using tf_below[of bot] by (simp add: bot_unique)

lemma tf_fix_down: "\<tau> c = c \<Longrightarrow> d \<le> c \<Longrightarrow> \<tau> d = d"
  by (metis tf_module inf_absorb1)

lemma tf_fix_sup: "\<tau> c = c \<Longrightarrow> \<tau> d = d \<Longrightarrow> \<tau> (sup c d) = sup c d"
  by (simp add: tf_sup)

lemma tf_greatest: "\<tau> c = c \<Longrightarrow> c \<le> x \<Longrightarrow> c \<le> \<tau> x"
  by (metis tf_mono)

text \<open>Within \<open>a\<close>, transforming more than \<open>a\<close> is transforming \<open>a\<close>.\<close>

lemma tf_inf_sup: "inf (\<tau> (sup a b)) a = \<tau> a"
proof -
  have "inf (\<tau> (sup a b)) a = sup (inf (\<tau> a) a) (inf (\<tau> b) a)"
    by (simp add: tf_sup inf_sup_distrib2)
  also have "inf (\<tau> a) a = \<tau> a" by (simp add: inf_absorb1 tf_below)
  also have "inf (\<tau> b) a = \<tau> (inf a b)" by (simp add: tf_module inf_commute)
  also have "sup (\<tau> a) (\<tau> (inf a b)) = \<tau> a" by (simp add: sup_absorb1 tf_mono)
  finally show ?thesis .
qed

end

lemma lod_tf_inf: "lod_tf (inf g)"
  unfolding lod_tf_def by (simp add: inf_left_commute)

lemma lod_tf_id: "lod_tf id"
  unfolding lod_tf_def by simp

subsection \<open>Transformers acting on keys\<close>

context lod_space
begin

text \<open>A transformer acts on a key through any LOD the key lives at; the choice is irrelevant.\<close>

lemma tf_proj_irrelevant:
  assumes tf: "lod_tf \<tau>" and c: "lives_at c k" and c': "lives_at c' k"
  shows "proj (\<tau> c)\<cdot>k = proj (\<tau> c')\<cdot>k"
proof -
  have e: "inf (\<tau> c) c' = inf (\<tau> c') c" by (metis tf_module[OF tf] inf_commute)
  have "proj (\<tau> c)\<cdot>k = proj (\<tau> c)\<cdot>(proj c'\<cdot>k)" using c' by (simp add: lives_at_def)
  also have "\<dots> = proj (inf (\<tau> c) c')\<cdot>k" by (simp only: proj_inf)
  also have "\<dots> = proj (inf (\<tau> c') c)\<cdot>k" by (simp only: e)
  also have "\<dots> = proj (\<tau> c')\<cdot>(proj c\<cdot>k)" by (simp only: proj_inf)
  also have "\<dots> = proj (\<tau> c')\<cdot>k" using c by (simp add: lives_at_def)
  finally show ?thesis .
qed

definition tf_key :: "('l \<Rightarrow> 'l) \<Rightarrow> 'k \<Rightarrow> 'k" where
  "tf_key \<tau> k = (THE k'. \<exists>c. lives_at c k \<and> k' = proj (\<tau> c)\<cdot>k)"

lemma tf_key_eq:
  assumes tf: "lod_tf \<tau>" and c: "lives_at c k"
  shows "tf_key \<tau> k = proj (\<tau> c)\<cdot>k"
  unfolding tf_key_def
proof (rule the_equality)
  show "\<exists>c'. lives_at c' k \<and> proj (\<tau> c)\<cdot>k = proj (\<tau> c')\<cdot>k" using c by blast
  show "k' = proj (\<tau> c)\<cdot>k" if "\<exists>c'. lives_at c' k \<and> k' = proj (\<tau> c')\<cdot>k" for k'
    using that tf_proj_irrelevant[OF tf _ c] by blast
qed

end

subsection \<open>Dropping dimensions\<close>

text \<open>On tuples, an LOD can drop a set of dimensions.  Dropping is a transformer, not a meet with
  an LOD: what is left after dropping is the meet with a non-finitary "negative" level, which is
  not itself an LOD.  Its action on keys is cutting away the dropped dimensions after projecting,
  which continues the dimension-set interpretation below.\<close>

locale lod_tuple_space = lod_space proj
  for proj :: "'l::{distrib_lattice, bounded_lattice_bot} \<Rightarrow> ('d, 'v::bounded_complete) tuple \<rightarrow> ('d, 'v) tuple" +
  fixes drop :: "'d set \<Rightarrow> 'l \<Rightarrow> 'l"
  assumes drop_tf: "lod_tf (drop D)"
    and proj_drop: "proj (drop D c)\<cdot>k = tcut (- D)\<cdot>(proj c\<cdot>k)"
begin

lemma drop_below: "drop D c \<le> c"
  by (rule tf_below[OF drop_tf])

lemma drop_mono: "c \<le> c' \<Longrightarrow> drop D c \<le> drop D c'"
  by (rule tf_mono[OF drop_tf])

lemma proj_drop_empty: "proj (drop {} c)\<cdot>k = proj c\<cdot>k"
  by (simp add: proj_drop tcut_beta tget_inverse)

lemma proj_drop_Un: "proj (drop (D \<union> E) c)\<cdot>k = proj (drop D (drop E c))\<cdot>k"
  by (simp add: proj_drop tcut_compose Int_commute)

lemma proj_drop_antimono: "D \<subseteq> E \<Longrightarrow> proj (drop E c)\<cdot>k \<sqsubseteq> proj (drop D c)\<cdot>k"
  by (simp add: proj_drop tcut_mono_set)

lemma proj_drop_commute: "proj (drop D (drop E c))\<cdot>k = proj (drop E (drop D c))\<cdot>k"
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

lemma lod_tf_fminus: "lod_tf (\<lambda>A. ffilter (\<lambda>d. d \<notin> D) A)"
  unfolding lod_tf_def by auto

interpretation dims: lod_tuple_space "\<lambda>A. tcut (fset A) :: ('d, 'v::{bounded_complete, chfin}) tuple \<rightarrow> _"
  "\<lambda>D A. ffilter (\<lambda>d. d \<notin> D) A"
  by unfold_locales (simp_all add: lod_tf_fminus tcut_compose Int_commute Collect_conj_eq Compl_eq)

end
