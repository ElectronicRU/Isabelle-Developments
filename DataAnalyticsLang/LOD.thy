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
      tcut_fset_compact compact_lives_fset)+

end
