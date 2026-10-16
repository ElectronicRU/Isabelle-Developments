theory Frame
  imports Slicer Relspace
begin

section \<open>Frames\<close>

text \<open>A frame has a level of detail and two levels of filters.  The \<^emph>\<open>ambient\<close> filter is an open
  predicate on rows: expressions may add to it (an MDX-style subselect) or, by \<open>ISOLATE\<close>, discard
  it, but never take it apart.  The \<^emph>\<open>slice\<close> is a syntactic filter on keys that expressions
  coarsen; dropping detail from the frame always coarsens the slice as well.  The frame's LOD
  partitions the selected rows into groups by their projected keys.\<close>

record ('l::type, 'f::type, 'r::pcpo) frame =
  flod :: 'l
  amb :: "'r sel"
  slice :: 'f

text \<open>The meaning of an expression: the LOD it decides at least; its \<^emph>\<open>dims\<close>, a finite set of
  pairs of a \<^emph>\<open>natural\<close> LOD (the key of values read out of the dataset) and a \<^emph>\<open>mask\<close> (a transformer
  for the part of a key's detail those values actually read; dropped detail is broadcast); and its
  values at each frame and key, \<open>\<bottom>\<close> for ``no entry''.  A pair per component keeps the dims law of a
  collection as weak as its components' laws; a broadcast needs none.\<close>

record ('l::type, 'f::type, 'r::pcpo, 'k::type, 'v::type) expr =
  emind :: 'l
  edims :: "('l \<times> ('l \<Rightarrow> 'l)) fset"
  esem :: "('l, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'v"

section \<open>Frame transformers\<close>

text \<open>The level-of-detail constructs act on the frame an inner expression is evaluated under.
  \<open>INCLUDE D\<close> adds detail \<open>D\<close>; \<open>RESTRICT \<phi>\<close> adds \<open>\<phi>\<close> to the ambient filter.  The others need the
  slicer: \<open>GROUP BY ONLY D\<close> replaces the LOD by \<open>D\<close> and coarsens the slice to it (\<open>TOTAL\<close> is
  \<open>GROUP BY ONLY \<bottom>\<close>); \<open>ISOLATE\<close> evaluates under the empty frame, with neither filter; \<open>E FOR \<tau> G\<close>
  drops detail by a transformer \<open>\<tau>\<close>, from the frame and from the slice, and conjoins \<open>G\<close>
  (\<open>EXCLUDE\<close> is \<open>FOR \<tau> \<^bold>1\<close>).\<close>

definition finclude :: "'l::sup \<Rightarrow> ('l, 'f::type, 'r::pcpo) frame \<Rightarrow> ('l, 'f, 'r) frame" where
  "finclude D F = F\<lparr>flod := sup (flod F) D\<rparr>"

lemma flod_finclude [simp]: "flod (finclude D F) = sup (flod F) D"
  by (simp add: finclude_def)

lemma amb_finclude [simp]: "amb (finclude D F) = amb F"
  by (simp add: finclude_def)

lemma slice_finclude [simp]: "slice (finclude D F) = slice F"
  by (simp add: finclude_def)

definition frestrict :: "'r::pcpo sel \<Rightarrow> ('l::type, 'f::type, 'r) frame \<Rightarrow> ('l, 'f, 'r) frame" where
  "frestrict \<phi> F = F\<lparr>amb := inf (amb F) \<phi>\<rparr>"

lemma flod_frestrict [simp]: "flod (frestrict \<phi> F) = flod F"
  by (simp add: frestrict_def)

lemma slice_frestrict [simp]: "slice (frestrict \<phi> F) = slice F"
  by (simp add: frestrict_def)

lemma amb_frestrict [simp]: "amb (frestrict \<phi> F) = inf (amb F) \<phi>"
  by (simp add: frestrict_def)

section \<open>Frame semantics\<close>

text \<open>Rows have keys, via \<open>rkey\<close>; a frame selects the rows in its ambient filter whose key its
  slice holds at.\<close>

locale frame_sem = pin_slicer proj conj sunit slod sopen coarsen spin
  for proj :: "'l::{distrib_lattice, bounded_lattice_bot} \<Rightarrow> 'k::bounded_complete \<rightarrow> 'k"
    and conj :: "'f \<Rightarrow> 'f \<Rightarrow> 'f" (infixl \<open>\<^bold>*\<close> 70) and sunit :: 'f (\<open>\<^bold>1\<close>)
    and slod sopen coarsen spin +
  fixes rkey :: "'r::pcpo \<rightarrow> 'k"
begin

definition frows :: "('l, 'f, 'r) frame \<Rightarrow> 'r \<Rightarrow> bool" where
  "frows F r \<longleftrightarrow> selects (amb F) r \<and> holds (slice F) (rkey\<cdot>r)"

lemma frows_cong: "amb F = amb F' \<Longrightarrow> slice F = slice F' \<Longrightarrow> frows F = frows F'"
  by (simp add: frows_def fun_eq_iff)

lemma frows_finclude [simp]: "frows (finclude D F) = frows F"
  by (simp add: frows_def fun_eq_iff)

lemma frows_frestrict: "frows (frestrict \<phi> F) r \<longleftrightarrow> frows F r \<and> selects \<phi> r"
  by (auto simp: frows_def)

definition fgroupby :: "'l \<Rightarrow> ('l, 'f, 'r) frame \<Rightarrow> ('l, 'f, 'r) frame" where
  "fgroupby D F = F\<lparr>flod := D, slice := coarsen D (slice F)\<rparr>"

definition fisolate :: "('l, 'f, 'r) frame \<Rightarrow> ('l, 'f, 'r) frame" where
  "fisolate F = \<lparr>flod = bot, amb = top, slice = \<^bold>1\<rparr>"

definition ffor :: "('l \<Rightarrow> 'l) \<Rightarrow> 'f \<Rightarrow> ('l, 'f, 'r) frame \<Rightarrow> ('l, 'f, 'r) frame" where
  "ffor \<tau> G F = F\<lparr>flod := \<tau> (flod F), slice := tf_slice \<tau> (slice F) \<^bold>* G\<rparr>"

definition peg :: "'k \<Rightarrow> ('l, 'f, 'r) frame \<Rightarrow> ('l, 'f, 'r) frame" where
  "peg K F = F\<lparr>slice := slice F \<^bold>* spin K\<rparr>"

lemma flod_peg [simp]: "flod (peg K F) = flod F"
  by (simp add: peg_def)

lemma amb_peg [simp]: "amb (peg K F) = amb F"
  by (simp add: peg_def)

lemma slice_peg [simp]: "slice (peg K F) = slice F \<^bold>* spin K"
  by (simp add: peg_def)

lemma frows_peg_sub: "frows (peg K F) r \<Longrightarrow> frows F r"
  by (simp add: frows_def)

lemma frows_peg: "compact K \<Longrightarrow> frows (peg K F) r \<longleftrightarrow> frows F r \<and> K \<sqsubseteq> rkey\<cdot>r"
  by (auto simp: frows_def holds_spin)

text \<open>Pegging commutes with the transformers, up to truncating the key to what survives.\<close>

lemma peg_finclude: "peg K (finclude D F) = finclude D (peg K F)"
  by (simp add: peg_def finclude_def)

lemma peg_frestrict: "peg K (frestrict \<phi> F) = frestrict \<phi> (peg K F)"
  by (simp add: peg_def frestrict_def)

lemma fgroupby_peg: "compact K \<Longrightarrow> fgroupby D (peg K F) = peg (proj D\<cdot>K) (fgroupby D F)"
  by (simp add: fgroupby_def peg_def coarsen_conj coarsen_spin)

lemma fisolate_peg: "fisolate (peg K F) = fisolate F"
  by (simp add: fisolate_def)

lemma ffor_peg:
  assumes tf: "lod_tf \<tau>" and K: "proj c\<cdot>K = K"
  shows "ffor \<tau> G (peg K F) = peg (proj (\<tau> c)\<cdot>K) (ffor \<tau> G F)"
proof -
  let ?a = "slod (slice F)" and ?b = "slod (spin K)"
  have cK: "compact K" by (metis K proj_compact)
  have bK: "proj ?b\<cdot>K = K" by (rule slod_spin_lives[OF cK])
  have abK: "lives_at (sup ?a ?b) K"
    using lives_at_up[of ?b K "sup ?a ?b"] bK by (simp add: lives_at_def)
  have c1: "coarsen (\<tau> (sup ?a ?b)) (slice F) = coarsen (\<tau> ?a) (slice F)"
    by (subst (1 2) coarsen_slod) (simp add: tf_inf_sup[OF tf] inf_absorb1 tf_below[OF tf])
  have "proj (\<tau> (sup ?a ?b))\<cdot>K = proj (\<tau> c)\<cdot>K"
    by (rule tf_proj_irrelevant[OF tf abK]) (simp add: lives_at_def K)
  then have c2: "coarsen (\<tau> (sup ?a ?b)) (spin K) = spin (proj (\<tau> c)\<cdot>K)"
    by (simp add: coarsen_spin[OF cK])
  show ?thesis
    by (simp add: ffor_def peg_def coarsen_conj c1 c2 conj.assoc conj.commute conj.left_commute)
qed

text \<open>Pegging to a key, then to a finer one, is pegging to the finer one.\<close>

lemma peg_peg_below:
  assumes "compact K'" "compact K" "K' \<sqsubseteq> K"
  shows "peg K (peg K' F) = peg K F"
proof -
  have j: "spin K' \<^bold>* spin K = spin K"
    using spin_join[OF assms(1,2) joinableI[OF assms(3) below_refl]] join_absorbI[OF assms(3)]
    by simp
  show ?thesis by (simp add: peg_def conj.assoc j)
qed

end

section \<open>Pins and key images\<close>

text \<open>The keys a frame has at an LOD are the projections of the data points it selects.  A table
  key must moreover be maximal at its LOD: everything that LOD needs is defined on the rows it
  groups.\<close>

context frame_sem
begin

definition keyimg :: "'r set \<Rightarrow> ('l, 'f, 'r) frame \<Rightarrow> 'l \<Rightarrow> 'k \<Rightarrow> bool" where
  "keyimg S F c k \<longleftrightarrow> (\<exists>x\<in>pts S. frows F x \<and> k = proj c\<cdot>(rkey\<cdot>x))"

definition fkeys :: "'r set \<Rightarrow> ('l, 'f, 'r) frame \<Rightarrow> 'l \<Rightarrow> 'k \<Rightarrow> bool" where
  "fkeys S F c k \<longleftrightarrow> keyimg S F c k \<and> maximal_at c k"

lemma keyimg_cong: "frows F = frows F' \<Longrightarrow> keyimg S F c = keyimg S F' c"
  by (simp add: keyimg_def fun_eq_iff)

lemma fkeys_cong:
  assumes "frows F = frows F'" shows "fkeys S F c = fkeys S F' c"
  unfolding fkeys_def keyimg_cong[OF assms] ..

lemma keyimg_mono: "(\<And>r. frows F r \<Longrightarrow> frows F' r) \<Longrightarrow> keyimg S F c k \<Longrightarrow> keyimg S F' c k"
  unfolding keyimg_def by blast

text \<open>Keys conform to the slice.\<close>

lemma keyimg_slicer: "keyimg S F c k \<Longrightarrow> \<exists>k'. k \<sqsubseteq> k' \<and> holds (slice F) k'"
  unfolding keyimg_def frows_def using proj_below by blast

lemma keyimg_peg_iff: "compact K \<Longrightarrow> keyimg S (peg K F) c K \<longleftrightarrow> keyimg S F c K"
  unfolding keyimg_def by (auto simp: frows_peg proj_below)

lemma fkeys_peg_iff: "compact K \<Longrightarrow> fkeys S (peg K F) c K \<longleftrightarrow> fkeys S F c K"
  by (simp add: fkeys_def keyimg_peg_iff)

text \<open>A frame \<^emph>\<open>pins\<close> a key at an LOD when its slice syntactically entails the key's pin and the
  key is maximal at that LOD; \<open>peg\<close> is the canonical way.  (Pinning is syntactic so that it
  survives coarsening: a slice may pin a key semantically through a condition that coarsening
  loses.)\<close>

definition pins :: "('l, 'f, 'r) frame \<Rightarrow> 'l \<Rightarrow> 'k \<Rightarrow> bool" where
  "pins F L K \<longleftrightarrow> slice F \<^bold>\<le> spin K \<and> maximal_at L K"

lemma pins_compact: "pins F L K \<Longrightarrow> compact K"
  unfolding pins_def by (blast intro: maximal_at_compact)

lemma pins_peg: "maximal_at L K \<Longrightarrow> pins (peg K F) L K"
  by (simp add: pins_def)

lemma frows_pinned: "pins F L K \<Longrightarrow> frows F r \<Longrightarrow> K \<sqsubseteq> rkey\<cdot>r"
  unfolding frows_def pins_def by (blast intro: holds_pinned maximal_at_compact)

text \<open>On a row of a pinning frame, the pinned key is the row's key at the pin's LOD.\<close>

lemma pinned_key:
  assumes "pins F L K" "frows F r"
  shows "proj L\<cdot>(rkey\<cdot>r) = K"
proof -
  have m: "maximal_at L K" using assms(1) by (simp add: pins_def)
  have "proj L\<cdot>K \<sqsubseteq> proj L\<cdot>(rkey\<cdot>r)" using frows_pinned[OF assms] by (rule monofun_cfun_arg)
  then have "K \<sqsubseteq> proj L\<cdot>(rkey\<cdot>r)" by (simp only: maximal_at_lives[OF m])
  then show ?thesis by (rule maximal_at_eq[OF m proj_idem])
qed

text \<open>A key maximal at \<open>c\<close> that conforms to a pinning slice lies above the truncation of the pin,
  and is compatible with it.\<close>

lemma pin_below_key:
  assumes "pins F L K" "maximal_at c K1" "K1 \<sqsubseteq> k'" "holds (slice F) k'"
  shows "proj c\<cdot>K \<sqsubseteq> K1" "K1 \<Up> K"
proof -
  have "K \<sqsubseteq> k'" using assms(1,4) unfolding pins_def by (blast intro: holds_pinned maximal_at_compact)
  show "proj c\<cdot>K \<sqsubseteq> K1" by (rule proj_below_maximal[OF assms(2) \<open>K \<sqsubseteq> k'\<close> assms(3)])
  show "K1 \<Up> K" using assms(3) \<open>K \<sqsubseteq> k'\<close> by (rule joinableI)
qed

end

section \<open>Laws for an abstract semantics\<close>

locale dataspace = frame_sem proj conj sunit slod sopen coarsen spin rkey
  for proj :: "'l::{distrib_lattice, bounded_lattice_bot} \<Rightarrow> 'k::bounded_complete \<rightarrow> 'k"
    and conj :: "'f \<Rightarrow> 'f \<Rightarrow> 'f" (infixl \<open>\<^bold>*\<close> 70) and sunit :: 'f (\<open>\<^bold>1\<close>)
    and slod sopen coarsen spin and rkey :: "'r::pcpo \<rightarrow> 'k" +
  fixes S :: "'r set"
  assumes dataset_S: "dataset S"
begin

subsection \<open>Rows seen through a mask\<close>

text \<open>The data rows in an ambient filter, and among them those whose key passes the slice
  transformed by a mask.  An LOD is read on rows through their keys.\<close>

definition arows :: "'r sel \<Rightarrow> 'r set" where
  "arows \<phi> = {x \<in> pts S. selects \<phi> x}"

definition mrows :: "('l \<Rightarrow> 'l) \<Rightarrow> ('l, 'f, 'r) frame \<Rightarrow> 'r set" where
  "mrows \<rho> F = {x \<in> arows (amb F). holds (tf_slice \<rho> (slice F)) (rkey\<cdot>x)}"

abbreviation rproj :: "'l \<Rightarrow> 'r \<Rightarrow> 'k" where
  "rproj L x \<equiv> proj L\<cdot>(rkey\<cdot>x)"

lemma mrows_cong: "amb F = amb F' \<Longrightarrow> slice F = slice F' \<Longrightarrow> mrows \<rho> F = mrows \<rho> F'"
  by (simp add: mrows_def)

lemma frows_mrows: "x \<in> pts S \<Longrightarrow> frows F x \<Longrightarrow> x \<in> mrows \<rho> F"
  by (simp add: mrows_def arows_def frows_def holds_tf_slice)

text \<open>Reading at a join of LODs is reading at both.\<close>

lemma rproj_sup_fequiv: "relspace.fequiv D (\<lambda>x. (rproj a x, rproj b x)) (rproj (sup a b))"
  unfolding relspace.fequiv_def relspace.determines_rows
proof (intro conjI ballI impI)
  fix d d' assume "rproj (sup a b) d = rproj (sup a b) d'"
  then have "proj a\<cdot>(rproj (sup a b) d) = proj a\<cdot>(rproj (sup a b) d')"
    "proj b\<cdot>(rproj (sup a b) d) = proj b\<cdot>(rproj (sup a b) d')" by simp_all
  then show "(rproj a d, rproj b d) = (rproj a d', rproj b d')" by (simp add: proj_le)
qed (simp add: proj_sup)

text \<open>Two LODs are \<^emph>\<open>equivalent at grain \<open>n\<close> through a mask \<open>\<rho>\<close>\<close> in a frame, together with a
  further row \<open>x\<close>, when their masks are equivalent modulo \<open>n\<close> on those rows (@{const
  relspace.equiv_mod}).  Being a condition on pairs of rows, it survives losing rows; it also
  survives adding the same detail to both sides.\<close>

definition dims_equiv :: "'l \<Rightarrow> ('l \<Rightarrow> 'l) \<Rightarrow> ('l, 'f, 'r) frame \<Rightarrow> 'r \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool" where
  "dims_equiv n \<rho> F x a t \<longleftrightarrow>
     relspace.equiv_mod (insert x (mrows \<rho> F)) (rproj n) (rproj (\<rho> a)) (rproj (\<rho> t))"

lemma dims_equiv_sub:
  assumes "mrows \<rho>' F' \<subseteq> mrows \<rho> F" "dims_equiv n \<rho> F x a t" "\<rho>' a' = \<rho> a" "\<rho>' t' = \<rho> t"
  shows "dims_equiv n \<rho>' F' x a' t'"
  using assms(2) unfolding dims_equiv_def assms(3,4)
  by (rule equiv_mod_subset[rotated]) (use assms(1) in blast)

lemma dims_equiv_sup:
  assumes "mrows \<rho>' F' \<subseteq> mrows \<rho> F" "dims_equiv n \<rho> F x a t"
    and "\<rho>' a' = sup (\<rho> a) c" "\<rho>' t' = sup (\<rho> t) c"
  shows "dims_equiv n \<rho>' F' x a' t'"
proof -
  let ?D = "insert x (mrows \<rho>' F')"
  have "relspace.equiv_mod ?D (rproj n) (rproj (\<rho> a)) (rproj (\<rho> t))"
    using assms(2) unfolding dims_equiv_def
    by (rule equiv_mod_subset[rotated]) (use assms(1) in blast)
  then have "relspace.equiv_mod ?D (rproj n)
      (\<lambda>x. (rproj (\<rho> a) x, rproj c x)) (\<lambda>x. (rproj (\<rho> t) x, rproj c x))"
    by (rule relspace.equiv_mod_pair)
  then show ?thesis unfolding dims_equiv_def assms(3,4)
    by (rule relspace.equiv_mod_fequiv[OF rproj_sup_fequiv rproj_sup_fequiv])
qed

text \<open>A finer grain constrains more pairs of rows, so the equivalence survives coarsening it.\<close>

lemma dims_equiv_natd_le: "n \<le> n' \<Longrightarrow> dims_equiv n' \<rho> F x a t \<Longrightarrow> dims_equiv n \<rho> F x a t"
proof -
  assume le: "n \<le> n'" and e: "dims_equiv n' \<rho> F x a t"
  have "rproj n' d \<noteq> rproj n' d'" if "rproj n d \<noteq> rproj n d'" for d d'
    using that proj_le[OF le, of "rkey\<cdot>d"] proj_le[OF le, of "rkey\<cdot>d'"] by force
  with e show ?thesis unfolding dims_equiv_def relspace.equiv_mod_def by blast
qed

text \<open>An expression's dims hypothesis holds at every pair of its dims.\<close>

definition dims_equivs :: "('l \<times> ('l \<Rightarrow> 'l)) fset \<Rightarrow> ('l, 'f, 'r) frame \<Rightarrow> 'r \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool" where
  "dims_equivs \<Delta> F x a t \<longleftrightarrow> (\<forall>(n, \<rho>) |\<in>| \<Delta>. dims_equiv n \<rho> F x a t)"

lemma dims_equivsD: "dims_equivs \<Delta> F x a t \<Longrightarrow> (n, \<rho>) |\<in>| \<Delta> \<Longrightarrow> dims_equiv n \<rho> F x a t"
  unfolding dims_equivs_def by blast

lemma dims_equivsI: "(\<And>n \<rho>. (n, \<rho>) |\<in>| \<Delta> \<Longrightarrow> dims_equiv n \<rho> F x a t) \<Longrightarrow> dims_equivs \<Delta> F x a t"
  unfolding dims_equivs_def by blast

end

text \<open>A fixed expression has a minimal LOD \<^term>\<open>mind\<close>, dims \<^term>\<open>dims\<close> (pairs of a natural
  LOD and a mask) and a semantics: a map from frames and keys to values, with \<^term>\<open>\<bottom>\<close> for ``no
  entry''.  Its key LOD under a frame is what it decides itself plus the frame's LOD.  The \<^emph>\<open>key
  laws\<close> say that keys conform to the slice, live at the key LOD, and come from data points.  Keys
  need not be maximal: a row missing data (\<open>\<bottom>\<close> in a column) gives a partial key, which no slice
  can pin.  The \<^emph>\<open>peg law\<close> says that pegging the frame to a key does not change the value there;
  the \<^emph>\<open>dims law\<close> says that in frames with the same filters, entries present at the keys a row
  has at two key LODs agree, when for every pair of the dims the masked key LODs are equivalent at
  the natural grain on the masked rows of the frame and that row.  It says nothing about
  presence.  The \<^emph>\<open>effective-LOD law\<close> says that the semantics depends on a frame's LOD only
  through the key LOD.  The slice is compared syntactically, since coarsening is not extensional.
  Combinators are then maps from lawful semantics to lawful semantics.\<close>

locale expr_sem = dataspace +
  fixes mind dims sem
  assumes masks_tf: "(n, \<rho>) |\<in>| dims \<Longrightarrow> lod_tf \<rho>"
    and key_slicer: "sem F k \<noteq> \<bottom> \<Longrightarrow> \<exists>k'. k \<sqsubseteq> k' \<and> holds (slice F) k'"
    and key_lives: "sem F k \<noteq> \<bottom> \<Longrightarrow> proj (sup mind (flod F))\<cdot>k = k"
    and key_data: "sem F k \<noteq> \<bottom> \<Longrightarrow> keyimg S F (sup mind (flod F)) k"
    and peg_law: "compact K \<Longrightarrow> sem (peg K F) K = sem F K"
    and dims_law: "\<lbrakk>amb F = amb F'; slice F = slice F'; x \<in> pts S;
                    dims_equivs dims F x (sup mind (flod F)) (sup mind (flod F'));
                    sem F (rproj (sup mind (flod F)) x) \<noteq> \<bottom>;
                    sem F' (rproj (sup mind (flod F')) x) \<noteq> \<bottom>\<rbrakk>
                   \<Longrightarrow> sem F (rproj (sup mind (flod F)) x) = sem F' (rproj (sup mind (flod F')) x)"
    and eff_law: "\<lbrakk>amb F = amb F'; slice F = slice F'; sup mind (flod F) = sup mind (flod F')\<rbrakk>
                  \<Longrightarrow> sem F = sem F'"
begin

abbreviation "kd F \<equiv> sup mind (flod F)"


text \<open>The compatibility the dims law relies on is automatic: an entry's key is the projection of
  a selected row, and the pin lies below that row's key.\<close>

lemma pinned_entry:
  assumes "pins F L K" "sem F K1 \<noteq> \<bottom>"
  shows "proj (kd F)\<cdot>K \<sqsubseteq> K1" "K1 \<Up> K"
proof -
  obtain x where x: "frows F x" and K1: "K1 = proj (kd F)\<cdot>(rkey\<cdot>x)"
    using key_data[OF assms(2)] by (auto simp: keyimg_def)
  have Kx: "K \<sqsubseteq> rkey\<cdot>x" by (rule frows_pinned[OF assms(1) x])
  then show "proj (kd F)\<cdot>K \<sqsubseteq> K1" unfolding K1 by (rule monofun_cfun_arg)
  show "K1 \<Up> K" unfolding K1 by (rule joinableI[of _ "rkey\<cdot>x"]) (simp_all add: Kx proj_below)
qed

text \<open>Pegging to a coarser key does not change the value either.\<close>

lemma peg_below: "compact K' \<Longrightarrow> compact K \<Longrightarrow> K' \<sqsubseteq> K \<Longrightarrow> sem (peg K' F) K = sem F K"
  by (metis peg_law peg_peg_below)

text \<open>Pegging to a key maximal at the key LOD leaves at most that key.\<close>

theorem strong_peg:
  assumes K: "maximal_at (kd F) K"
  shows "sem (peg K F) k = (if k = K then sem F K else \<bottom>)"
proof (cases "k = K")
  case True then show ?thesis by (simp add: peg_law maximal_at_compact[OF K])
next
  case False
  show ?thesis
  proof (rule ccontr)
    assume "sem (peg K F) k \<noteq> (if k = K then sem F K else \<bottom>)"
    with False have nb: "sem (peg K F) k \<noteq> \<bottom>" by simp
    obtain x where x: "frows (peg K F) x" and kx: "k = proj (kd F)\<cdot>(rkey\<cdot>x)"
      using key_data[OF nb] by (auto simp: keyimg_def)
    have "K \<sqsubseteq> rkey\<cdot>x" using x by (simp add: frows_peg maximal_at_compact[OF K])
    then have "proj (kd F)\<cdot>K \<sqsubseteq> k" unfolding kx by (rule monofun_cfun_arg)
    then have Kk: "K \<sqsubseteq> k" by (simp only: maximal_at_lives[OF K])
    have lv: "proj (kd F)\<cdot>k = k" using key_lives[OF nb] by simp
    from Kk have "k = K" by (rule maximal_at_eq[OF K lv])
    with False show False ..
  qed
qed

text \<open>Through a mask, a pin still fixes the masked truncation of the key.\<close>

lemma masked_pin:
  assumes \<rho>: "lod_tf \<rho>" and K: "maximal_at c K" and h: "holds (tf_slice \<rho> (spin K)) k"
  shows "proj (\<rho> c)\<cdot>k = proj (\<rho> c)\<cdot>K"
proof -
  have cK: "compact K" by (rule maximal_at_compact[OF K])
  have "proj (\<rho> (slod (spin K)))\<cdot>K = proj (\<rho> c)\<cdot>K"
    by (rule tf_proj_irrelevant[OF \<rho>])
      (simp_all add: lives_at_def slod_spin_lives[OF cK] maximal_at_lives[OF K])
  then have "proj (\<rho> c)\<cdot>K \<sqsubseteq> k" using h by (simp add: coarsen_spin[OF cK] holds_spin[OF proj_compact])
  then have "proj (\<rho> c)\<cdot>K \<sqsubseteq> proj (\<rho> c)\<cdot>k" by (metis monofun_cfun_arg proj_idem)
  then show ?thesis by (rule maximal_at_eq[OF maximal_at_proj[OF tf_below[OF \<rho>] K] proj_idem])
qed

text \<open>Values at different levels of detail: an entry of a frame pegged to a finer key sits at
  the truncation of that key and has the finer key's value.  Through the mask, the rows the
  pegged frame sees all have the pinned key's truncation, so the dims law applies.  (Presence
  at the coarser key is not claimed.)\<close>

theorem lod_shift:
  assumes "amb F1 = amb F2" "slice F1 = slice F2" "flod F1 \<le> flod F2" "sem F2 K2 \<noteq> \<bottom>"
    and K2m: "maximal_at (kd F2) K2" and nb: "sem (peg K2 F1) k \<noteq> \<bottom>"
  shows "k = proj (kd F1)\<cdot>K2" "sem (peg K2 F1) k = sem F2 K2"
proof -
  have cK2: "compact K2" by (rule maximal_at_compact[OF K2m])
  obtain x where xS: "x \<in> pts S" and x: "frows (peg K2 F1) x" and kx: "k = rproj (kd F1) x"
    using key_data[OF nb] by (auto simp: keyimg_def)
  have Kx: "K2 \<sqsubseteq> rkey\<cdot>x" using x by (simp add: frows_peg cK2)
  have sub: "kd F1 \<le> kd F2" using assms(3) by (rule sup_mono[OF order_refl])
  have km1: "maximal_at (kd F1) (proj (kd F1)\<cdot>K2)" by (rule maximal_at_proj[OF sub K2m])
  have "proj (kd F1)\<cdot>K2 \<sqsubseteq> k" unfolding kx using Kx by (rule monofun_cfun_arg)
  then show "k = proj (kd F1)\<cdot>K2" using key_lives[OF nb] by (intro maximal_at_eq[OF km1]) simp_all
  have x2: "rproj (kd F2) x = K2"
  proof -
    have "proj (kd F2)\<cdot>K2 \<sqsubseteq> rproj (kd F2) x" using Kx by (rule monofun_cfun_arg)
    then have "K2 \<sqsubseteq> rproj (kd F2) x" by (simp only: maximal_at_lives[OF K2m])
    then show ?thesis by (rule maximal_at_eq[OF K2m proj_idem])
  qed
  have f: "amb (peg K2 F2) = amb (peg K2 F1)" "slice (peg K2 F2) = slice (peg K2 F1)"
    by (simp_all add: assms(1,2))
  have eq1: "dims_equiv n \<rho> (peg K2 F2) x (kd (peg K2 F2)) (kd (peg K2 F1))"
    if n\<rho>: "(n, \<rho>) |\<in>| dims" for n \<rho>
  proof -
    have \<rho>: "lod_tf \<rho>" by (rule masks_tf[OF n\<rho>])
    have pin: "rproj (\<rho> (kd F2)) y = proj (\<rho> (kd F2))\<cdot>K2"
      if "y \<in> insert x (mrows \<rho> (peg K2 F2))" for y
    proof -
      from that tf_slice_conj[OF \<rho>, of "slice F2" "spin K2"]
      consider "y = x" | "holds (tf_slice \<rho> (spin K2)) (rkey\<cdot>y)"
        by (auto simp: mrows_def)
      then show ?thesis
      proof cases
        case 1
        then show ?thesis using proj_le[OF tf_below[OF \<rho>], of "kd F2" "rkey\<cdot>x"] x2 by simp
      next
        case 2
        then show ?thesis by (rule masked_pin[OF \<rho> K2m])
      qed
    qed
    show ?thesis
      unfolding dims_equiv_def relspace.equiv_mod_def
    proof (intro ballI impI)
      fix y y' assume y: "y \<in> insert x (mrows \<rho> (peg K2 F2))"
        and y': "y' \<in> insert x (mrows \<rho> (peg K2 F2))"
      have e2: "rproj (\<rho> (kd F2)) y = rproj (\<rho> (kd F2)) y'" using pin[OF y] pin[OF y'] by simp
      then have "rproj (\<rho> (kd F1)) y = rproj (\<rho> (kd F1)) y'"
        by (metis proj_le[OF tf_mono[OF \<rho> sub]])
      with e2 show "(rproj (\<rho> (kd (peg K2 F2))) y = rproj (\<rho> (kd (peg K2 F2))) y') =
                    (rproj (\<rho> (kd (peg K2 F1))) y = rproj (\<rho> (kd (peg K2 F1))) y')"
        by simp
    qed
  qed
  have eq: "dims_equivs dims (peg K2 F2) x (kd (peg K2 F2)) (kd (peg K2 F1))"
    by (rule dims_equivsI) (rule eq1)
  have "sem (peg K2 F2) (rproj (kd (peg K2 F2)) x) = sem (peg K2 F1) (rproj (kd (peg K2 F1)) x)"
    by (rule dims_law[OF f xS eq]) (simp_all add: x2 peg_law[OF cK2] assms(4) kx[symmetric] nb)
  then show "sem (peg K2 F1) k = sem F2 K2" by (simp add: x2 peg_law[OF cK2] kx)
qed

end

text \<open>Within a dataspace, a semantics is \<^emph>\<open>lawful\<close> when it forms an \<^locale>\<open>expr_sem\<close>
  instance; combinators are then plain theorems concluding lawfulness.\<close>

context dataspace
begin

abbreviation lawful where "lawful \<equiv> expr_sem proj conj sunit slod sopen coarsen spin rkey S"

lemma lawfulI:
  assumes "\<And>n \<rho>. (n, \<rho>) |\<in>| dims \<Longrightarrow> lod_tf \<rho>"
    and "\<And>F k. sem F k \<noteq> \<bottom> \<Longrightarrow> \<exists>k'. k \<sqsubseteq> k' \<and> holds (slice F) k'"
    and "\<And>F k. sem F k \<noteq> \<bottom> \<Longrightarrow> proj (sup mind (flod F))\<cdot>k = k"
    and "\<And>F k. sem F k \<noteq> \<bottom> \<Longrightarrow> keyimg S F (sup mind (flod F)) k"
    and "\<And>F K. compact K \<Longrightarrow> sem (peg K F) K = sem F K"
    and "\<And>F F' x. \<lbrakk>amb F = amb F'; slice F = slice F'; x \<in> pts S;
                    dims_equivs dims F x (sup mind (flod F)) (sup mind (flod F'));
                    sem F (rproj (sup mind (flod F)) x) \<noteq> \<bottom>;
                    sem F' (rproj (sup mind (flod F')) x) \<noteq> \<bottom>\<rbrakk>
                   \<Longrightarrow> sem F (rproj (sup mind (flod F)) x) = sem F' (rproj (sup mind (flod F')) x)"
    and "\<And>F F'. \<lbrakk>amb F = amb F'; slice F = slice F'; sup mind (flod F) = sup mind (flod F')\<rbrakk>
                 \<Longrightarrow> sem F = sem F'"
  shows "lawful mind dims sem"
  by (intro expr_sem.intro dataspace_axioms expr_sem_axioms.intro) (fact assms)+

abbreviation lawfulE where "lawfulE E \<equiv> lawful (emind E) (edims E) (esem E)"

subsection \<open>Conforming to data\<close>

text \<open>The \<^emph>\<open>guard\<close> keeps an entry only at keys of the data.  Simple constructions (maps,
  collections, constants) need not conform to data on their own: they agree with a lawful
  semantics at the data keys, and a single guard where they enter an aggregation, or the
  output, restores the key-data law.\<close>

definition guard :: "('l, 'f, 'r, 'k, 'v::pcpo) expr \<Rightarrow> ('l, 'f, 'r, 'k, 'v) expr" where
  "guard E = E\<lparr>esem := \<lambda>F k. if keyimg S F (sup (emind E) (flod F)) k then esem E F k else \<bottom>\<rparr>"

lemma guard_simps [simp]:
  "emind (guard E) = emind E" "edims (guard E) = edims E"
  "esem (guard E) F k = (if keyimg S F (sup (emind E) (flod F)) k then esem E F k else \<bottom>)"
  by (simp_all add: guard_def)

lemma guard_idem [simp]: "guard (guard E) = guard E"
  by (cases E) (simp add: guard_def fun_eq_iff)

lemma guard_lawful: "lawfulE E \<Longrightarrow> guard E = E"
proof -
  assume "lawfulE E"
  then interpret E: expr_sem proj conj sunit slod sopen coarsen spin rkey S
    "emind E" "edims E" "esem E" .
  have v: "(if keyimg S F (sup (emind E) (flod F)) k then esem E F k else \<bottom>) = esem E F k"
    for F k using E.key_data[of F k] by auto
  show "guard E = E" unfolding guard_def v by simp
qed

subsection \<open>Maps\<close>

text \<open>Applying a strict function to every entry.\<close>

definition smap :: "('v::pcpo \<rightarrow> 'w::pcpo) \<Rightarrow> ('l, 'f, 'r, 'k, 'v) expr \<Rightarrow> ('l, 'f, 'r, 'k, 'w) expr"
  where "smap g E = \<lparr>emind = emind E, edims = edims E, esem = \<lambda>F k. g\<cdot>(esem E F k)\<rparr>"

lemma smap_simps [simp]:
  "emind (smap g E) = emind E" "edims (smap g E) = edims E"
  "esem (smap g E) F k = g\<cdot>(esem E F k)"
  by (simp_all add: smap_def)

theorem lawful_smap: assumes "lawfulE E" "g\<cdot>\<bottom> = \<bottom>" shows "lawfulE (smap g E)"
proof -
  interpret E: expr_sem proj conj sunit slod sopen coarsen spin rkey S
    "emind E" "edims E" "esem E"
    by (fact assms(1))
  have nb: "esem E F k \<noteq> \<bottom>" if "g\<cdot>(esem E F k) \<noteq> \<bottom>" for F k
    using that assms(2) by auto
  show ?thesis
  proof (rule lawfulI, simp_all only: smap_simps)
    show "lod_tf \<rho>" if "(n, \<rho>) |\<in>| edims E" for n \<rho> by (rule E.masks_tf[OF that])
  next
    fix F :: "('l, 'f, 'r) frame" and k :: 'k assume "g\<cdot>(esem E F k) \<noteq> \<bottom>"
    then show "\<exists>k'. k \<sqsubseteq> k' \<and> holds (slice F) k'" by (rule E.key_slicer[OF nb])
  next
    fix F :: "('l, 'f, 'r) frame" and k :: 'k assume "g\<cdot>(esem E F k) \<noteq> \<bottom>"
    then show "proj (sup (emind E) (flod F))\<cdot>k = k" by (rule E.key_lives[OF nb])
  next
    fix F :: "('l, 'f, 'r) frame" and k :: 'k assume "g\<cdot>(esem E F k) \<noteq> \<bottom>"
    then show "keyimg S F (sup (emind E) (flod F)) k" by (rule E.key_data[OF nb])
  next
    fix F :: "('l, 'f, 'r) frame" and K :: 'k assume "compact K"
    then show "g\<cdot>(esem E (peg K F) K) = g\<cdot>(esem E F K)" by (simp only: E.peg_law)
  next
    fix F F' :: "('l, 'f, 'r) frame" and x :: 'r
    assume a: "amb F = amb F'" "slice F = slice F'" "x \<in> pts S"
      "dims_equivs (edims E) F x (sup (emind E) (flod F)) (sup (emind E) (flod F'))"
      "g\<cdot>(esem E F (rproj (sup (emind E) (flod F)) x)) \<noteq> \<bottom>"
      "g\<cdot>(esem E F' (rproj (sup (emind E) (flod F')) x)) \<noteq> \<bottom>"
    show "g\<cdot>(esem E F (rproj (sup (emind E) (flod F)) x))
        = g\<cdot>(esem E F' (rproj (sup (emind E) (flod F')) x))"
      by (simp only: E.dims_law[OF a(1-4) nb[OF a(5)] nb[OF a(6)]])
  next
    fix F F' :: "('l, 'f, 'r) frame"
    assume "amb F = amb F'" "slice F = slice F'" "sup (emind E) (flod F) = sup (emind E) (flod F')"
    then have "esem E F = esem E F'" by (rule E.eff_law)
    then show "esem (smap g E) F = esem (smap g E) F'" by (simp add: fun_eq_iff)
  qed
qed

lemma guard_smap: "g\<cdot>\<bottom> = \<bottom> \<Longrightarrow> guard (smap g E) = smap g (guard E)"
  by (cases E) (simp add: guard_def smap_def fun_eq_iff)

corollary lawful_guard_smap:
  assumes "lawfulE (guard E)" "g\<cdot>\<bottom> = \<bottom>" shows "lawfulE (guard (smap g E))"
  unfolding guard_smap[OF assms(2)] by (rule lawful_smap[OF assms])
end

section \<open>Combinators\<close>

subsection \<open>\<open>INCLUDE\<close>\<close>

definition group_by where
  "group_by D sem = (\<lambda>F. sem (finclude D F))"

theorem (in expr_sem) lawful_group_by:
  "lawful (sup mind D) dims (group_by D sem)"
proof (rule lawfulI)
  have kd: "sup (sup mind D) X = sup mind (sup X D)" for X by (simp only: ac_simps)
  show "lod_tf \<rho>" if "(n, \<rho>) |\<in>| dims" for n \<rho> by (rule masks_tf[OF that])
  show "\<exists>k'. k \<sqsubseteq> k' \<and> holds (slice F) k'" if "group_by D sem F k \<noteq> \<bottom>" for F k
    using key_slicer[of "finclude D F" k] that by (simp add: group_by_def)
  show "proj (sup (sup mind D) (flod F))\<cdot>k = k" if "group_by D sem F k \<noteq> \<bottom>" for F k
    using key_lives[of "finclude D F" k] that by (simp add: group_by_def kd)
  show "keyimg S F (sup (sup mind D) (flod F)) k" if "group_by D sem F k \<noteq> \<bottom>" for F k
    using key_data[of "finclude D F" k] that keyimg_cong[of "finclude D F" F S]
    by (simp add: group_by_def kd)
  show "group_by D sem (peg K F) K = group_by D sem F K" if "compact K" for F K
    by (simp add: group_by_def peg_finclude[symmetric] peg_law[OF that])
  show "group_by D sem F (rproj (sup (sup mind D) (flod F)) x)
      = group_by D sem F' (rproj (sup (sup mind D) (flod F')) x)"
    if "amb F = amb F'" "slice F = slice F'" "x \<in> pts S"
      "dims_equivs dims F x (sup (sup mind D) (flod F)) (sup (sup mind D) (flod F'))"
      "group_by D sem F (rproj (sup (sup mind D) (flod F)) x) \<noteq> \<bottom>"
      "group_by D sem F' (rproj (sup (sup mind D) (flod F')) x) \<noteq> \<bottom>"
    for F F' x
  proof -
    have "dims_equivs dims (finclude D F) x (kd (finclude D F)) (kd (finclude D F'))"
      using that(4) by (simp add: dims_equivs_def dims_equiv_def mrows_def kd)
    then show ?thesis
      using dims_law[of "finclude D F" "finclude D F'" x] that(1-3,5,6)
      by (simp add: group_by_def kd)
  qed
  show "group_by D sem F = group_by D sem F'"
    if "amb F = amb F'" "slice F = slice F'" "sup (sup mind D) (flod F) = sup (sup mind D) (flod F')"
    for F F'
  proof -
    have "sem (finclude D F) = sem (finclude D F')"
      by (rule eff_law) (use that in \<open>simp_all add: kd\<close>)
    then show ?thesis by (simp add: group_by_def)
  qed
qed

subsection \<open>Fixed-level constructs: \<open>GROUP BY ONLY\<close>, \<open>TOTAL\<close>, \<open>ISOLATE\<close>\<close>

text \<open>A construct that evaluates its argument under a transformed frame at a fixed LOD
  \<^term>\<open>E\<close>, broadcast back to the incoming frame's keys: it reads only the \<open>E\<close>-part of a key.  It
  is lawful whenever the transformer sees the incoming frame only through its filters, and
  pegging the incoming frame does not change the inner value at the truncated key.  This needs
  nothing of the inner semantics, and its dims law holds unconditionally: it has no dims.\<close>

context dataspace
begin

definition fixed where
  "fixed E T sem F k = (if fkeys S F (sup E (flod F)) k then sem (T F) (proj E\<cdot>k) else \<bottom>)"

theorem lawful_fixed:
  assumes "\<And>F K. compact K \<Longrightarrow> sem (T (peg K F)) (proj E\<cdot>K) = sem (T F) (proj E\<cdot>K)"
    and "\<And>F F'. amb F = amb F' \<Longrightarrow> slice F = slice F' \<Longrightarrow> T F = T F'"
  shows "lawful E {||} (fixed E T sem)"
proof (rule lawfulI)
  show "lod_tf \<rho>" if "(n, \<rho>) |\<in>| {||}" for n :: 'l and \<rho> :: "'l \<Rightarrow> 'l" using that by simp
  show "\<exists>k'. k \<sqsubseteq> k' \<and> holds (slice F) k'" if "fixed E T sem F k \<noteq> \<bottom>" for F k
    using that by (auto simp: fixed_def fkeys_def split: if_splits dest: keyimg_slicer)
  show "proj (sup E (flod F))\<cdot>k = k" if "fixed E T sem F k \<noteq> \<bottom>" for F k
    using that by (auto simp: fixed_def fkeys_def split: if_splits dest: maximal_at_lives)
  show "keyimg S F (sup E (flod F)) k" if "fixed E T sem F k \<noteq> \<bottom>" for F k
    using that by (auto simp: fixed_def fkeys_def split: if_splits)
  show "fixed E T sem (peg K F) K = fixed E T sem F K" if "compact K" for F K
    by (simp add: fixed_def fkeys_peg_iff[OF that] assms(1)[OF that])
  show "fixed E T sem F (rproj (sup E (flod F)) x) = fixed E T sem F' (rproj (sup E (flod F')) x)"
    if "amb F = amb F'" "slice F = slice F'" "x \<in> pts S"
      "dims_equivs {||} F x (sup E (flod F)) (sup E (flod F'))"
      "fixed E T sem F (rproj (sup E (flod F)) x) \<noteq> \<bottom>"
      "fixed E T sem F' (rproj (sup E (flod F')) x) \<noteq> \<bottom>" for F F' x
  proof -
    have "proj E\<cdot>(rproj (sup E (flod G)) x) = rproj E x" for G :: "('l, 'f, 'r) frame"
      by (simp add: proj_le)
    moreover have "T F' = T F" using assms(2)[OF that(1,2)] by simp
    ultimately show ?thesis using that(5,6) by (simp add: fixed_def split: if_splits)
  qed
  show "fixed E T sem F = fixed E T sem F'"
    if "amb F = amb F'" "slice F = slice F'" "sup E (flod F) = sup E (flod F')"
    for F F'
  proof -
    have "fkeys S F (sup E (flod F)) = fkeys S F' (sup E (flod F'))"
      using fkeys_cong[OF frows_cong[OF that(1,2)]] that(3) by simp
    then show ?thesis using assms(2)[OF that(1,2)] by (simp add: fixed_def fun_eq_iff)
  qed
qed

end

context expr_sem
begin

definition group_by_only where
  "group_by_only D = fixed (sup mind D) (fgroupby D) sem"

abbreviation total where
  "total \<equiv> group_by_only bot"

theorem lawful_group_by_only:
  "lawful (sup mind D) {||} (group_by_only D)"
  unfolding group_by_only_def
proof (rule lawful_fixed)
  show "sem (fgroupby D (peg K F)) (proj (sup mind D)\<cdot>K) = sem (fgroupby D F) (proj (sup mind D)\<cdot>K)"
    if "compact K" for F K
    by (simp add: fgroupby_peg[OF that] peg_below[OF proj_compact proj_compact proj_mono])
  show "fgroupby D F = fgroupby D F'" if "amb F = amb F'" "slice F = slice F'" for F F'
    using that by (cases F, cases F') (simp add: fgroupby_def)
qed

definition isolate where
  "isolate = fixed mind fisolate sem"

theorem lawful_isolate: "lawful mind {||} isolate"
  unfolding isolate_def
  by (rule lawful_fixed) (simp_all add: fisolate_peg fisolate_def)

end

subsection \<open>\<open>FOR\<close> and \<open>EXCLUDE\<close>\<close>

text \<open>\<open>E FOR \<tau> G\<close> is evaluated at the incoming frame's keys, truncated to the key LOD of the inner
  frame.  The key LOD of the inner frame is the expression's own detail plus the transformed key
  LOD of the outer one.\<close>

context expr_sem
begin

definition filtfor where
  "filtfor \<tau> G F k =
     (if fkeys S F (kd F) k then sem (ffor \<tau> G F) (proj (kd (ffor \<tau> G F))\<cdot>k) else \<bottom>)"

abbreviation exclude where
  "exclude \<tau> \<equiv> filtfor \<tau> \<^bold>1"

lemma flod_ffor [simp]: "flod (ffor \<tau> G F) = \<tau> (flod F)"
  by (simp add: ffor_def)

lemma amb_ffor [simp]: "amb (ffor \<tau> G F) = amb F"
  by (simp add: ffor_def)

lemma kd_ffor:
  assumes tf: "lod_tf \<tau>" shows "sup mind (\<tau> (flod F)) = sup mind (\<tau> (kd F))"
  using tf_below[OF tf, of mind] by (simp add: tf_sup[OF tf] sup_absorb1 sup_assoc[symmetric])

lemma kd_ffor_le: assumes tf: "lod_tf \<tau>" shows "kd (ffor \<tau> G F) \<le> kd F"
  by (simp only: flod_ffor) (intro sup_mono order_refl tf_below[OF tf])

lemma kd_ffor_tf: assumes tf: "lod_tf \<tau>" shows "\<tau> (kd F) \<le> kd (ffor \<tau> G F)"
  by (simp only: flod_ffor kd_ffor[OF tf]) (rule sup_ge2)

text \<open>Through any mask, the inner frame's masked rows are among the outer frame's rows masked by
  the composite, and its masked key LOD is the composite's, plus the masked detail of the
  expression itself.  \<open>FOR\<close> composes every mask of the dims with \<open>\<tau>\<close>.\<close>

lemma mrows_ffor:
  assumes \<rho>: "lod_tf \<rho>" and tf: "lod_tf \<tau>" shows "mrows \<rho> (ffor \<tau> G F) \<subseteq> mrows (\<rho> \<circ> \<tau>) F"
  using tf_slice_conj[OF \<rho>, of "tf_slice \<tau> (slice F)" G] tf_slice_comp[OF \<rho> tf, of "slice F"]
  by (auto simp: mrows_def ffor_def)

lemma mask_kd_ffor:
  assumes \<rho>: "lod_tf \<rho>" and tf: "lod_tf \<tau>"
  shows "\<rho> (kd (ffor \<tau> G F)) = sup ((\<rho> \<circ> \<tau>) (kd F)) (\<rho> mind)"
proof -
  have le: "\<rho> (\<tau> mind) \<le> \<rho> mind" by (rule tf_mono[OF \<rho> tf_below[OF tf]])
  have "\<rho> (kd (ffor \<tau> G F)) = sup (\<rho> mind) (\<rho> (\<tau> (flod F)))"
    by (simp add: tf_sup[OF \<rho>])
  also have "\<dots> = sup (\<rho> mind) (sup (\<rho> (\<tau> mind)) (\<rho> (\<tau> (flod F))))"
    by (simp only: sup_assoc[symmetric] sup_absorb1[OF le])
  also have "\<dots> = sup ((\<rho> \<circ> \<tau>) (kd F)) (\<rho> mind)"
    by (simp add: tf_sup[OF \<rho>] tf_sup[OF tf] sup_commute)
  finally show ?thesis .
qed

lemma lod_tf_comp: "lod_tf \<rho> \<Longrightarrow> lod_tf \<tau> \<Longrightarrow> lod_tf (\<rho> \<circ> \<tau>)"
  unfolding lod_tf_def by simp

abbreviation for_dims :: "('l \<Rightarrow> 'l) \<Rightarrow> ('l \<times> ('l \<Rightarrow> 'l)) fset \<Rightarrow> ('l \<times> ('l \<Rightarrow> 'l)) fset" where
  "for_dims \<tau> \<Delta> \<equiv> (\<lambda>(n, \<rho>). (n, \<rho> \<circ> \<tau>)) |`| \<Delta>"

theorem lawful_filtfor:
  assumes tf: "lod_tf \<tau>" shows "lawful mind (for_dims \<tau> dims) (filtfor \<tau> G)"
proof (rule lawfulI)
  show "lod_tf \<rho>'" if "(n, \<rho>') |\<in>| for_dims \<tau> dims" for n \<rho>'
    using that by (auto intro: lod_tf_comp[OF masks_tf tf])
  show "\<exists>k'. k \<sqsubseteq> k' \<and> holds (slice F) k'" if "filtfor \<tau> G F k \<noteq> \<bottom>" for F k
    using that by (auto simp: filtfor_def fkeys_def split: if_splits dest: keyimg_slicer)
  show "proj (kd F)\<cdot>k = k" if "filtfor \<tau> G F k \<noteq> \<bottom>" for F k
    using that by (auto simp: filtfor_def fkeys_def split: if_splits dest: maximal_at_lives)
  show "keyimg S F (kd F) k" if "filtfor \<tau> G F k \<noteq> \<bottom>" for F k
    using that by (auto simp: filtfor_def fkeys_def split: if_splits)
  show "filtfor \<tau> G (peg K F) K = filtfor \<tau> G F K" if cK: "compact K" for F K
  proof (cases "fkeys S F (kd F) K")
    case False
    then show ?thesis by (simp add: filtfor_def fkeys_peg_iff[OF cK])
  next
    case True
    let ?H = "ffor \<tau> G F" and ?K' = "proj (\<tau> (kd F))\<cdot>K"
    have Kl: "proj (kd F)\<cdot>K = K" using True by (simp add: fkeys_def maximal_at_lives)
    have "?K' \<sqsubseteq> proj (kd ?H)\<cdot>K" by (rule proj_mono[OF kd_ffor_tf[OF tf]])
    then have "sem (peg ?K' ?H) (proj (kd ?H)\<cdot>K) = sem ?H (proj (kd ?H)\<cdot>K)"
      by (rule peg_below[OF proj_compact proj_compact])
    then show ?thesis
      using True by (simp add: filtfor_def fkeys_peg_iff[OF cK] ffor_peg[OF tf Kl])
  qed
  show "filtfor \<tau> G F (rproj (kd F) x) = filtfor \<tau> G F' (rproj (kd F') x)"
    if "amb F = amb F'" "slice F = slice F'" "x \<in> pts S"
      "dims_equivs (for_dims \<tau> dims) F x (kd F) (kd F')"
      "filtfor \<tau> G F (rproj (kd F) x) \<noteq> \<bottom>" "filtfor \<tau> G F' (rproj (kd F') x) \<noteq> \<bottom>" for F F' x
  proof -
    let ?H = "ffor \<tau> G F" and ?H' = "ffor \<tau> G F'"
    have v: "filtfor \<tau> G F0 (rproj (kd F0) x) = sem (ffor \<tau> G F0) (rproj (kd (ffor \<tau> G F0)) x)"
      if "filtfor \<tau> G F0 (rproj (kd F0) x) \<noteq> \<bottom>" for F0
      using that proj_le[OF kd_ffor_le[OF tf, of G F0]] by (simp add: filtfor_def split: if_splits)
    have fH: "amb ?H = amb ?H'" "slice ?H = slice ?H'" by (simp_all add: ffor_def that(1,2))
    have eq: "dims_equivs dims ?H x (kd ?H) (kd ?H')"
    proof (rule dims_equivsI)
      fix n \<rho> assume n\<rho>: "(n, \<rho>) |\<in>| dims"
      have \<rho>: "lod_tf \<rho>" by (rule masks_tf[OF n\<rho>])
      have "dims_equiv n (\<rho> \<circ> \<tau>) F x (kd F) (kd F')"
        by (rule dims_equivsD[OF that(4)]) (use n\<rho> in force)
      then show "dims_equiv n \<rho> ?H x (kd ?H) (kd ?H')"
        by (rule dims_equiv_sup[OF mrows_ffor[OF \<rho> tf] _ mask_kd_ffor[OF \<rho> tf] mask_kd_ffor[OF \<rho> tf]])
    qed
    have "sem ?H (rproj (kd ?H) x) = sem ?H' (rproj (kd ?H') x)"
      by (rule dims_law[OF fH that(3) eq]) (use that(5,6) v in simp_all)
    then show ?thesis using v[OF that(5)] v[OF that(6)] by simp
  qed
  show "filtfor \<tau> G F = filtfor \<tau> G F'"
    if "amb F = amb F'" "slice F = slice F'" "kd F = kd F'" for F F'
  proof -
    have k: "fkeys S F (kd F) = fkeys S F' (kd F')"
      using fkeys_cong[OF frows_cong[OF that(1,2)]] that(3) by simp
    have kH: "kd (ffor \<tau> G F) = kd (ffor \<tau> G F')" by (simp only: flod_ffor kd_ffor[OF tf] that(3))
    have "sem (ffor \<tau> G F) = sem (ffor \<tau> G F')"
      by (rule eff_law) (use that kH in \<open>simp_all add: ffor_def\<close>)
    then show ?thesis using k kH by (simp add: filtfor_def fun_eq_iff)
  qed
qed

end

subsection \<open>\<open>RESTRICT\<close>\<close>

definition restrict where
  "restrict \<phi> sem = (\<lambda>F. sem (frestrict \<phi> F))"

theorem (in expr_sem) lawful_restrict: "lawful mind dims (restrict \<phi> sem)"
proof (rule lawfulI)
  show "lod_tf \<rho>" if "(n, \<rho>) |\<in>| dims" for n \<rho> by (rule masks_tf[OF that])
  show "\<exists>k'. k \<sqsubseteq> k' \<and> holds (slice F) k'" if "restrict \<phi> sem F k \<noteq> \<bottom>" for F k
    using key_slicer[of "frestrict \<phi> F" k] that by (simp add: restrict_def)
  show "proj (kd F)\<cdot>k = k" if "restrict \<phi> sem F k \<noteq> \<bottom>" for F k
    using key_lives[of "frestrict \<phi> F" k] that by (simp add: restrict_def)
  show "keyimg S F (kd F) k" if "restrict \<phi> sem F k \<noteq> \<bottom>" for F k
    using key_data[of "frestrict \<phi> F" k] that keyimg_mono[of "frestrict \<phi> F" F S]
    by (simp add: restrict_def frows_frestrict)
  show "restrict \<phi> sem (peg K F) K = restrict \<phi> sem F K" if "compact K" for F K
    by (simp add: restrict_def peg_frestrict[symmetric] peg_law[OF that])
  show "restrict \<phi> sem F (rproj (kd F) x) = restrict \<phi> sem F' (rproj (kd F') x)"
    if "amb F = amb F'" "slice F = slice F'" "x \<in> pts S"
      "dims_equivs dims F x (kd F) (kd F')"
      "restrict \<phi> sem F (rproj (kd F) x) \<noteq> \<bottom>" "restrict \<phi> sem F' (rproj (kd F') x) \<noteq> \<bottom>" for F F' x
  proof -
    text \<open>Restricting loses rows, which the equivalence survives.\<close>
    have "dims_equivs dims (frestrict \<phi> F) x (kd (frestrict \<phi> F)) (kd (frestrict \<phi> F'))"
    proof (rule dims_equivsI)
      fix n \<rho> assume "(n, \<rho>) |\<in>| dims"
      then show "dims_equiv n \<rho> (frestrict \<phi> F) x (kd (frestrict \<phi> F)) (kd (frestrict \<phi> F'))"
        by (intro dims_equiv_sub[OF _ dims_equivsD[OF that(4)]]) (auto simp: mrows_def arows_def)
    qed
    then show ?thesis
      using dims_law[of "frestrict \<phi> F" "frestrict \<phi> F'" x] that by (simp add: restrict_def)
  qed
  show "restrict \<phi> sem F = restrict \<phi> sem F'"
    if "amb F = amb F'" "slice F = slice F'" "kd F = kd F'" for F F'
  proof -
    have "sem (frestrict \<phi> F) = sem (frestrict \<phi> F')"
      by (rule eff_law) (use that in simp_all)
    then show ?thesis by (simp add: restrict_def)
  qed
qed

end