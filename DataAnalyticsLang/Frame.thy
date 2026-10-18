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

text \<open>The meaning of an expression: the LOD it decides at least; its \<^emph>\<open>dims\<close>, a map from
  \<^emph>\<open>masks\<close> (the part of a key's detail some values actually read; dropped detail is broadcast) to
  \<^emph>\<open>natural\<close> LODs (the key those values are read out of the dataset at), \<open>\<bottom>\<close> for none; the
  bottom mask, which reads nothing, carries the join of them all, the expression's natural grain;
  and its entries: at each frame, a finite map from keys to values.  Natural LODs of one mask combine by join
  (@{text dims_equiv_sup_natd}), so a collection joins its components' maps and its dims law is as
  weak as theirs; a broadcast needs none.\<close>

record ('l::distrib_lattice, 'f::type, 'r::pcpo, 'k::type, 'v::type) expr =
  emind :: 'l
  edims :: "'l \<Rightarrow> 'l"
  esem :: "('l, 'f, 'r) frame \<Rightarrow> 'k \<rightharpoonup> 'v"

text \<open>The record packages' own \<open>truncate\<close> operations would shadow the truncation action.\<close>

hide_const (open) frame.truncate expr.truncate

section \<open>Frame transformers\<close>

text \<open>The level-of-detail constructs act on the frame an inner expression is evaluated under.
  \<open>INCLUDE D\<close> adds detail \<open>D\<close>; \<open>RESTRICT \<phi>\<close> adds \<open>\<phi>\<close> to the ambient filter.  The others need the
  slicer: \<open>GROUP BY ONLY D\<close> replaces the LOD by \<open>D\<close> and coarsens the slice to it (\<open>TOTAL\<close> is
  \<open>GROUP BY ONLY \<bottom>\<close>); \<open>ISOLATE\<close> evaluates under the empty frame, with neither filter; \<open>E FOR \<tau> G\<close>
  drops detail by a truncation \<open>\<tau>\<close>, from the frame and from the slice, and conjoins \<open>G\<close>
  (\<open>EXCLUDE\<close> is \<open>FOR \<tau> \<^bold>1\<close>).\<close>

definition finclude :: "'l::po \<Rightarrow> ('l, 'f::type, 'r::pcpo) frame \<Rightarrow> ('l, 'f, 'r) frame" where
  "finclude D F = F\<lparr>flod := flod F \<squnion> D\<rparr>"

lemma flod_finclude [simp]: "flod (finclude D F) = flod F \<squnion> D"
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

locale frame_sem = pin_slicer conj sunit slod sopen coarsen spin
  for conj :: "'f \<Rightarrow> 'f \<Rightarrow> 'f" (infixl \<open>\<^bold>*\<close> 70) and sunit :: 'f (\<open>\<^bold>1\<close>)
    and slod :: "'f \<Rightarrow> 'k::{dI, locally_finitely_detailed} semi_factor" and sopen :: "'f \<Rightarrow> 'k sel"
    and coarsen spin +
  fixes rkey :: "'r::pcpo \<rightarrow> 'k"
begin

definition frows :: "('k semi_factor, 'f, 'r) frame \<Rightarrow> 'r \<Rightarrow> bool" where
  "frows F r \<longleftrightarrow> selects (amb F) r \<and> holds (slice F) (rkey\<cdot>r)"

lemma frows_cong: "amb F = amb F' \<Longrightarrow> slice F = slice F' \<Longrightarrow> frows F = frows F'"
  by (simp add: frows_def fun_eq_iff)

lemma frows_finclude [simp]: "frows (finclude D F) = frows F"
  by (simp add: frows_def fun_eq_iff)

lemma frows_frestrict: "frows (frestrict \<phi> F) r \<longleftrightarrow> frows F r \<and> selects \<phi> r"
  by (auto simp: frows_def)

definition fgroupby :: "'k semi_factor \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> ('k semi_factor, 'f, 'r) frame" where
  "fgroupby D F = F\<lparr>flod := D, slice := coarsen D (slice F)\<rparr>"

definition fisolate :: "('k semi_factor, 'f, 'r) frame \<Rightarrow> ('k semi_factor, 'f, 'r) frame" where
  "fisolate F = \<lparr>flod = \<bottom>, amb = top, slice = \<^bold>1\<rparr>"

definition ffor :: "'k semi_factor \<Rightarrow> 'f \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> ('k semi_factor, 'f, 'r) frame" where
  "ffor \<tau> G F = F\<lparr>flod := truncate \<tau> (flod F), slice := coarsen \<tau> (slice F) \<^bold>* G\<rparr>"

definition peg :: "'k \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> ('k semi_factor, 'f, 'r) frame" where
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
  assumes cK: "compact K" and K: "proj c\<cdot>K = K"
  shows "ffor \<tau> G (peg K F) = peg (proj (truncate \<tau> c)\<cdot>K) (ffor \<tau> G F)"
proof -
  let ?a = "slod (slice F)" and ?b = "slod (spin K)"
  have bK: "proj ?b\<cdot>K = K" by (rule slod_spin_lives[OF cK])
  have abK: "lives_at (?a \<squnion> ?b) K"
    using lives_at_up[of ?b K "(?a \<squnion> ?b)"] bK by (simp add: lives_at_def lattice_join_ge2)
  have "proj (truncate \<tau> (?a \<squnion> ?b))\<cdot>K = proj (truncate \<tau> c)\<cdot>K"
    by (rule truncate_proj_irrelevant[OF abK]) (simp add: lives_at_def K)
  then have c2: "coarsen (truncate \<tau> (?a \<squnion> ?b)) (spin K) = spin (proj (truncate \<tau> c)\<cdot>K)"
    by (simp add: coarsen_spin[OF cK])
  have e: "truncate \<tau> (?a \<squnion> ?b) \<sqinter> ?b = truncate \<tau> ?b"
    by (metis lattice_meet_assoc lattice_meet_commute lattice_meet_absorb1 lattice_join_ge2)
  have c3: "coarsen \<tau> (spin K) = coarsen (truncate \<tau> (?a \<squnion> ?b)) (spin K)"
    using coarsen_slod[of \<tau> "spin K"] coarsen_slod[of "truncate \<tau> (?a \<squnion> ?b)" "spin K"] e by simp
  show ?thesis
    by (simp add: ffor_def peg_def coarsen_conj c3 c2 conj.assoc conj.commute conj.left_commute)
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

definition keyimg :: "'r set \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k semi_factor \<Rightarrow> 'k \<Rightarrow> bool" where
  "keyimg S F c k \<longleftrightarrow> (\<exists>x\<in>pts S. frows F x \<and> k = proj c\<cdot>(rkey\<cdot>x))"

definition fkeys :: "'r set \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k semi_factor \<Rightarrow> 'k \<Rightarrow> bool" where
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

definition pins :: "('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k semi_factor \<Rightarrow> 'k \<Rightarrow> bool" where
  "pins F L K \<longleftrightarrow> slice F \<^bold>\<le> spin K \<and> maximal_at L K \<and> compact K"

lemma pins_compact: "pins F L K \<Longrightarrow> compact K"
  unfolding pins_def by blast

lemma pins_peg: "compact K \<Longrightarrow> maximal_at L K \<Longrightarrow> pins (peg K F) L K"
  by (simp add: pins_def)

lemma frows_pinned: "pins F L K \<Longrightarrow> frows F r \<Longrightarrow> K \<sqsubseteq> rkey\<cdot>r"
  unfolding frows_def pins_def by (blast intro: holds_pinned)

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
  have "K \<sqsubseteq> k'" using assms(1,4) unfolding pins_def by (blast intro: holds_pinned)
  show "proj c\<cdot>K \<sqsubseteq> K1" by (rule proj_below_maximal[OF assms(2) \<open>K \<sqsubseteq> k'\<close> assms(3)])
  show "K1 \<Up> K" using assms(3) \<open>K \<sqsubseteq> k'\<close> by (rule joinableI)
qed

end

section \<open>Laws for an abstract semantics\<close>

locale dataspace = frame_sem conj sunit slod sopen coarsen spin rkey
  for conj :: "'f \<Rightarrow> 'f \<Rightarrow> 'f" (infixl \<open>\<^bold>*\<close> 70) and sunit :: 'f (\<open>\<^bold>1\<close>)
    and slod :: "'f \<Rightarrow> 'k::{dI, locally_finitely_detailed} semi_factor" and sopen :: "'f \<Rightarrow> 'k sel"
    and coarsen spin and rkey :: "'r::pcpo \<rightarrow> 'k" +
  fixes S :: "'r set"
  assumes dataset_S: "dataset S"
begin

subsection \<open>Rows seen through a mask\<close>

text \<open>The data rows in an ambient filter, and among them those whose key passes the slice
  transformed by a mask.  An LOD is read on rows through their keys.\<close>

definition arows :: "'r sel \<Rightarrow> 'r set" where
  "arows \<phi> = {x \<in> pts S. selects \<phi> x}"

definition mrows :: "'k semi_factor \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'r set" where
  "mrows \<rho> F = {x \<in> arows (amb F). holds (coarsen \<rho> (slice F)) (rkey\<cdot>x)}"

abbreviation rproj :: "'k semi_factor \<Rightarrow> 'r \<Rightarrow> 'k" where
  "rproj L x \<equiv> proj L\<cdot>(rkey\<cdot>x)"

lemma mrows_cong: "amb F = amb F' \<Longrightarrow> slice F = slice F' \<Longrightarrow> mrows \<rho> F = mrows \<rho> F'"
  by (simp add: mrows_def)

lemma frows_mrows: "x \<in> pts S \<Longrightarrow> frows F x \<Longrightarrow> x \<in> mrows \<rho> F"
  by (simp add: mrows_def arows_def frows_def holds_coarsen)

text \<open>Reading at a join of LODs is reading at both.\<close>

lemma rproj_sup_fequiv: "relspace.fequiv D (\<lambda>x. (rproj a x, rproj b x)) (rproj (a \<squnion> b))"
  unfolding relspace.fequiv_def relspace.determines_rows
proof (intro conjI ballI impI)
  fix d d' assume "rproj (a \<squnion> b) d = rproj (a \<squnion> b) d'"
  then have "proj a\<cdot>(rproj (a \<squnion> b) d) = proj a\<cdot>(rproj (a \<squnion> b) d')"
    "proj b\<cdot>(rproj (a \<squnion> b) d) = proj b\<cdot>(rproj (a \<squnion> b) d')" by simp_all
  then show "(rproj a d, rproj b d) = (rproj a d', rproj b d')" by (simp add: proj_le lattice_join_ge1 lattice_join_ge2)
qed (simp add: proj_sup)

lemma rproj_sup_eq: "rproj (a \<squnion> b) y = rproj (a \<squnion> b) z \<longleftrightarrow> rproj a y = rproj a z \<and> rproj b y = rproj b z"
proof
  assume e: "rproj (a \<squnion> b) y = rproj (a \<squnion> b) z"
  show "rproj a y = rproj a z \<and> rproj b y = rproj b z"
    using arg_cong[OF e, of "Rep_cfun (proj a)"] arg_cong[OF e, of "Rep_cfun (proj b)"]
    by (simp add: proj_le lattice_join_ge1 lattice_join_ge2)
qed (simp add: proj_sup)

text \<open>Two LODs are \<^emph>\<open>equivalent at grain \<open>n\<close> through a mask \<open>\<rho>\<close>\<close> in a frame, together with a
  further row \<open>x\<close>, when their masks are equivalent modulo \<open>n\<close> on those rows (@{const
  relspace.equiv_mod}).  Being a condition on pairs of rows, it survives losing rows; it also
  survives adding the same detail to both sides.\<close>

definition dims_equiv :: "'k semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'r \<Rightarrow> 'k semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> bool" where
  "dims_equiv n \<rho> F x a t \<longleftrightarrow>
     relspace.equiv_mod (insert x (mrows \<rho> F)) (rproj n) (rproj (truncate \<rho> a)) (rproj (truncate \<rho> t))"

text \<open>The extra row may change too, when it stays among the rows compared.\<close>

lemma dims_equiv_sub_row:
  assumes "insert y (mrows \<rho>' F') \<subseteq> insert x (mrows \<rho> F)" "dims_equiv n \<rho> F x a t"
    "truncate \<rho>' a' = truncate \<rho> a" "truncate \<rho>' t' = truncate \<rho> t"
  shows "dims_equiv n \<rho>' F' y a' t'"
  using assms(2) unfolding dims_equiv_def assms(3,4)
  by (rule equiv_mod_subset[rotated]) (use assms(1) in blast)

lemma dims_equiv_sub:
  assumes "mrows \<rho>' F' \<subseteq> mrows \<rho> F" "dims_equiv n \<rho> F x a t"
    "truncate \<rho>' a' = truncate \<rho> a" "truncate \<rho>' t' = truncate \<rho> t"
  shows "dims_equiv n \<rho>' F' x a' t'"
  by (rule dims_equiv_sub_row[OF _ assms(2-4)]) (use assms(1) in blast)

lemma dims_equiv_sup_row:
  assumes "insert y (mrows \<rho>' F') \<subseteq> insert x (mrows \<rho> F)" "dims_equiv n \<rho> F x a t"
    and "truncate \<rho>' a' = (truncate \<rho> a \<squnion> c)" "truncate \<rho>' t' = (truncate \<rho> t \<squnion> c)"
  shows "dims_equiv n \<rho>' F' y a' t'"
proof -
  let ?D = "insert y (mrows \<rho>' F')"
  have "relspace.equiv_mod ?D (rproj n) (rproj (truncate \<rho> a)) (rproj (truncate \<rho> t))"
    using assms(2) unfolding dims_equiv_def
    by (rule equiv_mod_subset[rotated]) (use assms(1) in blast)
  then have "relspace.equiv_mod ?D (rproj n)
      (\<lambda>x. (rproj (truncate \<rho> a) x, rproj c x)) (\<lambda>x. (rproj (truncate \<rho> t) x, rproj c x))"
    by (rule relspace.equiv_mod_pair)
  then show ?thesis unfolding dims_equiv_def assms(3,4)
    by (rule relspace.equiv_mod_fequiv[OF rproj_sup_fequiv rproj_sup_fequiv])
qed

lemma dims_equiv_sup:
  assumes "mrows \<rho>' F' \<subseteq> mrows \<rho> F" "dims_equiv n \<rho> F x a t"
    and "truncate \<rho>' a' = (truncate \<rho> a \<squnion> c)" "truncate \<rho>' t' = (truncate \<rho> t \<squnion> c)"
  shows "dims_equiv n \<rho>' F' x a' t'"
  by (rule dims_equiv_sup_row[OF _ assms(2-4)]) (use assms(1) in blast)

text \<open>Frames with the same filters have the same masked rows, so the equivalence is symmetric.\<close>

lemma dims_equiv_sym:
  "amb F = amb F' \<Longrightarrow> slice F = slice F' \<Longrightarrow> dims_equiv n \<rho> F x a t \<Longrightarrow> dims_equiv n \<rho> F' x t a"
  unfolding dims_equiv_def by (simp add: mrows_cong[of F' F] relspace.equiv_mod_sym)

text \<open>A finer grain constrains more pairs of rows, so the equivalence survives coarsening it.\<close>

lemma dims_equiv_natd_le: "n \<sqsubseteq> n' \<Longrightarrow> dims_equiv n' \<rho> F x a t \<Longrightarrow> dims_equiv n \<rho> F x a t"
proof -
  assume le: "n \<sqsubseteq> n'" and e: "dims_equiv n' \<rho> F x a t"
  have "rproj n' d \<noteq> rproj n' d'" if "rproj n d \<noteq> rproj n d'" for d d'
    using that proj_le[OF le, of "rkey\<cdot>d"] proj_le[OF le, of "rkey\<cdot>d'"] by force
  with e show ?thesis unfolding dims_equiv_def relspace.equiv_mod_def by blast
qed

text \<open>The grains of one mask combine: the equivalence at a join of grains is the equivalence at
  both, and the bottom grain imposes nothing.  So the dims are a map from masks to grains, a
  collection joins those maps, and two pairs with the same mask collapse into one.\<close>

lemma dims_equiv_bot: "dims_equiv \<bottom> \<rho> F x a t"
  unfolding dims_equiv_def relspace.equiv_mod_def by (simp add: proj_bot)

lemma dims_equiv_sup_natd:
  "dims_equiv (n \<squnion> n') \<rho> F x a t \<longleftrightarrow> dims_equiv n \<rho> F x a t \<and> dims_equiv n' \<rho> F x a t"
proof
  assume "dims_equiv (n \<squnion> n') \<rho> F x a t"
  then show "dims_equiv n \<rho> F x a t \<and> dims_equiv n' \<rho> F x a t"
    by (blast intro: dims_equiv_natd_le[OF lattice_join_ge1] dims_equiv_natd_le[OF lattice_join_ge2])
next
  assume e: "dims_equiv n \<rho> F x a t \<and> dims_equiv n' \<rho> F x a t"
  have "rproj n d \<noteq> rproj n d' \<or> rproj n' d \<noteq> rproj n' d'"
    if "rproj (n \<squnion> n') d \<noteq> rproj (n \<squnion> n') d'" for d d'
    using that by (auto simp: proj_sup)
  with e show "dims_equiv (n \<squnion> n') \<rho> F x a t"
    unfolding dims_equiv_def relspace.equiv_mod_def by blast
qed

text \<open>The bottom mask reads nothing, so its natural LOD does not matter.\<close>

lemma dims_equiv_bot_mask: "dims_equiv n \<bottom> F x a t"
  unfolding dims_equiv_def by (simp add: relspace.equiv_mod_refl)

text \<open>An expression's dims hypothesis holds at every mask, at the natural LOD the dims give it.\<close>

definition dims_equivs :: "('k semi_factor \<Rightarrow> 'k semi_factor) \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'r \<Rightarrow> 'k semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> bool" where
  "dims_equivs \<Delta> F x a t \<longleftrightarrow> (\<forall>\<rho>. dims_equiv (\<Delta> \<rho>) \<rho> F x a t)"

lemma dims_equivsD: "dims_equivs \<Delta> F x a t \<Longrightarrow> dims_equiv (\<Delta> \<rho>) \<rho> F x a t"
  unfolding dims_equivs_def by blast

lemma dims_equivsI: "(\<And>\<rho>. dims_equiv (\<Delta> \<rho>) \<rho> F x a t) \<Longrightarrow> dims_equivs \<Delta> F x a t"
  unfolding dims_equivs_def by blast

lemma dims_equivs_bot: "dims_equivs \<bottom> F x a t"
  by (simp add: dims_equivs_def dims_equiv_bot)

lemma dims_equivs_sym:
  "amb F = amb F' \<Longrightarrow> slice F = slice F' \<Longrightarrow> dims_equivs \<Delta> F x a t \<Longrightarrow> dims_equivs \<Delta> F' x t a"
  unfolding dims_equivs_def by (blast intro: dims_equiv_sym)

end

text \<open>A fixed expression has a minimal LOD \<^term>\<open>mind\<close>, dims \<^term>\<open>dims\<close> (a map from masks to
  natural LODs) and a semantics: at each frame, a map from keys to values; a value \<open>\<bottom>\<close> is an
  undefined value, not a missing entry.  Its key LOD under a frame is what it decides itself plus
  the frame's LOD.  The \<^emph>\<open>peg law\<close> says that pegging the frame to a key does not change the
  value there.  The \<^emph>\<open>dims law\<close> says that in frames with the same filters, the entries present
  at the keys a row of the frame has at two key LODs agree, when for every mask the masked key
  LODs are equivalent at the natural grain on the masked rows of the frame and that row.  The
  \<^emph>\<open>effective-LOD law\<close> says that the semantics depends on a frame's LOD only through the key
  LOD.  The slice is compared syntactically, since coarsening is not extensional.  These laws
  make a semantics \<^emph>\<open>semilawful\<close>: it says nothing about which keys have entries, and may have
  entries at keys that are not in the data.\<close>

locale expr_laws = dataspace +
  fixes mind dims sem
  assumes peg_law: "compact K \<Longrightarrow> sem (peg K F) K = sem F K"
    and present_dims_law: "\<lbrakk>amb F = amb F'; slice F = slice F'; x \<in> pts S; frows F x;
                    dims_equivs dims F x (mind \<squnion> flod F) (mind \<squnion> flod F');
                    sem F (rproj (mind \<squnion> flod F) x) \<noteq> None;
                    sem F' (rproj (mind \<squnion> flod F') x) \<noteq> None\<rbrakk>
                   \<Longrightarrow> sem F (rproj (mind \<squnion> flod F) x) = sem F' (rproj (mind \<squnion> flod F') x)"
    and eff_law: "\<lbrakk>amb F = amb F'; slice F = slice F'; (mind \<squnion> flod F) = (mind \<squnion> flod F')\<rbrakk>
                  \<Longrightarrow> sem F = sem F'"
    and mind_compact: "compact mind"
    and dims_compact: "compact dims"
    and dims_bot: "dims \<rho> \<sqsubseteq> dims \<bottom>"

text \<open>A semantics is \<^emph>\<open>lawful\<close> when moreover the \<^emph>\<open>key law\<close> holds: entries are only at the
  keys of the frame's data points at the key LOD; so keys conform to the slice and live at the
  key LOD.  An expression may drop keys, by a filter of its own.  Keys need not be maximal: a row
  missing data (\<open>\<bottom>\<close> in a column) gives a partial key, which no slice can pin.  The dims law then
  holds as an equality: under the equivalence, at a row of the frame, the entries are both
  missing or present with the same value; what an expression drops is accounted for in its dims,
  like what it reads.  Combinators are then maps from lawful semantics to lawful semantics.\<close>

locale expr_sem = expr_laws +
  assumes key_data: "sem F k \<noteq> None \<Longrightarrow> keyimg S F (mind \<squnion> flod F) k"
    and dims_law: "\<lbrakk>amb F = amb F'; slice F = slice F'; x \<in> pts S; frows F x;
                    dims_equivs dims F x (mind \<squnion> flod F) (mind \<squnion> flod F')\<rbrakk>
                   \<Longrightarrow> sem F (rproj (mind \<squnion> flod F) x) = sem F' (rproj (mind \<squnion> flod F') x)"
begin

abbreviation "kd F \<equiv> (mind \<squnion> flod F)"

lemma key_slicer: "sem F k \<noteq> None \<Longrightarrow> \<exists>k'. k \<sqsubseteq> k' \<and> holds (slice F) k'"
  by (rule keyimg_slicer[OF key_data])

lemma key_lives: "sem F k \<noteq> None \<Longrightarrow> proj (kd F)\<cdot>k = k"
  using key_data[of F k] by (auto simp: keyimg_def)

lemma kd_compact: "compact (flod F) \<Longrightarrow> compact (kd F)"
  by (simp add: compact_semi_factor_sup mind_compact)


text \<open>The compatibility the dims law relies on is automatic: an entry's key is the projection of
  a selected row, and the pin lies below that row's key.\<close>

lemma pinned_entry:
  assumes "pins F L K" "sem F K1 \<noteq> None"
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
  assumes F: "compact (flod F)" and K: "maximal_at (kd F) K"
  shows "sem (peg K F) k = (if k = K then sem F K else None)"
proof (cases "k = K")
  case True then show ?thesis by (simp add: peg_law maximal_at_compact[OF K kd_compact[OF F]])
next
  case False
  show ?thesis
  proof (rule ccontr)
    assume "sem (peg K F) k \<noteq> (if k = K then sem F K else None)"
    with False have nb: "sem (peg K F) k \<noteq> None" by simp
    obtain x where x: "frows (peg K F) x" and kx: "k = proj (kd F)\<cdot>(rkey\<cdot>x)"
      using key_data[OF nb] by (auto simp: keyimg_def)
    have "K \<sqsubseteq> rkey\<cdot>x" using x by (simp add: frows_peg maximal_at_compact[OF K kd_compact[OF F]])
    then have "proj (kd F)\<cdot>K \<sqsubseteq> k" unfolding kx by (rule monofun_cfun_arg)
    then have Kk: "K \<sqsubseteq> k" by (simp only: maximal_at_lives[OF K])
    have lv: "proj (kd F)\<cdot>k = k" using key_lives[OF nb] by simp
    from Kk have "k = K" by (rule maximal_at_eq[OF K lv])
    with False show False ..
  qed
qed

text \<open>Through a mask, a pin still fixes the masked truncation of the key.\<close>

lemma masked_pin:
  assumes cK: "compact K" and K: "maximal_at c K" and h: "holds (coarsen \<rho> (spin K)) k"
  shows "proj (truncate \<rho> c)\<cdot>k = proj (truncate \<rho> c)\<cdot>K"
proof -
  have "proj (truncate \<rho> (slod (spin K)))\<cdot>K = proj (truncate \<rho> c)\<cdot>K"
    by (rule truncate_proj_irrelevant)
      (simp_all add: lives_at_def slod_spin_lives[OF cK] maximal_at_lives[OF K])
  moreover have "holds (coarsen (truncate \<rho> (slod (spin K))) (spin K)) k"
    using h by (simp only: coarsen_slod[of \<rho> "spin K"])
  ultimately have "proj (truncate \<rho> c)\<cdot>K \<sqsubseteq> k"
    by (simp add: coarsen_spin[OF cK] holds_spin[OF compact_proj_compact[OF cK]])
  then have "proj (truncate \<rho> c)\<cdot>K \<sqsubseteq> proj (truncate \<rho> c)\<cdot>k" by (metis monofun_cfun_arg proj_idem)
  then show ?thesis
    by (rule maximal_at_eq[OF maximal_at_proj[OF truncate_below K] proj_idem])
qed

text \<open>Values at different levels of detail: an entry of a frame pegged to a finer key sits at
  the truncation of that key and has the finer key's value.  Through the mask, the rows the
  pegged frame sees all have the pinned key's truncation, so the dims law applies.  (Presence
  at the coarser key is not claimed.)\<close>

theorem lod_shift:
  assumes "amb F1 = amb F2" "slice F1 = slice F2" "flod F1 \<sqsubseteq> flod F2"
    and F2: "compact (flod F2)"
    and K2m: "maximal_at (kd F2) K2" and nb: "sem (peg K2 F1) k \<noteq> None"
  shows "k = proj (kd F1)\<cdot>K2" "sem (peg K2 F1) k = sem F2 K2"
proof -
  have cK2: "compact K2" by (rule maximal_at_compact[OF K2m kd_compact[OF F2]])
  obtain x where xS: "x \<in> pts S" and x: "frows (peg K2 F1) x" and kx: "k = rproj (kd F1) x"
    using key_data[OF nb] by (auto simp: keyimg_def)
  have Kx: "K2 \<sqsubseteq> rkey\<cdot>x" using x by (simp add: frows_peg cK2)
  have sub: "kd F1 \<sqsubseteq> kd F2" using assms(3) by (rule lattice_join_mono[OF below_refl])
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
  have eq1: "dims_equiv n \<rho> (peg K2 F2) x (kd (peg K2 F2)) (kd (peg K2 F1))" for n \<rho>
  proof -
    have pin: "rproj (truncate \<rho> (kd F2)) y = proj (truncate \<rho> (kd F2))\<cdot>K2"
      if "y \<in> insert x (mrows \<rho> (peg K2 F2))" for y
    proof -
      from that coarsen_conj[of \<rho> "slice F2" "spin K2"]
      consider "y = x" | "holds (coarsen \<rho> (spin K2)) (rkey\<cdot>y)"
        by (auto simp: mrows_def)
      then show ?thesis
      proof cases
        case 1
        then show ?thesis using proj_le[OF truncate_below, of \<rho> "kd F2" "rkey\<cdot>x"] x2 by simp
      next
        case 2
        then show ?thesis by (rule masked_pin[OF cK2 K2m])
      qed
    qed
    show ?thesis
      unfolding dims_equiv_def relspace.equiv_mod_def
    proof (intro ballI impI)
      fix y y' assume y: "y \<in> insert x (mrows \<rho> (peg K2 F2))"
        and y': "y' \<in> insert x (mrows \<rho> (peg K2 F2))"
      have e2: "rproj (truncate \<rho> (kd F2)) y = rproj (truncate \<rho> (kd F2)) y'"
        using pin[OF y] pin[OF y'] by simp
      then have "rproj (truncate \<rho> (kd F1)) y = rproj (truncate \<rho> (kd F1)) y'"
        by (metis proj_le[OF truncate_mono[OF sub]])
      with e2 show "(rproj (truncate \<rho> (kd (peg K2 F2))) y = rproj (truncate \<rho> (kd (peg K2 F2))) y') =
                    (rproj (truncate \<rho> (kd (peg K2 F1))) y = rproj (truncate \<rho> (kd (peg K2 F1))) y')"
        by simp
    qed
  qed
  have eq: "dims_equivs dims (peg K2 F2) x (kd (peg K2 F2)) (kd (peg K2 F1))"
    by (rule dims_equivsI) (rule eq1)
  have "sem (peg K2 F2) (rproj (kd (peg K2 F2)) x) = sem (peg K2 F1) (rproj (kd (peg K2 F1)) x)"
    by (rule dims_law[OF f xS _ eq]) (use x f frows_cong[OF f] in simp)
  then show "sem (peg K2 F1) k = sem F2 K2" by (simp add: x2 peg_law[OF cK2] kx)
qed

end

text \<open>Within a dataspace, a semantics is \<^emph>\<open>lawful\<close> when it forms an \<^locale>\<open>expr_sem\<close>
  instance; combinators are then plain theorems concluding lawfulness.\<close>

context dataspace
begin

abbreviation semilawful where "semilawful \<equiv> expr_laws conj sunit slod sopen coarsen spin rkey S"

abbreviation lawful where "lawful \<equiv> expr_sem conj sunit slod sopen coarsen spin rkey S"

lemma lawful_semilawful: "lawful mind dims sem \<Longrightarrow> semilawful mind dims sem"
  by (rule expr_sem.axioms(1))

lemma lawfulI:
  assumes "\<And>F k. sem F k \<noteq> None \<Longrightarrow> keyimg S F (mind \<squnion> flod F) k"
    and "\<And>F K. compact K \<Longrightarrow> sem (peg K F) K = sem F K"
    and "\<And>F F' x. \<lbrakk>amb F = amb F'; slice F = slice F'; x \<in> pts S; frows F x;
                    dims_equivs dims F x (mind \<squnion> flod F) (mind \<squnion> flod F')\<rbrakk>
                   \<Longrightarrow> sem F (rproj (mind \<squnion> flod F) x) = sem F' (rproj (mind \<squnion> flod F') x)"
    and "\<And>F F'. \<lbrakk>amb F = amb F'; slice F = slice F'; (mind \<squnion> flod F) = (mind \<squnion> flod F')\<rbrakk>
                 \<Longrightarrow> sem F = sem F'"
    and "compact mind" and "compact dims" and "\<And>\<rho>. dims \<rho> \<sqsubseteq> dims \<bottom>"
  shows "lawful mind dims sem"
  by (intro expr_sem.intro expr_laws.intro dataspace_axioms expr_laws_axioms.intro expr_sem_axioms.intro)
    (fact assms | (rule assms(3), assumption+))+

text \<open>The dims law splits into presence, of which one direction suffices since the equivalence
  is symmetric, and agreement of present entries.\<close>

lemma dims_lawI:
  assumes pres: "\<And>F F'. \<lbrakk>amb F = amb F'; slice F = slice F'; frows F x;
                    dims_equivs dims F x (mind \<squnion> flod F) (mind \<squnion> flod F');
                    sem F (rproj (mind \<squnion> flod F) x) \<noteq> None\<rbrakk>
                   \<Longrightarrow> sem F' (rproj (mind \<squnion> flod F') x) \<noteq> None"
    and val: "\<lbrakk>sem F (rproj (mind \<squnion> flod F) x) \<noteq> None; sem F' (rproj (mind \<squnion> flod F') x) \<noteq> None\<rbrakk>
                   \<Longrightarrow> sem F (rproj (mind \<squnion> flod F) x) = sem F' (rproj (mind \<squnion> flod F') x)"
    and a: "amb F = amb F'" "slice F = slice F'" "frows F x"
      "dims_equivs dims F x (mind \<squnion> flod F) (mind \<squnion> flod F')"
  shows "sem F (rproj (mind \<squnion> flod F) x) = sem F' (rproj (mind \<squnion> flod F') x)"
proof (cases "sem F (rproj (mind \<squnion> flod F) x) = None")
  case False
  then have n: "sem F (rproj (mind \<squnion> flod F) x) \<noteq> None" by simp
  show ?thesis by (rule val[OF n pres[OF a n]])
next
  case True
  have x': "frows F' x" using a(3) frows_cong[OF a(1,2)] by simp
  have "sem F' (rproj (mind \<squnion> flod F') x) = None"
  proof (rule ccontr)
    assume "sem F' (rproj (mind \<squnion> flod F') x) \<noteq> None"
    then have "sem F (rproj (mind \<squnion> flod F) x) \<noteq> None"
      by (rule pres[OF a(1,2)[symmetric] x' dims_equivs_sym[OF a(1,2,4)]])
    with True show False by simp
  qed
  with True show ?thesis by simp
qed

abbreviation lawfulE where "lawfulE E \<equiv> lawful (emind E) (edims E) (esem E)"

subsection \<open>Conforming to data\<close>

text \<open>The \<^emph>\<open>guard\<close> keeps an entry only at keys of the data.  Simple constructions (maps,
  collections, constants) need not conform to data on their own: they agree with a lawful
  semantics at the data keys, and a single guard where they enter an aggregation, or the
  output, restores the key law.\<close>

definition guard :: "('k semi_factor, 'f, 'r, 'k, 'v) expr \<Rightarrow> ('k semi_factor, 'f, 'r, 'k, 'v) expr" where
  "guard E = E\<lparr>esem := \<lambda>F k. if keyimg S F (emind E \<squnion> flod F) k then esem E F k else None\<rparr>"

lemma guard_simps [simp]:
  "emind (guard E) = emind E" "edims (guard E) = edims E"
  "esem (guard E) F k = (if keyimg S F (emind E \<squnion> flod F) k then esem E F k else None)"
  by (simp_all add: guard_def)

lemma guard_idem [simp]: "guard (guard E) = guard E"
  by (cases E) (simp add: guard_def fun_eq_iff)

lemma guard_lawful: "lawfulE E \<Longrightarrow> guard E = E"
proof -
  assume "lawfulE E"
  then interpret E: expr_sem conj sunit slod sopen coarsen spin rkey S
    "emind E" "edims E" "esem E" .
  have v: "(if keyimg S F (emind E \<squnion> flod F) k then esem E F k else None) = esem E F k"
    for F k using E.key_data[of F k] by (cases "esem E F k") auto
  show "guard E = E" unfolding guard_def v by simp
qed

subsection \<open>Maps\<close>

text \<open>Applying a function to every entry's value.  It need not be strict: an undefined value is
  still an entry.\<close>

definition smap :: "('v::cpo \<rightarrow> 'w::cpo) \<Rightarrow> ('k semi_factor, 'f, 'r, 'k, 'v) expr \<Rightarrow> ('k semi_factor, 'f, 'r, 'k, 'w) expr"
  where "smap g E = \<lparr>emind = emind E, edims = edims E, esem = \<lambda>F k. map_option (Rep_cfun g) (esem E F k)\<rparr>"

lemma smap_simps [simp]:
  "emind (smap g E) = emind E" "edims (smap g E) = edims E"
  "esem (smap g E) F k = map_option (Rep_cfun g) (esem E F k)"
  by (simp_all add: smap_def)

theorem lawful_smap: assumes "lawfulE E" shows "lawfulE (smap g E)"
proof -
  interpret E: expr_sem conj sunit slod sopen coarsen spin rkey S
    "emind E" "edims E" "esem E"
    by (fact assms(1))
  show ?thesis
  proof (rule lawfulI, simp_all only: smap_simps)
    fix F :: "('k semi_factor, 'f, 'r) frame" and k :: 'k
    assume "map_option (Rep_cfun g) (esem E F k) \<noteq> None"
    then show "keyimg S F (emind E \<squnion> flod F) k" by (intro E.key_data) simp
  next
    fix F :: "('k semi_factor, 'f, 'r) frame" and K :: 'k assume "compact K"
    then show "map_option (Rep_cfun g) (esem E (peg K F) K) = map_option (Rep_cfun g) (esem E F K)"
      by (simp only: E.peg_law)
  next
    fix F F' :: "('k semi_factor, 'f, 'r) frame" and x :: 'r
    assume a: "amb F = amb F'" "slice F = slice F'" "x \<in> pts S" "frows F x"
      "dims_equivs (edims E) F x (emind E \<squnion> flod F) (emind E \<squnion> flod F')"
    show "map_option (Rep_cfun g) (esem E F (rproj (emind E \<squnion> flod F) x))
        = map_option (Rep_cfun g) (esem E F' (rproj (emind E \<squnion> flod F') x))"
      by (simp only: E.dims_law[OF a])
  next
    fix F F' :: "('k semi_factor, 'f, 'r) frame"
    assume "amb F = amb F'" "slice F = slice F'" "(emind E \<squnion> flod F) = (emind E \<squnion> flod F')"
    then have "esem E F = esem E F'" by (rule E.eff_law)
    then show "esem (smap g E) F = esem (smap g E) F'" by (simp add: fun_eq_iff)
  next
    show "compact (emind E)" by (rule E.mind_compact)
  next
    show "compact (edims E)" by (rule E.dims_compact)
  next
    show "edims E \<rho> \<sqsubseteq> edims E \<bottom>" for \<rho> by (rule E.dims_bot)
  qed
qed

lemma guard_smap: "guard (smap g E) = smap g (guard E)"
  by (cases E) (simp add: guard_def smap_def fun_eq_iff)

corollary lawful_guard_smap:
  assumes "lawfulE (guard E)" shows "lawfulE (guard (smap g E))"
  unfolding guard_smap by (rule lawful_smap[OF assms])
end

section \<open>Combinators\<close>

subsection \<open>\<open>INCLUDE\<close>\<close>

definition group_by where
  "group_by D sem = (\<lambda>F. sem (finclude D F))"

theorem (in expr_sem) lawful_group_by:
  assumes D: "compact D"
  shows "lawful (mind \<squnion> D) dims (group_by D sem)"
proof (rule lawfulI)
  have kd: "(mind \<squnion> D \<squnion> X) = (mind \<squnion> (X \<squnion> D))" for X by (simp only: ac_simps)
  show "keyimg S F (mind \<squnion> D \<squnion> flod F) k" if "group_by D sem F k \<noteq> None" for F k
    using key_data[of "finclude D F" k] keyimg_cong[of "finclude D F" F S] that
    by (simp add: group_by_def kd)
  show "group_by D sem (peg K F) K = group_by D sem F K" if "compact K" for F K
    by (simp add: group_by_def peg_finclude[symmetric] peg_law[OF that])
  show "group_by D sem F (rproj (mind \<squnion> D \<squnion> flod F) x)
      = group_by D sem F' (rproj (mind \<squnion> D \<squnion> flod F') x)"
    if "amb F = amb F'" "slice F = slice F'" "x \<in> pts S" "frows F x"
      "dims_equivs dims F x (mind \<squnion> D \<squnion> flod F) (mind \<squnion> D \<squnion> flod F')"
    for F F' x
  proof -
    have "dims_equivs dims (finclude D F) x (kd (finclude D F)) (kd (finclude D F'))"
      using that(5) by (simp add: dims_equivs_def dims_equiv_def mrows_def kd)
    then show ?thesis
      using dims_law[of "finclude D F" "finclude D F'" x] that(1-4)
      by (simp add: group_by_def kd)
  qed
  show "group_by D sem F = group_by D sem F'"
    if "amb F = amb F'" "slice F = slice F'" "(mind \<squnion> D \<squnion> flod F) = (mind \<squnion> D \<squnion> flod F')"
    for F F'
  proof -
    have "sem (finclude D F) = sem (finclude D F')"
      by (rule eff_law) (use that in \<open>simp_all add: kd\<close>)
    then show ?thesis by (simp add: group_by_def)
  qed
  show "compact (mind \<squnion> D)" by (simp add: compact_semi_factor_sup mind_compact D)
  show "compact dims" by (rule dims_compact)
  show "dims \<rho> \<sqsubseteq> dims \<bottom>" for \<rho> by (rule dims_bot)
qed

text \<open>Under a truncation to \<open>\<tau>\<close> (\<open>FOR\<close>, or a fixed LOD) the dims move along the masks' meet
  with \<open>\<tau>\<close>; the natural LODs of masks that meet \<open>\<tau>\<close> in the same mask join.  The bottom mask keeps carrying the natural grain.\<close>

definition for_dims ::
    "'k::{bifinite, distributive_cpo} semi_factor \<Rightarrow> ('k semi_factor \<Rightarrow> 'k semi_factor) \<Rightarrow> 'k semi_factor \<Rightarrow> 'k semi_factor"
  where "for_dims \<tau> \<Delta> \<rho>' = lub {\<Delta> \<rho> |\<rho>. (\<rho> \<sqinter> \<tau>) = \<rho>'}"

lemma for_dims_upper: "\<Delta> \<rho> \<sqsubseteq> for_dims \<tau> \<Delta> (\<rho> \<sqinter> \<tau>)"
  by (auto simp: for_dims_def intro: lattice_lub_upper)

lemma for_dims_bot:
  assumes "\<And>\<rho>. \<Delta> \<rho> \<sqsubseteq> \<Delta> \<bottom>"
  shows "for_dims \<tau> \<Delta> \<rho>' \<sqsubseteq> for_dims \<tau> \<Delta> \<bottom>"
proof -
  have "for_dims \<tau> \<Delta> \<rho>' \<sqsubseteq> \<Delta> \<bottom>" unfolding for_dims_def by (rule lattice_lub_least) (auto simp: is_ub_def intro: assms)
  also have "\<Delta> \<bottom> \<sqsubseteq> for_dims \<tau> \<Delta> \<bottom>" using for_dims_upper[of \<Delta> \<bottom> \<tau>] by simp
  finally show ?thesis .
qed

lemma compact_for_dims:
  fixes \<Delta> :: "'k::{bifinite, distributive_cpo} semi_factor \<Rightarrow> 'k semi_factor"
  assumes "compact \<Delta>"
  shows "compact (for_dims \<tau> \<Delta>)"
proof -
  have fin: "finite {\<rho>. \<Delta> \<rho> \<noteq> \<bottom>}" and comp: "\<And>\<rho>. compact (\<Delta> \<rho>)"
    using assms by (simp_all add: compact_fun_iff)
  have "range \<Delta> \<subseteq> insert \<bottom> (\<Delta> ` {\<rho>. \<Delta> \<rho> \<noteq> \<bottom>})" by auto
  then have rng: "finite (range \<Delta>)" using fin by (rule finite_subset[OF _ finite_insert[THEN iffD2, OF finite_imageI]])
  have val: "compact (for_dims \<tau> \<Delta> \<rho>')" for \<rho>'
  proof -
    let ?S = "{\<Delta> \<rho> |\<rho>. (\<rho> \<sqinter> \<tau>) = \<rho>'}"
    have "?S \<subseteq> range \<Delta>" by auto
    then have "finite ?S" using rng by (rule finite_subset)
    then have "compact (lub ?S)" by (rule compact_finite_lub[OF _ _ lattice_is_lub]) (auto simp: comp)
    then show ?thesis by (simp add: for_dims_def)
  qed
  have "for_dims \<tau> \<Delta> \<rho>' = \<bottom>" if "\<rho>' \<notin> (\<lambda>\<rho>. (\<rho> \<sqinter> \<tau>)) ` {\<rho>. \<Delta> \<rho> \<noteq> \<bottom>}" for \<rho>'
  proof -
    have "\<forall>\<rho>. (\<rho> \<sqinter> \<tau>) = \<rho>' \<longrightarrow> \<Delta> \<rho> = \<bottom>" using that by blast
    then show ?thesis by (auto simp: for_dims_def lattice_lub_bot_conv)
  qed
  then have "{\<rho>'. for_dims \<tau> \<Delta> \<rho>' \<noteq> \<bottom>} \<subseteq> (\<lambda>\<rho>. (\<rho> \<sqinter> \<tau>)) ` {\<rho>. \<Delta> \<rho> \<noteq> \<bottom>}" by blast
  then have "finite {\<rho>'. for_dims \<tau> \<Delta> \<rho>' \<noteq> \<bottom>}" using fin by (rule finite_subset[OF _ finite_imageI])
  with val show ?thesis by (simp add: compact_fun_iff)
qed

subsection \<open>Fixed-level constructs: \<open>GROUP BY ONLY\<close>, \<open>TOTAL\<close>, \<open>ISOLATE\<close>\<close>

text \<open>A construct that evaluates its argument under a transformed frame at a fixed LOD
  \<^term>\<open>E\<close>, broadcast back to the incoming frame's keys: it reads only the \<open>E\<close>-part of a key.  It
  is lawful whenever the transformer sees the incoming frame only through its filters and pegging
  the incoming frame does not change the inner value at the truncated key.  The inner expression
  may drop truncated keys, also by rows the incoming slice would not select, after a coarsening.
  Its dims are what the inner expression reads, moved along the truncation to \<open>E\<close>
  (@{const for_dims}); all their masks lie below \<open>E\<close>, so they see no change of the incoming LOD,
  only the incoming selection coarsened, and the dims law holds whatever they are.\<close>

context dataspace
begin

definition fixed where
  "fixed E T sem F k = (if keyimg S F (E \<squnion> flod F) k then sem (T F) (proj E\<cdot>k) else None)"

theorem lawful_fixed:
  assumes "\<And>F K. compact K \<Longrightarrow> sem (T (peg K F)) (proj E\<cdot>K) = sem (T F) (proj E\<cdot>K)"
    and "\<And>F F'. amb F = amb F' \<Longrightarrow> slice F = slice F' \<Longrightarrow> T F = T F'"
    and "compact E" and "compact \<Delta>" and "\<And>\<rho>. \<Delta> \<rho> \<sqsubseteq> \<Delta> \<bottom>"
  shows "lawful E \<Delta> (fixed E T sem)"
proof (rule lawfulI)
  show "keyimg S F (E \<squnion> flod F) k" if "fixed E T sem F k \<noteq> None" for F k
    using that by (simp add: fixed_def split: if_splits)
  show "fixed E T sem (peg K F) K = fixed E T sem F K" if "compact K" for F K
    by (simp add: fixed_def keyimg_peg_iff[OF that] assms(1)[OF that])
  show "fixed E T sem F (rproj (E \<squnion> flod F) x) = fixed E T sem F' (rproj (E \<squnion> flod F') x)"
    if "amb F = amb F'" "slice F = slice F'" "x \<in> pts S" "frows F x"
      "dims_equivs \<Delta> F x (E \<squnion> flod F) (E \<squnion> flod F')" for F F' x
  proof -
    have "proj E\<cdot>(rproj (E \<squnion> flod G) x) = rproj E x" for G :: "('k semi_factor, 'f, 'r) frame"
      by (simp add: proj_le lattice_join_ge1)
    moreover have "keyimg S G (E \<squnion> flod G) (rproj (E \<squnion> flod G) x)" if "frows G x" for G
      using that \<open>x \<in> pts S\<close> by (auto simp: keyimg_def)
    moreover have "frows F' x" using that(4) frows_cong[OF that(1,2)] by simp
    moreover have "T F' = T F" using assms(2)[OF that(1,2)] by simp
    ultimately show ?thesis using that(4) by (simp add: fixed_def)
  qed
  show "fixed E T sem F = fixed E T sem F'"
    if "amb F = amb F'" "slice F = slice F'" "(E \<squnion> flod F) = (E \<squnion> flod F')"
    for F F'
  proof -
    have "keyimg S F (E \<squnion> flod F) = keyimg S F' (E \<squnion> flod F')"
      using keyimg_cong[OF frows_cong[OF that(1,2)]] that(3) by simp
    then show ?thesis using assms(2)[OF that(1,2)] by (simp add: fixed_def fun_eq_iff)
  qed
  show "compact E" by (fact assms(3))
  show "compact \<Delta>" by (fact assms(4))
  show "\<Delta> \<rho> \<sqsubseteq> \<Delta> \<bottom>" for \<rho> by (fact assms(5))
qed

end

context expr_sem
begin

definition group_by_only where
  "group_by_only D = fixed (mind \<squnion> D) (fgroupby D) sem"

abbreviation total where
  "total \<equiv> group_by_only \<bottom>"

theorem lawful_group_by_only:
  assumes D: "compact D"
  shows "lawful (mind \<squnion> D) (for_dims (mind \<squnion> D) dims) (group_by_only D)"
  unfolding group_by_only_def
proof (rule lawful_fixed)
  show "sem (fgroupby D (peg K F)) (proj (mind \<squnion> D)\<cdot>K) = sem (fgroupby D F) (proj (mind \<squnion> D)\<cdot>K)"
    if "compact K" for F K
    by (simp add: fgroupby_peg[OF that]
        peg_below[OF compact_proj_compact[OF that] compact_proj_compact[OF that] proj_mono[OF lattice_join_ge2]])
  show "fgroupby D F = fgroupby D F'" if "amb F = amb F'" "slice F = slice F'" for F F'
    using that by (cases F, cases F') (simp add: fgroupby_def)
  show "compact (mind \<squnion> D)" by (simp add: compact_semi_factor_sup mind_compact D)
  show "compact (for_dims (mind \<squnion> D) dims)" by (rule compact_for_dims[OF dims_compact])
  show "for_dims (mind \<squnion> D) dims \<rho> \<sqsubseteq> for_dims (mind \<squnion> D) dims \<bottom>" for \<rho>
    by (rule for_dims_bot) (rule dims_bot)
qed

text \<open>\<open>ISOLATE\<close> replaces the incoming frame by the whole dataset, so it reads nothing of the
  incoming selection: it has no dims.\<close>

definition isolate where
  "isolate = fixed mind fisolate sem"

theorem lawful_isolate: "lawful mind \<bottom> isolate"
  unfolding isolate_def by (rule lawful_fixed) (simp_all add: fisolate_peg fisolate_def mind_compact compact_fun_iff)

end

subsection \<open>\<open>FOR\<close> and \<open>EXCLUDE\<close>\<close>

text \<open>\<open>E FOR \<tau> G\<close> is evaluated at the incoming frame's keys, truncated to the key LOD of the inner
  frame.  The key LOD of the inner frame is the expression's own detail plus the truncated key
  LOD of the outer one.\<close>

text \<open>An expression that reads, or drops rows by, a grain \<open>m\<close> of the whole key: \<open>m\<close> joins
  the natural LOD of the full mask, and of the bottom mask, which carries an upper bound.\<close>

definition top_dims ::
    "'k::{bifinite, distributive_cpo} semi_factor \<Rightarrow> ('k semi_factor \<Rightarrow> 'k semi_factor) \<Rightarrow> 'k semi_factor \<Rightarrow> 'k semi_factor"
  where "top_dims m \<Delta> \<rho> = (\<Delta> \<rho> \<squnion> (if \<rho> = lattice_top \<or> \<rho> = \<bottom> then m else \<bottom>))"

lemma top_dims_ge: "\<Delta> \<rho> \<sqsubseteq> top_dims m \<Delta> \<rho>"
  by (simp add: top_dims_def lattice_join_ge1)

lemma top_dims_top: "m \<sqsubseteq> top_dims m \<Delta> lattice_top"
  by (simp add: top_dims_def lattice_join_ge2)

lemma top_dims_bot_natd: "top_dims \<bottom> \<Delta> = \<Delta>"
  by (simp add: top_dims_def fun_eq_iff lattice_join_bot_right)

lemma compact_top_dims:
  fixes \<Delta> :: "'k::{bifinite, distributive_cpo} semi_factor \<Rightarrow> 'k semi_factor"
  assumes m: "compact m" and \<Delta>: "compact \<Delta>"
  shows "compact (top_dims m \<Delta>)"
proof -
  have "{\<rho>. top_dims m \<Delta> \<rho> \<noteq> \<bottom>} \<subseteq> {\<rho>. \<Delta> \<rho> \<noteq> \<bottom>} \<union> {lattice_top, \<bottom>}"
    by (auto simp: top_dims_def lattice_join_bot_right split: if_splits)
  moreover have "finite ({\<rho>. \<Delta> \<rho> \<noteq> \<bottom>} \<union> {lattice_top, \<bottom>})" using \<Delta> by (simp add: compact_fun_iff)
  ultimately have "finite {\<rho>. top_dims m \<Delta> \<rho> \<noteq> \<bottom>}" by (rule finite_subset)
  moreover have "compact (top_dims m \<Delta> \<rho>)" for \<rho>
    using \<Delta> m by (simp add: top_dims_def compact_fun_iff compact_semi_factor_sup)
  ultimately show ?thesis by (simp add: compact_fun_iff)
qed

lemma top_dims_bot:
  assumes "\<And>\<rho>. \<Delta> \<rho> \<sqsubseteq> \<Delta> \<bottom>"
  shows "top_dims m \<Delta> \<rho> \<sqsubseteq> top_dims m \<Delta> \<bottom>"
  unfolding top_dims_def by (rule lattice_join_mono[OF assms]) simp

context expr_sem
begin

definition filtfor where
  "filtfor \<tau> G F k =
     (if keyimg S F (kd F) k then sem (ffor \<tau> G F) (proj (kd (ffor \<tau> G F))\<cdot>k) else None)"

abbreviation exclude where
  "exclude \<tau> \<equiv> filtfor \<tau> \<^bold>1"

lemma flod_ffor [simp]: "flod (ffor \<tau> G F) = truncate \<tau> (flod F)"
  by (simp add: ffor_def)

lemma amb_ffor [simp]: "amb (ffor \<tau> G F) = amb F"
  by (simp add: ffor_def)

lemma kd_ffor: "(mind \<squnion> truncate \<tau> (flod F)) = (mind \<squnion> truncate \<tau> (kd F))"
  using truncate_below[of \<tau> mind]
  by (simp add: truncate_sup lattice_join_absorb1 lattice_join_assoc[symmetric])

lemma kd_ffor_le: "kd (ffor \<tau> G F) \<sqsubseteq> kd F"
  by (simp only: flod_ffor) (intro lattice_join_mono below_refl truncate_below)

lemma kd_ffor_trunc: "truncate \<tau> (kd F) \<sqsubseteq> kd (ffor \<tau> G F)"
  by (simp only: flod_ffor kd_ffor) (rule lattice_join_ge2)

text \<open>Through any mask, the inner frame's masked rows are among the outer frame's rows masked by
  the composite, and its masked key LOD is the composite's, plus the masked detail of the
  expression itself.  \<open>FOR\<close> meets every mask of the dims with \<open>\<tau>\<close>.\<close>

lemma mrows_ffor: "mrows \<rho> (ffor \<tau> G F) \<subseteq> mrows (\<rho> \<sqinter> \<tau>) F"
  using coarsen_conj[of \<rho> "coarsen \<tau> (slice F)" G] coarsen_coarsen[of \<rho> \<tau> "slice F"]
  by (auto simp: mrows_def ffor_def)

lemma mask_kd_ffor:
  "truncate \<rho> (kd (ffor \<tau> G F)) = (truncate (\<rho> \<sqinter> \<tau>) (kd F) \<squnion> truncate \<rho> mind)"
proof -
  have le: "truncate \<rho> (truncate \<tau> mind) \<sqsubseteq> truncate \<rho> mind"
    by (rule truncate_mono[OF truncate_below])
  have "truncate \<rho> (kd (ffor \<tau> G F)) = (truncate \<rho> mind \<squnion> (truncate \<rho> (truncate \<tau> (flod F))))"
    by (simp add: truncate_sup)
  also have "\<dots> = truncate \<rho> mind \<squnion>
      (truncate \<rho> (truncate \<tau> mind) \<squnion> truncate \<rho> (truncate \<tau> (flod F)))"
    by (simp only: lattice_join_assoc[symmetric] lattice_join_absorb1[OF le])
  also have "\<dots> = (truncate (\<rho> \<sqinter> \<tau>) (kd F) \<squnion> truncate \<rho> mind)"
    by (simp add: truncate_inf_comp truncate_sup lattice_join_commute)
  finally show ?thesis .
qed

text \<open>The filter \<open>G\<close> may drop a data key: its truncation may have no rows passing \<open>G\<close>.  Which
  keys it drops depends on how the truncated grouping meets \<open>G\<close>, so the grain of \<open>G\<close> joins the
  natural LOD of the full mask, before the dims move along \<open>\<tau>\<close>: a row failing \<open>G\<close> whose key has
  an inner entry shares its truncated key with a row passing \<open>G\<close>, which differs from it at that
  grain, so the equivalence keeps the two together.\<close>

theorem lawful_filtfor: "lawful mind (for_dims \<tau> (top_dims (slod G) dims)) (filtfor \<tau> G)"
proof -
  let ?D = "for_dims \<tau> (top_dims (slod G) dims)"
  have dle: "dims \<rho> \<sqsubseteq> ?D (\<rho> \<sqinter> \<tau>)" for \<rho>
    by (rule below_trans[OF top_dims_ge[of dims \<rho> "slod G"] for_dims_upper[of "top_dims (slod G) dims" \<rho> \<tau>]])
  have Gle: "slod G \<sqsubseteq> ?D \<tau>"
    using below_trans[OF top_dims_top[of "slod G" dims] for_dims_upper[of "top_dims (slod G) dims" lattice_top \<tau>]]
    by (simp only: lattice_meet_top_left)
  text \<open>The inner dims hypothesis, at the row and at the rows of the inner frame.\<close>
  have inner: "dims_equivs dims (ffor \<tau> G F) z (kd (ffor \<tau> G F)) (kd (ffor \<tau> G F'))"
    if e: "dims_equivs ?D F x (kd F) (kd F')" and z: "z = x \<or> (z \<in> pts S \<and> frows (ffor \<tau> G F) z)"
    for F F' x z
  proof (rule dims_equivsI)
    fix \<rho>
    have sub: "insert z (mrows \<rho> (ffor \<tau> G F)) \<subseteq> insert x (mrows (\<rho> \<sqinter> \<tau>) F)"
      using mrows_ffor[of \<rho> \<tau> G F] frows_mrows[of z "ffor \<tau> G F" \<rho>] z by blast
    have "dims_equiv (?D (\<rho> \<sqinter> \<tau>)) (\<rho> \<sqinter> \<tau>) F x (kd F) (kd F')" by (rule dims_equivsD[OF e])
    then have "dims_equiv (dims \<rho>) (\<rho> \<sqinter> \<tau>) F x (kd F) (kd F')" by (rule dims_equiv_natd_le[OF dle])
    then show "dims_equiv (dims \<rho>) \<rho> (ffor \<tau> G F) z (kd (ffor \<tau> G F)) (kd (ffor \<tau> G F'))"
      by (rule dims_equiv_sup_row[OF sub _ mask_kd_ffor mask_kd_ffor])
  qed
  text \<open>A row passing \<open>G\<close> with the truncated key of a row failing it keeps that key.\<close>
  have trans: "rproj (kd (ffor \<tau> G F')) y = rproj (kd (ffor \<tau> G F')) x"
    if e: "dims_equivs ?D F x (kd F) (kd F')" and x: "frows F x" "\<not> frows (ffor \<tau> G F) x"
      and y: "y \<in> pts S" "frows (ffor \<tau> G F) y"
      and k: "rproj (kd (ffor \<tau> G F)) y = rproj (kd (ffor \<tau> G F)) x" for F F' x y
  proof -
    have Gy: "holds G (rkey\<cdot>y)" using y(2) by (simp add: frows_def ffor_def)
    have Gx: "\<not> holds G (rkey\<cdot>x)" using x by (simp add: frows_def ffor_def holds_coarsen)
    have n: "rproj (slod G) y \<noteq> rproj (slod G) x"
      using Gy Gx holds_lod[of G "rkey\<cdot>y"] holds_lod[of G "rkey\<cdot>x"] by auto
    have "rproj (mind \<squnion> truncate \<tau> (kd F)) y = rproj (mind \<squnion> truncate \<tau> (kd F)) x"
      using k by (simp only: flod_ffor kd_ffor)
    then have em: "rproj mind y = rproj mind x"
      and et: "rproj (truncate \<tau> (kd F)) y = rproj (truncate \<tau> (kd F)) x"
      by (simp_all only: rproj_sup_eq)
    have "dims_equiv (?D \<tau>) \<tau> F x (kd F) (kd F')" by (rule dims_equivsD[OF e])
    then have "dims_equiv (slod G) \<tau> F x (kd F) (kd F')" by (rule dims_equiv_natd_le[OF Gle])
    then have eqm: "relspace.equiv_mod (insert x (mrows \<tau> F)) (rproj (slod G))
        (rproj (truncate \<tau> (kd F))) (rproj (truncate \<tau> (kd F')))"
      by (simp only: dims_equiv_def)
    have "y \<in> mrows (lattice_top \<sqinter> \<tau>) F"
      using mrows_ffor[of lattice_top \<tau> G F] frows_mrows[OF y, of lattice_top] by blast
    then have yM: "y \<in> mrows \<tau> F" by (simp only: lattice_meet_top_left)
    have "rproj (truncate \<tau> (kd F')) y = rproj (truncate \<tau> (kd F')) x"
      using eqm yM n et unfolding relspace.equiv_mod_def by blast
    with em show ?thesis by (simp only: flod_ffor kd_ffor rproj_sup_eq)
  qed
  text \<open>At a row failing \<open>G\<close> with an inner entry, the entries are read at a row passing it.\<close>
  have wit: "sem (ffor \<tau> G F) (rproj (kd (ffor \<tau> G F)) x) = sem (ffor \<tau> G F') (rproj (kd (ffor \<tau> G F')) x)"
    if a: "amb F = amb F'" "slice F = slice F'" "frows F x" "\<not> frows (ffor \<tau> G F) x"
      "dims_equivs ?D F x (kd F) (kd F')"
      and nb: "sem (ffor \<tau> G F) (rproj (kd (ffor \<tau> G F)) x) \<noteq> None" for F F' x
  proof -
    obtain y where y: "y \<in> pts S" "frows (ffor \<tau> G F) y"
      and ky: "rproj (kd (ffor \<tau> G F)) x = rproj (kd (ffor \<tau> G F)) y"
      using key_data[OF nb] by (auto simp: keyimg_def)
    have ky': "rproj (kd (ffor \<tau> G F')) y = rproj (kd (ffor \<tau> G F')) x"
      by (rule trans[OF a(5,3,4) y ky[symmetric]])
    have fH: "amb (ffor \<tau> G F) = amb (ffor \<tau> G F')" "slice (ffor \<tau> G F) = slice (ffor \<tau> G F')"
      by (simp_all add: ffor_def a(1,2))
    have "sem (ffor \<tau> G F) (rproj (kd (ffor \<tau> G F)) y) = sem (ffor \<tau> G F') (rproj (kd (ffor \<tau> G F')) y)"
      by (rule dims_law[OF fH y inner[OF a(5)]]) (use y in blast)
    then show ?thesis using ky ky' by simp
  qed
  have v: "filtfor \<tau> G F0 (rproj (kd F0) x) = sem (ffor \<tau> G F0) (rproj (kd (ffor \<tau> G F0)) x)"
    if "x \<in> pts S" "frows F0 x" for F0 x
  proof -
    have "keyimg S F0 (kd F0) (rproj (kd F0) x)" using that by (auto simp: keyimg_def)
    then show ?thesis using proj_le[OF kd_ffor_le[of \<tau> G F0]] by (simp add: filtfor_def)
  qed
  show ?thesis
  proof (rule lawfulI)
    show "keyimg S F (kd F) k" if "filtfor \<tau> G F k \<noteq> None" for F k
      using that by (simp add: filtfor_def split: if_splits)
    show "filtfor \<tau> G (peg K F) K = filtfor \<tau> G F K" if cK: "compact K" for F K
    proof (cases "keyimg S F (kd F) K")
      case False
      then show ?thesis by (simp add: filtfor_def keyimg_peg_iff[OF cK])
    next
      case True
      let ?H = "ffor \<tau> G F" and ?K' = "proj (truncate \<tau> (kd F))\<cdot>K"
      have Kl: "proj (kd F)\<cdot>K = K" using True by (auto simp: keyimg_def)
      have "?K' \<sqsubseteq> proj (kd ?H)\<cdot>K" by (rule proj_mono[OF kd_ffor_trunc])
      then have "sem (peg ?K' ?H) (proj (kd ?H)\<cdot>K) = sem ?H (proj (kd ?H)\<cdot>K)"
        by (rule peg_below[OF compact_proj_compact[OF cK] compact_proj_compact[OF cK]])
      then show ?thesis
        using True by (simp add: filtfor_def keyimg_peg_iff[OF cK] ffor_peg[OF cK Kl])
    qed
    show "filtfor \<tau> G F (rproj (kd F) x) = filtfor \<tau> G F' (rproj (kd F') x)"
      if a: "amb F = amb F'" "slice F = slice F'" "x \<in> pts S" "frows F x"
        "dims_equivs ?D F x (kd F) (kd F')" for F F' x
    proof -
      let ?H = "ffor \<tau> G F" and ?H' = "ffor \<tau> G F'"
      have fH: "amb ?H = amb ?H'" "slice ?H = slice ?H'" by (simp_all add: ffor_def a(1,2))
      have x': "frows F' x" using a(4) frows_cong[OF a(1,2)] by simp
      have "sem ?H (rproj (kd ?H) x) = sem ?H' (rproj (kd ?H') x)"
      proof (cases "frows ?H x")
        case True
        then show ?thesis by (rule dims_law[OF fH a(3) _ inner[OF a(5) disjI1[OF refl]]])
      next
        case False
        have nH': "\<not> frows ?H' x" using False frows_cong[OF fH] by simp
        show ?thesis
        proof (cases "sem ?H (rproj (kd ?H) x) = None")
          case False
          then show ?thesis using wit[OF a(1,2,4) \<open>\<not> frows ?H x\<close> a(5)] by simp
        next
          case True
          have "sem ?H' (rproj (kd ?H') x) = None"
          proof (rule ccontr)
            assume n: "sem ?H' (rproj (kd ?H') x) \<noteq> None"
            have "sem ?H' (rproj (kd ?H') x) = sem ?H (rproj (kd ?H) x)"
              by (rule wit[OF a(1,2)[symmetric] x' nH' dims_equivs_sym[OF a(1,2,5)] n])
            with n True show False by simp
          qed
          with True show ?thesis by simp
        qed
      qed
      then show ?thesis using v[OF a(3,4)] v[OF a(3) x'] by simp
    qed
    show "filtfor \<tau> G F = filtfor \<tau> G F'"
      if "amb F = amb F'" "slice F = slice F'" "kd F = kd F'" for F F'
    proof -
      have k: "keyimg S F (kd F) = keyimg S F' (kd F')"
        using keyimg_cong[OF frows_cong[OF that(1,2)]] that(3) by simp
      have kH: "kd (ffor \<tau> G F) = kd (ffor \<tau> G F')" by (simp only: flod_ffor kd_ffor that(3))
      have "sem (ffor \<tau> G F) = sem (ffor \<tau> G F')"
        by (rule eff_law) (use that kH in \<open>simp_all add: ffor_def\<close>)
      then show ?thesis using k kH by (simp add: filtfor_def fun_eq_iff)
    qed
    show "compact mind" by (rule mind_compact)
    show "compact ?D" by (rule compact_for_dims[OF compact_top_dims[OF slod_compact dims_compact]])
    show "?D \<rho> \<sqsubseteq> ?D \<bottom>" for \<rho> by (rule for_dims_bot) (rule top_dims_bot, rule dims_bot)
  qed
qed

text \<open>Without a filter, nothing is dropped and the dims just move along \<open>\<tau>\<close>.\<close>

corollary lawful_exclude: "lawful mind (for_dims \<tau> dims) (exclude \<tau>)"
  using lawful_filtfor[of \<tau> "\<^bold>1"] by (simp only: slod_unit top_dims_bot_natd)

end

subsection \<open>\<open>RESTRICT\<close>\<close>

definition restrict where
  "restrict \<phi> sem = (\<lambda>F. sem (frestrict \<phi> F))"

text \<open>Restricting drops the keys none of whose rows pass the filter.  When the filter is read at
  a grain \<open>n\<close> of the key \<open>-\<close> rows it separates differ at \<open>n\<close>, or share their whole key \<open>-\<close> \<open>n\<close>
  joins the natural LOD of the full mask: a row failing the filter whose key has an entry shares
  that key with a row passing it, and the equivalence keeps the two together.\<close>

theorem (in expr_sem) lawful_restrict:
  assumes n: "compact n"
    and \<phi>: "\<And>x y. x \<in> pts S \<Longrightarrow> y \<in> pts S \<Longrightarrow> selects \<phi> y \<Longrightarrow> \<not> selects \<phi> x
              \<Longrightarrow> rproj n y \<noteq> rproj n x \<or> rkey\<cdot>y = rkey\<cdot>x"
  shows "lawful mind (top_dims n dims) (restrict \<phi> sem)"
proof -
  let ?D = "top_dims n dims"
  text \<open>Restricting loses rows, which the equivalence survives.\<close>
  have inner: "dims_equivs dims (frestrict \<phi> F) z (kd (frestrict \<phi> F)) (kd (frestrict \<phi> F'))"
    if e: "dims_equivs ?D F x (kd F) (kd F')" and z: "z = x \<or> (z \<in> pts S \<and> frows F z)" for F F' x z
  proof (rule dims_equivsI)
    fix \<rho>
    have sub: "insert z (mrows \<rho> (frestrict \<phi> F)) \<subseteq> insert x (mrows \<rho> F)"
      using frows_mrows[of z F \<rho>] z by (auto simp: mrows_def arows_def)
    have "dims_equiv (dims \<rho>) \<rho> F x (kd F) (kd F')"
      by (rule dims_equiv_natd_le[OF top_dims_ge dims_equivsD[OF e]])
    then show "dims_equiv (dims \<rho>) \<rho> (frestrict \<phi> F) z (kd (frestrict \<phi> F)) (kd (frestrict \<phi> F'))"
      by (rule dims_equiv_sub_row[OF sub]) simp_all
  qed
  text \<open>A row passing the filter with the key of a row failing it keeps that key.\<close>
  have trans: "rproj (kd F') y = rproj (kd F') x"
    if e: "dims_equivs ?D F x (kd F) (kd F')" and x: "x \<in> pts S" "\<not> selects \<phi> x"
      and y: "y \<in> pts S" "frows (frestrict \<phi> F) y" and k: "rproj (kd F) y = rproj (kd F) x" for F F' x y
  proof -
    have yF: "frows F y" and sy: "selects \<phi> y" using y(2) by (simp_all add: frows_frestrict)
    from \<phi>[OF x(1) y(1) sy x(2)] show ?thesis
    proof
      assume nn: "rproj n y \<noteq> rproj n x"
      have "dims_equiv n lattice_top F x (kd F) (kd F')"
        by (rule dims_equiv_natd_le[OF top_dims_top dims_equivsD[OF e]])
      then have eqm: "relspace.equiv_mod (insert x (mrows lattice_top F)) (rproj n) (rproj (kd F)) (rproj (kd F'))"
        by (simp only: dims_equiv_def truncate_top)
      have "y \<in> mrows lattice_top F" by (rule frows_mrows[OF y(1) yF])
      then show ?thesis using eqm nn k unfolding relspace.equiv_mod_def by blast
    qed simp
  qed
  text \<open>At a row failing the filter with an entry, the entries are read at a row passing it.\<close>
  have wit: "sem (frestrict \<phi> F) (rproj (kd F) x) = sem (frestrict \<phi> F') (rproj (kd F') x)"
    if a: "amb F = amb F'" "slice F = slice F'" "x \<in> pts S" "\<not> selects \<phi> x"
      "dims_equivs ?D F x (kd F) (kd F')"
      and nb: "sem (frestrict \<phi> F) (rproj (kd F) x) \<noteq> None" for F F' x
  proof -
    have "keyimg S (frestrict \<phi> F) (kd F) (rproj (kd F) x)"
      using key_data[OF nb] by (simp only: flod_frestrict)
    then obtain y where y: "y \<in> pts S" "frows (frestrict \<phi> F) y"
      and ky: "rproj (kd F) x = rproj (kd F) y" by (auto simp: keyimg_def)
    have ky': "rproj (kd F') y = rproj (kd F') x" by (rule trans[OF a(5,3,4) y ky[symmetric]])
    have fr: "amb (frestrict \<phi> F) = amb (frestrict \<phi> F')" "slice (frestrict \<phi> F) = slice (frestrict \<phi> F')"
      by (simp_all add: a(1,2))
    have "sem (frestrict \<phi> F) (rproj (kd (frestrict \<phi> F)) y)
        = sem (frestrict \<phi> F') (rproj (kd (frestrict \<phi> F')) y)"
      by (rule dims_law[OF fr y inner[OF a(5)]]) (use y frows_frestrict in blast)
    then show ?thesis using ky ky' by simp
  qed
  show ?thesis
  proof (rule lawfulI)
    show "keyimg S F (kd F) k" if "restrict \<phi> sem F k \<noteq> None" for F k
      using key_data[of "frestrict \<phi> F" k] keyimg_mono[of "frestrict \<phi> F" F S "kd F" k] that
      by (simp add: restrict_def frows_frestrict)
    show "restrict \<phi> sem (peg K F) K = restrict \<phi> sem F K" if "compact K" for F K
      by (simp add: restrict_def peg_frestrict[symmetric] peg_law[OF that])
    show "restrict \<phi> sem F (rproj (kd F) x) = restrict \<phi> sem F' (rproj (kd F') x)"
      if a: "amb F = amb F'" "slice F = slice F'" "x \<in> pts S" "frows F x"
        "dims_equivs ?D F x (kd F) (kd F')" for F F' x
    proof (cases "selects \<phi> x")
      case True
      have fr: "amb (frestrict \<phi> F) = amb (frestrict \<phi> F')" "slice (frestrict \<phi> F) = slice (frestrict \<phi> F')"
        by (simp_all add: a(1,2))
      have "frows (frestrict \<phi> F) x" using a(4) True by (simp add: frows_frestrict)
      from dims_law[OF fr a(3) this inner[OF a(5) disjI1[OF refl]]] show ?thesis by (simp add: restrict_def)
    next
      case False
      show ?thesis
      proof (cases "sem (frestrict \<phi> F) (rproj (kd F) x) = None")
        case False
        then show ?thesis using wit[OF a(1-3) \<open>\<not> selects \<phi> x\<close> a(5)] by (simp add: restrict_def)
      next
        case True
        have "sem (frestrict \<phi> F') (rproj (kd F') x) = None"
        proof (rule ccontr)
          assume nb: "sem (frestrict \<phi> F') (rproj (kd F') x) \<noteq> None"
          have "sem (frestrict \<phi> F') (rproj (kd F') x) = sem (frestrict \<phi> F) (rproj (kd F) x)"
            by (rule wit[OF a(1,2)[symmetric] a(3) \<open>\<not> selects \<phi> x\<close> dims_equivs_sym[OF a(1,2,5)] nb])
          with nb True show False by simp
        qed
        with True show ?thesis by (simp add: restrict_def)
      qed
    qed
    show "restrict \<phi> sem F = restrict \<phi> sem F'"
      if "amb F = amb F'" "slice F = slice F'" "kd F = kd F'" for F F'
    proof -
      have "sem (frestrict \<phi> F) = sem (frestrict \<phi> F')"
        by (rule eff_law) (use that in simp_all)
      then show ?thesis by (simp add: restrict_def)
    qed
    show "compact mind" by (rule mind_compact)
    show "compact ?D" by (rule compact_top_dims[OF n dims_compact])
    show "?D \<rho> \<sqsubseteq> ?D \<bottom>" for \<rho> by (rule top_dims_bot) (rule dims_bot)
  qed
qed

end
