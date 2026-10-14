theory Frame
  imports Slicer
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
  "ffor \<tau> G F = F\<lparr>flod := \<tau> (flod F), slice := coarsen (\<tau> (slod (slice F))) (slice F) \<^bold>* G\<rparr>"

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

text \<open>A fixed expression has LODs \<^term>\<open>mind\<close> \<open>\<le>\<close> \<^term>\<open>maxd\<close> and a semantics: a map from frames
  and keys to values, with \<^term>\<open>\<bottom>\<close> for ``no entry''.  Its key LOD under a frame is what it
  decides itself plus what of the frame it can be evaluated up to.  The \<^emph>\<open>key laws\<close> say that keys
  conform to the slice, are maximal at the key LOD, and come from data points; the \<^emph>\<open>peg law\<close>
  says that pegging the frame to a key does not change the value there; the \<^emph>\<open>dims law\<close> says
  that in frames pinning a key \<open>K\<close> at \<open>L\<close>, varying the frame's LOD within \<open>L\<close> moves each entry to
  the corresponding key (the truncated join with \<open>K\<close>) without changing its value; the
  \<^emph>\<open>effective-LOD law\<close> says that the semantics depends on a frame's LOD only through the key
  LOD.  The slice is compared syntactically, since coarsening is not extensional.  Combinators
  are then maps from lawful semantics to lawful semantics.\<close>

locale dataspace = frame_sem proj conj sunit slod sopen coarsen spin rkey
  for proj :: "'l::{distrib_lattice, bounded_lattice_bot} \<Rightarrow> 'k::bounded_complete \<rightarrow> 'k"
    and conj :: "'f \<Rightarrow> 'f \<Rightarrow> 'f" (infixl \<open>\<^bold>*\<close> 70) and sunit :: 'f (\<open>\<^bold>1\<close>)
    and slod sopen coarsen spin and rkey :: "'r::pcpo \<rightarrow> 'k" +
  fixes S :: "'r set"
  assumes dataset_S: "dataset S"

locale expr_sem = dataspace +
  fixes mind maxd sem
  assumes mind_maxd: "mind \<le> maxd"
    and key_slicer: "sem F k \<noteq> \<bottom> \<Longrightarrow> \<exists>k'. k \<sqsubseteq> k' \<and> holds (slice F) k'"
    and key_max: "sem F k \<noteq> \<bottom> \<Longrightarrow> maximal_at (inf (sup mind (flod F)) maxd) k"
    and key_data: "sem F k \<noteq> \<bottom> \<Longrightarrow> keyimg S F (inf (sup mind (flod F)) maxd) k"
    and peg_law: "compact K \<Longrightarrow> sem (peg K F) K = sem F K"
    and dims_law: "\<lbrakk>amb F = amb F'; slice F = slice F'; pins F L K;
                    sup (flod F) L = sup (flod F') L; sem F K1 \<noteq> \<bottom>\<rbrakk>
                   \<Longrightarrow> sem F' (proj (inf (sup mind (flod F')) maxd)\<cdot>(K1 \<squnion> K)) = sem F K1"
    and eff_law: "\<lbrakk>amb F = amb F'; slice F = slice F';
                   inf (sup mind (flod F)) maxd = inf (sup mind (flod F')) maxd\<rbrakk>
                  \<Longrightarrow> sem F = sem F'"
begin

abbreviation "kd F \<equiv> inf (sup mind (flod F)) maxd"

text \<open>The compatibility the dims law relies on is automatic.\<close>

lemma pinned_entry:
  assumes "pins F L K" "sem F K1 \<noteq> \<bottom>"
  shows "proj (kd F)\<cdot>K \<sqsubseteq> K1" "K1 \<Up> K"
proof -
  obtain k' where "K1 \<sqsubseteq> k'" "holds (slice F) k'" using key_slicer[OF assms(2)] by blast
  with assms(1) key_max[OF assms(2)] show "proj (kd F)\<cdot>K \<sqsubseteq> K1" "K1 \<Up> K"
    by (blast intro: pin_below_key)+
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
    have km: "maximal_at (kd F) k" using key_max[OF nb] by simp
    obtain k' where kk: "k \<sqsubseteq> k'" and h: "holds (slice F \<^bold>* spin K) k'"
      using key_slicer[OF nb] by auto
    have "K \<sqsubseteq> k'" using h by (simp add: holds_spin maximal_at_compact[OF K])
    then have "proj (kd F)\<cdot>K \<sqsubseteq> k" by (rule proj_below_maximal[OF km _ kk])
    then have "K \<sqsubseteq> k" by (simp only: maximal_at_lives[OF K])
    then have "k = K" by (rule maximal_at_eq[OF K maximal_at_lives[OF km]])
    with False show False ..
  qed
qed

text \<open>Values at different levels of detail: the value at a finer key is the value at its
  truncation, once the finer key is pinned by the slice.  The finer frame is first trimmed to
  detail the expression can see (effective-LOD law), so that the extra detail lies within the
  finer key's LOD; then the dims law moves the entry.\<close>

theorem lod_shift:
  assumes "amb F1 = amb F2" "slice F1 = slice F2" "flod F1 \<le> flod F2" "sem F2 K2 \<noteq> \<bottom>"
  shows "sem (peg K2 F1) k = (if k = proj (kd F1)\<cdot>K2 then sem F2 K2 else \<bottom>)"
proof -
  define F2' where "F2' = F2\<lparr>flod := sup (flod F1) (inf (flod F2) maxd)\<rparr>"
  let ?L = "kd F2" and ?k = "proj (kd F1)\<cdot>K2"
  have mm: "inf mind maxd = mind" using mind_maxd by (rule inf_absorb1)
  have kdF2: "kd F2 = sup mind (inf (flod F2) maxd)"
    by (simp add: inf_sup_distrib2 mm)
  have "kd F2' = sup mind (sup (inf (flod F1) maxd) (inf (flod F2) maxd))"
    by (simp add: F2'_def inf_sup_distrib2 mm)
  also have "sup (inf (flod F1) maxd) (inf (flod F2) maxd) = inf (flod F2) maxd"
    by (rule sup_absorb2) (rule inf_mono[OF assms(3) order_refl])
  finally have "kd F2' = kd F2" by (simp only: kdF2)
  then have same: "sem F2' = sem F2" by (intro eff_law) (simp_all add: F2'_def)
  have K2m: "maximal_at ?L K2" by (rule key_max[OF assms(4)])
  have cK2: "compact K2" by (rule maximal_at_compact[OF K2m])
  have sp: "sem (peg K2 F2') K2 = sem F2 K2" using peg_law[OF cK2] same by simp
  have f1: "amb (peg K2 F2') = amb (peg K2 F1)" "slice (peg K2 F2') = slice (peg K2 F1)"
    by (simp_all add: F2'_def assms(1,2))
  have f2: "sup (flod (peg K2 F2')) ?L = sup (flod (peg K2 F1)) ?L"
  proof -
    have "inf (flod F2) maxd \<le> ?L" by (simp add: kdF2)
    then show ?thesis by (simp add: F2'_def sup_assoc sup_absorb2)
  qed
  have f3: "sem (peg K2 F2') K2 \<noteq> \<bottom>" using assms(4) sp by simp
  have v: "sem (peg K2 F1) ?k = sem F2 K2"
    using dims_law[OF f1 pins_peg[OF K2m] f2 f3] by (simp add: sp)
  have sub: "kd F1 \<le> ?L" using assms(3) by (intro inf_mono sup_mono) simp_all
  have km1: "maximal_at (kd F1) ?k" by (rule maximal_at_proj[OF sub K2m])
  show ?thesis
  proof (cases "k = ?k")
    case True with v show ?thesis by simp
  next
    case False
    show ?thesis
    proof (rule ccontr)
      assume "sem (peg K2 F1) k \<noteq> (if k = ?k then sem F2 K2 else \<bottom>)"
      with False have nb: "sem (peg K2 F1) k \<noteq> \<bottom>" by simp
      have km: "maximal_at (kd F1) k" using key_max[OF nb] by simp
      obtain k' where kk: "k \<sqsubseteq> k'" and h: "holds (slice F1 \<^bold>* spin K2) k'"
        using key_slicer[OF nb] by auto
      have "K2 \<sqsubseteq> k'" using h by (simp add: holds_spin cK2)
      then have "?k \<sqsubseteq> k" by (rule proj_below_maximal[OF km _ kk])
      then have "k = ?k" by (rule maximal_at_eq[OF km1 maximal_at_lives[OF km]])
      with False show False ..
    qed
  qed
qed

end

text \<open>Within a dataspace, a semantics is \<^emph>\<open>lawful\<close> when it forms an \<^locale>\<open>expr_sem\<close>
  instance; combinators are then plain theorems concluding lawfulness.\<close>

context dataspace
begin

abbreviation lawful where "lawful \<equiv> expr_sem proj conj sunit slod sopen coarsen spin rkey S"

lemma lawfulI:
  assumes "mind \<le> maxd"
    and "\<And>F k. sem F k \<noteq> \<bottom> \<Longrightarrow> \<exists>k'. k \<sqsubseteq> k' \<and> holds (slice F) k'"
    and "\<And>F k. sem F k \<noteq> \<bottom> \<Longrightarrow> maximal_at (inf (sup mind (flod F)) maxd) k"
    and "\<And>F k. sem F k \<noteq> \<bottom> \<Longrightarrow> keyimg S F (inf (sup mind (flod F)) maxd) k"
    and "\<And>F K. compact K \<Longrightarrow> sem (peg K F) K = sem F K"
    and "\<And>F F' L K K1. \<lbrakk>amb F = amb F'; slice F = slice F'; pins F L K;
                        sup (flod F) L = sup (flod F') L; sem F K1 \<noteq> \<bottom>\<rbrakk>
                       \<Longrightarrow> sem F' (proj (inf (sup mind (flod F')) maxd)\<cdot>(K1 \<squnion> K)) = sem F K1"
    and "\<And>F F'. \<lbrakk>amb F = amb F'; slice F = slice F';
                 inf (sup mind (flod F)) maxd = inf (sup mind (flod F')) maxd\<rbrakk>
                 \<Longrightarrow> sem F = sem F'"
  shows "lawful mind maxd sem"
  by (intro expr_sem.intro dataspace_axioms expr_sem_axioms.intro) (fact assms)+

end

section \<open>Combinators\<close>

subsection \<open>\<open>INCLUDE\<close>\<close>

definition group_by where
  "group_by D sem = (\<lambda>F. sem (finclude D F))"

theorem (in expr_sem) lawful_group_by:
  "lawful (sup mind (inf D maxd)) maxd (group_by D sem)"
proof (rule lawfulI)
  have mm: "inf mind maxd = mind" using mind_maxd by (rule inf_absorb1)
  have kd: "inf (sup (sup mind (inf D maxd)) X) maxd = inf (sup mind (sup X D)) maxd" for X
  proof -
    have "inf (sup (sup mind (inf D maxd)) X) maxd = sup (sup mind (inf D maxd)) (inf X maxd)"
      by (simp only: inf_sup_distrib2 mm inf_assoc inf_idem)
    also have "\<dots> = sup mind (sup (inf X maxd) (inf D maxd))" by (simp only: ac_simps)
    also have "\<dots> = inf (sup mind (sup X D)) maxd" by (simp only: inf_sup_distrib2 mm)
    finally show ?thesis .
  qed
  show "sup mind (inf D maxd) \<le> maxd" using mind_maxd by simp
  show "\<exists>k'. k \<sqsubseteq> k' \<and> holds (slice F) k'" if "group_by D sem F k \<noteq> \<bottom>" for F k
    using key_slicer[of "finclude D F" k] that by (simp add: group_by_def)
  show "maximal_at (inf (sup (sup mind (inf D maxd)) (flod F)) maxd) k"
    if "group_by D sem F k \<noteq> \<bottom>" for F k
    using key_max[of "finclude D F" k] that by (simp add: group_by_def kd)
  show "keyimg S F (inf (sup (sup mind (inf D maxd)) (flod F)) maxd) k"
    if "group_by D sem F k \<noteq> \<bottom>" for F k
    using key_data[of "finclude D F" k] that keyimg_cong[of "finclude D F" F S]
    by (simp add: group_by_def kd)
  show "group_by D sem (peg K F) K = group_by D sem F K" if "compact K" for F K
    by (simp add: group_by_def peg_finclude[symmetric] peg_law[OF that])
  show "group_by D sem F' (proj (inf (sup (sup mind (inf D maxd)) (flod F')) maxd)\<cdot>(K1 \<squnion> K))
          = group_by D sem F K1"
    if "amb F = amb F'" "slice F = slice F'" "pins F L K" "sup (flod F) L = sup (flod F') L"
       "group_by D sem F K1 \<noteq> \<bottom>" for F F' L K K1
  proof -
    have "pins (finclude D F) L K" using that(3) by (simp add: pins_def)
    moreover have "sup (flod (finclude D F)) L = sup (flod (finclude D F')) L"
    proof -
      have e: "sup (sup a D) L = sup (sup a L) D" for a by (simp only: sup_assoc sup_commute[of D L])
      show ?thesis by (simp only: flod_finclude e that(4))
    qed
    ultimately show ?thesis
      using dims_law[of "finclude D F" "finclude D F'" L K K1] that(1,2,5)
      by (simp add: group_by_def kd)
  qed
  show "group_by D sem F = group_by D sem F'"
    if "amb F = amb F'" "slice F = slice F'"
       "inf (sup (sup mind (inf D maxd)) (flod F)) maxd = inf (sup (sup mind (inf D maxd)) (flod F')) maxd"
    for F F'
  proof -
    have "sem (finclude D F) = sem (finclude D F')"
      by (rule eff_law) (use that in \<open>simp_all add: kd\<close>)
    then show ?thesis by (simp add: group_by_def)
  qed
qed

subsection \<open>Fixed-level constructs: \<open>GROUP BY ONLY\<close>, \<open>TOTAL\<close>, \<open>ISOLATE\<close>\<close>

text \<open>A construct that evaluates its argument under a transformed frame at a fixed key LOD
  \<^term>\<open>E\<close>, restricted back to the incoming frame's keys.  It is lawful whenever the transformer
  sees the incoming frame only through its filters, and pegging the incoming frame does not
  change the inner value at the key.  This needs nothing of the inner semantics.\<close>

context dataspace
begin

definition fixed where
  "fixed E T sem F k = (if fkeys S F E k then sem (T F) k else \<bottom>)"

theorem lawful_fixed:
  assumes "\<And>F K. compact K \<Longrightarrow> sem (T (peg K F)) K = sem (T F) K"
    and "\<And>F F'. amb F = amb F' \<Longrightarrow> slice F = slice F' \<Longrightarrow> T F = T F'"
  shows "lawful E E (fixed E T sem)"
proof (rule lawfulI)
  have E: "\<And>X. inf (sup E X) E = E" by (simp add: inf_absorb2)
  show "E \<le> E" by simp
  show "\<exists>k'. k \<sqsubseteq> k' \<and> holds (slice F) k'" if "fixed E T sem F k \<noteq> \<bottom>" for F k
    using that by (auto simp: fixed_def fkeys_def split: if_splits dest: keyimg_slicer)
  show "maximal_at (inf (sup E (flod F)) E) k" if "fixed E T sem F k \<noteq> \<bottom>" for F k
    using that by (auto simp: fixed_def fkeys_def E split: if_splits)
  show "keyimg S F (inf (sup E (flod F)) E) k" if "fixed E T sem F k \<noteq> \<bottom>" for F k
    using that by (auto simp: fixed_def fkeys_def E split: if_splits)
  show "fixed E T sem (peg K F) K = fixed E T sem F K" if "compact K" for F K
    by (simp add: fixed_def fkeys_peg_iff[OF that] assms(1)[OF that])
  show "fixed E T sem F' (proj (inf (sup E (flod F')) E)\<cdot>(K1 \<squnion> K)) = fixed E T sem F K1"
    if "amb F = amb F'" "slice F = slice F'" "pins F L K" "sup (flod F) L = sup (flod F') L"
       "fixed E T sem F K1 \<noteq> \<bottom>" for F F' L K K1
  proof -
    have K1: "fkeys S F E K1" using that(5) by (auto simp: fixed_def split: if_splits)
    then have m: "maximal_at E K1" and ki: "keyimg S F E K1" by (simp_all add: fkeys_def)
    obtain k' where "K1 \<sqsubseteq> k'" "holds (slice F) k'" using keyimg_slicer[OF ki] by blast
    then have le: "proj E\<cdot>K \<sqsubseteq> K1" and j: "K1 \<Up> K" using pin_below_key[OF that(3) m] by blast+
    have "proj E\<cdot>(K1 \<squnion> K) = K1"
      by (simp add: proj_join[OF j] maximal_at_lives[OF m] join_absorb2[OF le])
    moreover have "fkeys S F' E = fkeys S F E"
      by (rule fkeys_cong[OF frows_cong[OF that(1,2)], symmetric])
    moreover have "T F' = T F" using assms(2)[OF that(1,2)] by simp
    ultimately show ?thesis by (simp add: fixed_def E)
  qed
  show "fixed E T sem F = fixed E T sem F'"
    if "amb F = amb F'" "slice F = slice F'" "inf (sup E (flod F)) E = inf (sup E (flod F')) E"
    for F F'
  proof -
    have "fkeys S F E = fkeys S F' E" by (rule fkeys_cong[OF frows_cong[OF that(1,2)]])
    then show ?thesis using assms(2)[OF that(1,2)] by (simp add: fixed_def fun_eq_iff)
  qed
qed

end

context expr_sem
begin

definition group_by_only where
  "group_by_only D = fixed (inf (sup mind D) maxd) (fgroupby D) sem"

abbreviation total where
  "total \<equiv> group_by_only bot"

theorem lawful_group_by_only:
  "lawful (inf (sup mind D) maxd) (inf (sup mind D) maxd) (group_by_only D)"
  unfolding group_by_only_def
proof (rule lawful_fixed)
  show "sem (fgroupby D (peg K F)) K = sem (fgroupby D F) K" if "compact K" for F K
    by (simp add: fgroupby_peg[OF that] peg_below[OF proj_compact that proj_below])
  show "fgroupby D F = fgroupby D F'" if "amb F = amb F'" "slice F = slice F'" for F F'
    using that by (cases F, cases F') (simp add: fgroupby_def)
qed

definition isolate where
  "isolate = fixed mind fisolate sem"

theorem lawful_isolate: "lawful mind mind isolate"
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
  assumes tf: "lod_tf \<tau>" shows "inf (sup mind (\<tau> (flod F))) maxd = sup mind (\<tau> (kd F))"
proof -
  have mm: "inf mind maxd = mind" using mind_maxd by (rule inf_absorb1)
  have "\<tau> (kd F) = inf maxd (sup (\<tau> mind) (\<tau> (flod F)))"
    by (simp add: inf_commute tf_module[OF tf] tf_sup[OF tf])
  then have "sup mind (\<tau> (kd F)) = inf (sup mind maxd) (sup mind (sup (\<tau> mind) (\<tau> (flod F))))"
    by (simp add: sup_inf_distrib1)
  also have "sup mind maxd = maxd" using mind_maxd by (rule sup_absorb2)
  also have "sup mind (sup (\<tau> mind) (\<tau> (flod F))) = sup mind (\<tau> (flod F))"
    using tf_below[OF tf, of mind] by (simp add: sup_absorb1 sup_assoc[symmetric])
  finally show ?thesis by (simp add: inf_commute)
qed

lemma kd_ffor_le: assumes tf: "lod_tf \<tau>" shows "kd (ffor \<tau> G F) \<le> kd F"
  by (simp only: flod_ffor) (intro inf_mono sup_mono order_refl tf_below[OF tf])

lemma kd_ffor_tf: assumes tf: "lod_tf \<tau>" shows "\<tau> (kd F) \<le> kd (ffor \<tau> G F)"
  by (simp only: flod_ffor kd_ffor[OF tf]) (rule sup_ge2)

text \<open>Under a change of frame LOD within \<open>L\<close>, key LODs change within \<open>L\<close> too.\<close>

lemma kd_within:
  assumes "sup (flod F) L = sup (flod F') L"
  shows "kd F' \<le> sup (kd F) L"
proof -
  have "kd F' \<le> inf (sup mind (sup (flod F') L)) maxd" by (intro inf_mono sup_mono) simp_all
  also have "sup mind (sup (flod F') L) = sup (sup mind (flod F)) L"
    by (simp only: assms[symmetric] sup_assoc)
  also have "inf (sup (sup mind (flod F)) L) maxd \<le> sup (kd F) L"
    by (simp only: inf_sup_distrib2) (rule sup_mono[OF order_refl inf_le1])
  finally show ?thesis .
qed

theorem lawful_filtfor:
  assumes tf: "lod_tf \<tau>" shows "lawful mind maxd (filtfor \<tau> G)"
proof (rule lawfulI)
  show "mind \<le> maxd" by (rule mind_maxd)
  show "\<exists>k'. k \<sqsubseteq> k' \<and> holds (slice F) k'" if "filtfor \<tau> G F k \<noteq> \<bottom>" for F k
    using that by (auto simp: filtfor_def fkeys_def split: if_splits dest: keyimg_slicer)
  show "maximal_at (kd F) k" if "filtfor \<tau> G F k \<noteq> \<bottom>" for F k
    using that by (auto simp: filtfor_def fkeys_def split: if_splits)
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
  show "filtfor \<tau> G F' (proj (kd F')\<cdot>(K1 \<squnion> K)) = filtfor \<tau> G F K1"
    if "amb F = amb F'" "slice F = slice F'" "pins F L K" "sup (flod F) L = sup (flod F') L"
       "filtfor \<tau> G F K1 \<noteq> \<bottom>" for F F' L K K1
  proof -
    note asm = that
    let ?H = "ffor \<tau> G F" and ?H' = "ffor \<tau> G F'" and ?K'' = "proj (\<tau> L)\<cdot>K"
    from asm(5) have K1: "fkeys S F (kd F) K1" and ni: "sem ?H (proj (kd ?H)\<cdot>K1) \<noteq> \<bottom>"
      by (auto simp: filtfor_def split: if_splits)
    then have K1m: "maximal_at (kd F) K1" and K1i: "keyimg S F (kd F) K1"
      by (simp_all add: fkeys_def)
    obtain x where x: "x \<in> pts S" "frows F x" and K1x: "K1 = proj (kd F)\<cdot>(rkey\<cdot>x)"
      using K1i by (auto simp: keyimg_def)
    have Km: "maximal_at L K" using asm(3) by (simp add: pins_def)
    have cK: "compact K" by (rule pins_compact[OF asm(3)])
    have Kx: "K = proj L\<cdot>(rkey\<cdot>x)" by (rule pinned_key[OF asm(3) x(2), symmetric])
    have j: "K1 \<Up> K" by (rule joinableI[of _ "rkey\<cdot>x"]) (simp_all add: K1x Kx proj_below)
    have jx: "K1 \<squnion> K = proj (sup (kd F) L)\<cdot>(rkey\<cdot>x)" by (simp add: proj_sup K1x Kx)
    have sF': "kd F' \<le> sup (kd F) L" by (rule kd_within[OF asm(4)])
    have K1'x: "proj (kd F')\<cdot>(K1 \<squnion> K) = proj (kd F')\<cdot>(rkey\<cdot>x)"
      by (simp add: jx proj_le[OF sF'])
    have xF': "frows F' x" using x(2) frows_cong[OF asm(1,2)] by simp
    have K1'k: "fkeys S F' (kd F') (proj (kd F')\<cdot>(K1 \<squnion> K))"
      unfolding fkeys_def
    proof
      show "keyimg S F' (kd F') (proj (kd F')\<cdot>(K1 \<squnion> K))"
        unfolding keyimg_def K1'x using x(1) xF' by blast
      show "maximal_at (kd F') (proj (kd F')\<cdot>(K1 \<squnion> K))"
        by (rule maximal_at_proj[OF sF' maximal_at_join[OF K1m Km j]])
    qed
    text \<open>The inner frames pin the truncated key at the transformed LOD.\<close>
    have pH: "pins ?H (\<tau> L) ?K''"
      unfolding pins_def
    proof
      show "maximal_at (\<tau> L) ?K''" by (rule maximal_at_proj[OF tf_below[OF tf] Km])
      have le: "slice F \<^bold>\<le> spin K" using asm(3) by (simp add: pins_def)
      let ?A = "\<tau> (slod (slice F))"
      have "slod (slice F) = sup (slod (slice F)) (slod (spin K))"
        using le by (metis sle_def slod_conj)
      then have "lives_at (slod (slice F)) K"
        using lives_at_up[of "slod (spin K)" K] slod_spin_lives[OF cK]
        by (metis lives_at_def sup_ge2)
      then have eq: "proj ?A\<cdot>K = ?K''"
        by (rule tf_proj_irrelevant[OF tf]) (simp add: lives_at_def maximal_at_lives[OF Km])
      have "coarsen ?A (slice F) \<^bold>\<le> coarsen ?A (spin K)" by (rule coarsen_mono[OF le])
      then have "coarsen ?A (slice F) \<^bold>\<le> spin ?K''" by (simp only: coarsen_spin[OF cK] eq)
      moreover have "slice ?H \<^bold>\<le> coarsen ?A (slice F)" by (simp add: ffor_def)
      ultimately show "slice ?H \<^bold>\<le> spin ?K''" by (rule sord.trans[rotated])
    qed
    have fH: "amb ?H = amb ?H'" "slice ?H = slice ?H'" by (simp_all add: ffor_def asm(1,2))
    have dH: "sup (flod ?H) (\<tau> L) = sup (flod ?H') (\<tau> L)"
      by (simp add: tf_sup[OF tf, symmetric] asm(4))
    have IH: "sem ?H' (proj (kd ?H')\<cdot>(proj (kd ?H)\<cdot>K1 \<squnion> ?K'')) = sem ?H (proj (kd ?H)\<cdot>K1)"
      by (rule dims_law[OF fH pH dH ni])
    text \<open>Both sides are the row's key at the inner key LOD.\<close>
    have e1: "proj (kd ?H)\<cdot>K1 = proj (kd ?H)\<cdot>(rkey\<cdot>x)" by (simp only: K1x proj_le[OF kd_ffor_le[OF tf]])
    have e2: "?K'' = proj (\<tau> L)\<cdot>(rkey\<cdot>x)" by (simp add: Kx proj_le[OF tf_below[OF tf]])
    have sH': "kd ?H' \<le> sup (kd ?H) (\<tau> L)"
    proof -
      have "kd ?H' = sup mind (\<tau> (kd F'))" by (simp only: flod_ffor kd_ffor[OF tf])
      also have "\<dots> \<le> sup mind (\<tau> (sup (kd F) L))" using sF' by (intro sup_mono tf_mono[OF tf]) simp_all
      also have "\<dots> = sup (sup mind (\<tau> (kd F))) (\<tau> L)" by (simp add: tf_sup[OF tf] sup_assoc)
      also have "\<dots> = sup (kd ?H) (\<tau> L)" by (simp only: flod_ffor kd_ffor[OF tf])
      finally show ?thesis .
    qed
    have key: "proj (kd ?H')\<cdot>(proj (kd ?H)\<cdot>K1 \<squnion> ?K'') = proj (kd ?H')\<cdot>(proj (kd F')\<cdot>(K1 \<squnion> K))"
      by (simp only: e1 e2 K1'x proj_sup[symmetric] proj_le[OF sH'] proj_le[OF kd_ffor_le[OF tf]])
    have "filtfor \<tau> G F' (proj (kd F')\<cdot>(K1 \<squnion> K))
          = sem ?H' (proj (kd ?H')\<cdot>(proj (kd F')\<cdot>(K1 \<squnion> K)))"
      unfolding filtfor_def by (simp only: if_P[OF K1'k])
    also have "\<dots> = sem ?H (proj (kd ?H)\<cdot>K1)" using IH unfolding key .
    also have "\<dots> = filtfor \<tau> G F K1" unfolding filtfor_def by (simp only: if_P[OF K1])
    finally show ?thesis .
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

theorem (in expr_sem) lawful_restrict: "lawful mind maxd (restrict \<phi> sem)"
proof (rule lawfulI)
  show "mind \<le> maxd" by (rule mind_maxd)
  show "\<exists>k'. k \<sqsubseteq> k' \<and> holds (slice F) k'" if "restrict \<phi> sem F k \<noteq> \<bottom>" for F k
    using key_slicer[of "frestrict \<phi> F" k] that by (simp add: restrict_def)
  show "maximal_at (kd F) k" if "restrict \<phi> sem F k \<noteq> \<bottom>" for F k
    using key_max[of "frestrict \<phi> F" k] that by (simp add: restrict_def)
  show "keyimg S F (kd F) k" if "restrict \<phi> sem F k \<noteq> \<bottom>" for F k
    using key_data[of "frestrict \<phi> F" k] that keyimg_mono[of "frestrict \<phi> F" F S]
    by (simp add: restrict_def frows_frestrict)
  show "restrict \<phi> sem (peg K F) K = restrict \<phi> sem F K" if "compact K" for F K
    by (simp add: restrict_def peg_frestrict[symmetric] peg_law[OF that])
  show "restrict \<phi> sem F' (proj (kd F')\<cdot>(K1 \<squnion> K)) = restrict \<phi> sem F K1"
    if "amb F = amb F'" "slice F = slice F'" "pins F L K" "sup (flod F) L = sup (flod F') L"
       "restrict \<phi> sem F K1 \<noteq> \<bottom>" for F F' L K K1
  proof -
    have "pins (frestrict \<phi> F) L K" using that(3) by (simp add: pins_def)
    then show ?thesis
      using dims_law[of "frestrict \<phi> F" "frestrict \<phi> F'" L K K1] that(1,2,4,5)
      by (simp add: restrict_def)
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