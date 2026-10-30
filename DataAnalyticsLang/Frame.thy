theory Frame
  imports Slicer Views
begin

default_sort type

section \<open>Frames\<close>

text \<open>Guards are continuous truth-valued functions of rows: three-valued conditions, undecided
  on rows too partial to decide them.  The guard every row passes, and the parallel conjunction of
  guards, under which falsity of either side decides.\<close>

type_synonym 'r guard = "'r \<rightarrow> tr"

definition gtrue :: "'r::cpo guard" where
  "gtrue = (\<Lambda> _. TT)"

definition gand :: "'r::cpo guard \<Rightarrow> 'r guard \<Rightarrow> 'r guard" where
  "gand \<gamma> \<delta> = (\<Lambda> y. pand\<cdot>(\<gamma>\<cdot>y)\<cdot>(\<delta>\<cdot>y))"

lemma gtrue_apply [simp]: "gtrue\<cdot>y = TT"
  by (simp add: gtrue_def)

lemma gand_apply: "gand \<gamma> \<delta>\<cdot>y = pand\<cdot>(\<gamma>\<cdot>y)\<cdot>(\<delta>\<cdot>y)"
  by (simp add: gand_def)

lemma gand_TT [simp]: "gand \<gamma> \<delta>\<cdot>y = TT \<longleftrightarrow> \<gamma>\<cdot>y = TT \<and> \<delta>\<cdot>y = TT"
  and gand_FF [simp]: "gand \<gamma> \<delta>\<cdot>y = FF \<longleftrightarrow> \<gamma>\<cdot>y = FF \<or> \<delta>\<cdot>y = FF"
  by (simp_all add: gand_apply pand_TT_iff pand_FF_iff)

lemma gand_gtrue [simp]: "gand \<gamma> gtrue = \<gamma>" "gand gtrue \<gamma> = \<gamma>"
  by (simp_all add: cfun_eq_iff gand_apply)

lemma gand_assoc: "gand (gand \<gamma> \<delta>) \<epsilon> = gand \<gamma> (gand \<delta> \<epsilon>)"
  by (simp add: cfun_eq_iff gand_apply pand_assoc)

lemma gand_commute: "gand \<gamma> \<delta> = gand \<delta> \<gamma>"
  by (simp add: cfun_eq_iff gand_apply pand_commute)

lemma gand_left_commute: "gand \<gamma> (gand \<delta> \<epsilon>) = gand \<delta> (gand \<gamma> \<epsilon>)"
  by (metis gand_assoc gand_commute)

lemmas gand_ac = gand_assoc gand_commute gand_left_commute

text \<open>A frame has a level of detail and two levels of filters.  The \<^emph>\<open>ambient\<close> filter is a guard:
  expressions may add to it (an MDX-style subselect), but never take it apart or discard it.  The
  \<^emph>\<open>slice\<close> is a syntactic filter on keys that expressions coarsen; dropping detail from the frame
  always coarsens the slice as well.  The frame's LOD partitions the rows into groups by their
  projected keys; the filters decide, three-valued, which rows of a group take part.\<close>

record ('l::type, 'f::type, 'r::pcpo) frame =
  flod :: 'l
  amb :: "'r guard"
  slice :: 'f

text \<open>The record package's own \<open>truncate\<close> operation would shadow the truncation action.\<close>

hide_const (open) frame.truncate

section \<open>Frame transformers\<close>

text \<open>The level-of-detail constructs act on the frame an inner expression is evaluated under.
  \<open>finclude D\<close> adds detail \<open>D\<close> (\<open>GROUP BY\<close>); \<open>frestrict \<phi>\<close> adds \<open>\<phi>\<close> to the ambient filter;
  \<open>ffor \<tau> G\<close> needs the slicer: it drops detail by a truncation \<open>\<tau>\<close>, from the frame and from the
  slice, and conjoins \<open>G\<close>.  Pegging conjoins a key's pin to the slice.\<close>

definition finclude :: "'l::po \<Rightarrow> ('l, 'f::type, 'r::pcpo) frame \<Rightarrow> ('l, 'f, 'r) frame" where
  "finclude D F = F\<lparr>flod := flod F \<squnion> D\<rparr>"

lemma flod_finclude: "flod (finclude D F) = flod F \<squnion> D"
  by (simp add: finclude_def)

lemma amb_finclude [simp]: "amb (finclude D F) = amb F"
  by (simp add: finclude_def)

lemma slice_finclude [simp]: "slice (finclude D F) = slice F"
  by (simp add: finclude_def)

definition frestrict :: "'r::pcpo guard \<Rightarrow> ('l::type, 'f::type, 'r) frame \<Rightarrow> ('l, 'f, 'r) frame" where
  "frestrict \<phi> F = F\<lparr>amb := gand (amb F) \<phi>\<rparr>"

lemma flod_frestrict [simp]: "flod (frestrict \<phi> F) = flod F"
  by (simp add: frestrict_def)

lemma slice_frestrict [simp]: "slice (frestrict \<phi> F) = slice F"
  by (simp add: frestrict_def)

lemma amb_frestrict [simp]: "amb (frestrict \<phi> F) = gand (amb F) \<phi>"
  by (simp add: frestrict_def)

section \<open>Frame semantics\<close>

text \<open>A dataspace fixes a slicer and a schema with keys; datasets are elements of the lower
  powerdomain of rows, their data points the maximal members.  Rows have keys, via \<open>rkey\<close>; a frame's
  filter on rows conjoins its ambient filter with its slice at the row's key.  A slice coarsened to
  an upper part \<open>\<rho>\<close> gives the frame's filter as seen by a group that keeps only \<open>\<rho>\<close>.\<close>

locale dataspace = slicer slicing + keyed_schema rules keying
  for slicing :: "('f, 'k::{domain, lod_domain}) slicer_ops"
    and rules :: "'r::{domain, lod_domain} schema_rules" and keying :: "('r, 'k) keying"
begin

definition guard_holds :: "'f \<Rightarrow> 'r guard" where
  "guard_holds X = sopen X oo proj (slod X) oo rkey"

lemma guard_holds_apply: "guard_holds X\<cdot>y = sopen X\<cdot>(rkey\<cdot>y)"
  by (simp add: guard_holds_def sopen_lod)

lemma guard_holds_TT [simp]: "guard_holds X\<cdot>y = TT \<longleftrightarrow> holds X (rkey\<cdot>y)"
  by (simp add: guard_holds_apply holds_def)

lemma guard_holds_conj: "guard_holds (a \<^bold>* b) = gand (guard_holds a) (guard_holds b)"
  by (simp add: cfun_eq_iff guard_holds_apply gand_apply sopen_conj)

lemma guard_holds_unit [simp]: "guard_holds \<^bold>1 = gtrue"
  by (simp add: cfun_eq_iff guard_holds_apply sopen_unit)

definition fguard :: "'k semi_factor \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'r guard" where
  "fguard \<rho> F = gand (amb F) (guard_holds (coarsen \<rho> (slice F)))"

definition frows :: "('k semi_factor, 'f, 'r) frame \<Rightarrow> 'r guard" where
  "frows F = gand (amb F) (guard_holds (slice F))"

lemma fguard_top [simp]: "fguard \<top> F = frows F"
  by (simp add: fguard_def frows_def)

lemma fguard_cong: "amb F = amb F' \<Longrightarrow> slice F = slice F' \<Longrightarrow> fguard \<rho> F = fguard \<rho> F'"
  by (simp add: fguard_def)

lemma frows_cong: "amb F = amb F' \<Longrightarrow> slice F = slice F' \<Longrightarrow> frows F = frows F'"
  by (simp add: frows_def)

lemma fguard_finclude [simp]: "fguard \<rho> (finclude D F) = fguard \<rho> F"
  and frows_finclude [simp]: "frows (finclude D F) = frows F"
  by (simp_all add: fguard_def frows_def)

lemma fguard_frestrict: "fguard \<rho> (frestrict \<phi> F) = gand (fguard \<rho> F) \<phi>"
  and frows_frestrict: "frows (frestrict \<phi> F) = gand (frows F) \<phi>"
  by (simp_all add: fguard_def frows_def gand_ac)

definition ffor :: "'k semi_factor \<Rightarrow> 'f \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> ('k semi_factor, 'f, 'r) frame" where
  "ffor \<tau> G F = F\<lparr>flod := (\<tau> \<sqinter> flod F), slice := coarsen \<tau> (slice F) \<^bold>* G\<rparr>"

lemma flod_ffor [simp]: "flod (ffor \<tau> G F) = (\<tau> \<sqinter> flod F)"
  and amb_ffor [simp]: "amb (ffor \<tau> G F) = amb F"
  and slice_ffor [simp]: "slice (ffor \<tau> G F) = coarsen \<tau> (slice F) \<^bold>* G"
  by (simp_all add: ffor_def)

definition peg :: "'k \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> ('k semi_factor, 'f, 'r) frame" where
  "peg K F = F\<lparr>slice := slice F \<^bold>* spin K\<rparr>"

lemma flod_peg [simp]: "flod (peg K F) = flod F"
  by (simp add: peg_def)

lemma amb_peg [simp]: "amb (peg K F) = amb F"
  by (simp add: peg_def)

lemma slice_peg [simp]: "slice (peg K F) = slice F \<^bold>* spin K"
  by (simp add: peg_def)

lemma frows_peg: "compact K \<Longrightarrow> K \<sqsubseteq> rkey\<cdot>r \<Longrightarrow> frows (peg K F)\<cdot>r = frows F\<cdot>r"
  by (simp add: frows_def gand_apply guard_holds_conj holds_spin[unfolded holds_def, symmetric] guard_holds_apply)

text \<open>Pegging commutes with the transformers that keep the slice.\<close>

lemma peg_finclude: "peg K (finclude D F) = finclude D (peg K F)"
  by (simp add: peg_def finclude_def)

lemma peg_frestrict: "peg K (frestrict \<phi> F) = frestrict \<phi> (peg K F)"
  by (simp add: peg_def frestrict_def)

end

section \<open>Key images\<close>

text \<open>The keys a frame has at an LOD are the projections of the data points its filter does not
  reject.\<close>

context dataspace
begin

definition keyimg :: "'r lower_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k semi_factor \<Rightarrow> 'k \<Rightarrow> bool" where
  "keyimg data F c k \<longleftrightarrow> (\<exists>x\<in>lower_maximal data. frows F\<cdot>x \<noteq> FF \<and> k = proj c\<cdot>(rkey\<cdot>x))"

lemma keyimg_cong: "frows F = frows F' \<Longrightarrow> keyimg data F c = keyimg data F' c"
  by (simp add: keyimg_def fun_eq_iff)

lemma keyimg_mono: "(\<And>r. frows F\<cdot>r \<noteq> FF \<Longrightarrow> frows F'\<cdot>r \<noteq> FF) \<Longrightarrow> keyimg data F c k \<Longrightarrow> keyimg data F' c k"
  unfolding keyimg_def by blast

text \<open>Keys conform to the slice: it is not false above them.\<close>

lemma keyimg_slicer: "keyimg data F c k \<Longrightarrow> \<exists>k'. k \<sqsubseteq> k' \<and> sopen (slice F)\<cdot>k' \<noteq> FF"
  unfolding keyimg_def frows_def using proj_below by (fastforce simp: gand_FF guard_holds_apply)

lemma keyimg_peg_iff:
  assumes K: "compact K" shows "keyimg data (peg K F) c K \<longleftrightarrow> keyimg data F c K"
proof -
  have "frows (peg K F)\<cdot>x = frows F\<cdot>x" if "K = proj c\<cdot>(rkey\<cdot>x)" for x
    by (rule frows_peg[OF K]) (simp only: that proj_below)
  then show ?thesis unfolding keyimg_def by (metis (no_types, lifting))
qed

end

context dataspace
begin

text \<open>An LOD is read on rows through their keys; reading at a join of LODs is reading at both.\<close>

lemma rproj_sup_eq: "rproj (a \<squnion> b) y = rproj (a \<squnion> b) z \<longleftrightarrow> rproj a y = rproj a z \<and> rproj b y = rproj b z"
proof
  assume e: "rproj (a \<squnion> b) y = rproj (a \<squnion> b) z"
  show "rproj a y = rproj a z \<and> rproj b y = rproj b z"
    using arg_cong[OF e, of "Rep_cfun (proj a)"] arg_cong[OF e, of "Rep_cfun (proj b)"]
    by (simp add: proj_le lattice_join_ge1 lattice_join_ge2)
qed (simp add: proj_sup)

end

end
