theory Frame
  imports Slicer Views
begin

default_sort type

section \<open>Frames\<close>

text \<open>A frame has a level of detail and two levels of filters.  The \<^emph>\<open>ambient\<close> filter is an open
  predicate on rows: expressions may add to it (an MDX-style subselect), but never take it apart
  or discard it.  The \<^emph>\<open>slice\<close> is a syntactic filter on keys that expressions coarsen;
  dropping detail from the frame always coarsens the slice as well.  The frame's LOD partitions
  the selected rows into groups by their projected keys.\<close>

record ('l::type, 'f::type, 'r::pcpo) frame =
  flod :: 'l
  amb :: "'r sel"
  slice :: 'f

text \<open>The record package's own \<open>truncate\<close> operation would shadow the truncation action.\<close>

hide_const (open) frame.truncate

section \<open>Frame transformers\<close>

text \<open>The level-of-detail constructs act on the frame an inner expression is evaluated under.
  \<open>finclude D\<close> adds detail \<open>D\<close> (requested detail: \<open>INCLUDE\<close> is not a combinator of its own, it
  compiles into the grouping inside an aggregate); \<open>frestrict \<phi>\<close> adds \<open>\<phi>\<close> to the ambient filter;
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

definition frestrict :: "'r::pcpo sel \<Rightarrow> ('l::type, 'f::type, 'r) frame \<Rightarrow> ('l, 'f, 'r) frame" where
  "frestrict \<phi> F = F\<lparr>amb := inf (amb F) \<phi>\<rparr>"

lemma flod_frestrict [simp]: "flod (frestrict \<phi> F) = flod F"
  by (simp add: frestrict_def)

lemma slice_frestrict [simp]: "slice (frestrict \<phi> F) = slice F"
  by (simp add: frestrict_def)

lemma amb_frestrict [simp]: "amb (frestrict \<phi> F) = inf (amb F) \<phi>"
  by (simp add: frestrict_def)

section \<open>Frame semantics\<close>

text \<open>A dataspace fixes a slicer and a schema with keys; datasets are elements of the lower
  powerdomain of rows, their data points the maximal members.  Rows have keys, via \<open>rkey\<close>; a frame
  selects the rows in its ambient filter whose key its slice holds at.\<close>

locale dataspace = slicer slicing + keyed_schema rules keying
  for slicing :: "('f, 'k::{domain, lod_domain}) slicer_ops"
    and rules :: "'r::{domain, lod_domain} schema_rules" and keying :: "('r, 'k) keying"
begin

definition frows :: "('k semi_factor, 'f, 'r) frame \<Rightarrow> 'r \<Rightarrow> bool" where
  "frows F r \<longleftrightarrow> selects (amb F) r \<and> holds (slice F) (rkey\<cdot>r)"

lemma frows_cong: "amb F = amb F' \<Longrightarrow> slice F = slice F' \<Longrightarrow> frows F = frows F'"
  by (simp add: frows_def fun_eq_iff)

lemma frows_finclude [simp]: "frows (finclude D F) = frows F"
  by (simp add: frows_def fun_eq_iff)

lemma frows_frestrict: "frows (frestrict \<phi> F) r \<longleftrightarrow> frows F r \<and> selects \<phi> r"
  by (auto simp: frows_def)

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

lemma frows_peg_sub: "frows (peg K F) r \<Longrightarrow> frows F r"
  by (simp add: frows_def)

lemma frows_peg: "compact K \<Longrightarrow> frows (peg K F) r \<longleftrightarrow> frows F r \<and> K \<sqsubseteq> rkey\<cdot>r"
  by (auto simp: frows_def holds_spin)

text \<open>Pegging commutes with the transformers that keep the slice.\<close>

lemma peg_finclude: "peg K (finclude D F) = finclude D (peg K F)"
  by (simp add: peg_def finclude_def)

lemma peg_frestrict: "peg K (frestrict \<phi> F) = frestrict \<phi> (peg K F)"
  by (simp add: peg_def frestrict_def)

end

section \<open>Key images\<close>

text \<open>The keys a frame has at an LOD are the projections of the data points it selects.\<close>

context dataspace
begin

definition keyimg :: "'r lower_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k semi_factor \<Rightarrow> 'k \<Rightarrow> bool" where
  "keyimg data F c k \<longleftrightarrow> (\<exists>x\<in>lower_maximal data. frows F x \<and> k = proj c\<cdot>(rkey\<cdot>x))"

lemma keyimg_cong: "frows F = frows F' \<Longrightarrow> keyimg data F c = keyimg data F' c"
  by (simp add: keyimg_def fun_eq_iff)

lemma keyimg_mono: "(\<And>r. frows F r \<Longrightarrow> frows F' r) \<Longrightarrow> keyimg data F c k \<Longrightarrow> keyimg data F' c k"
  unfolding keyimg_def by blast

text \<open>Keys conform to the slice.\<close>

lemma keyimg_slicer: "keyimg data F c k \<Longrightarrow> \<exists>k'. k \<sqsubseteq> k' \<and> holds (slice F) k'"
  unfolding keyimg_def frows_def using proj_below by blast

lemma keyimg_peg_iff: "compact K \<Longrightarrow> keyimg data (peg K F) c K \<longleftrightarrow> keyimg data F c K"
  unfolding keyimg_def by (auto simp: frows_peg proj_below)

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
