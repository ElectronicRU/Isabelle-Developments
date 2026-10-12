theory Frame
  imports Slicer
begin

section \<open>Frames\<close>

text \<open>A frame has a finite (syntactic) dimension set and two levels of filters.  The \<^emph>\<open>ambient\<close>
  filter is a plain open set of rows: expressions may add to it (an MDX-style subselect) or, by
  \<open>ISOLATE\<close>, discard it, but never take it apart.  The \<^emph>\<open>slice\<close> is a syntactic filter on keys
  that expressions coarsen dimension by dimension; dropping a dimension from the frame always
  coarsens it out of the slice as well.  The dimensions partition the selected rows into
  groups by equality of their level-of-detail tuples.\<close>

record ('d::type, 'f::type, 'r::pcpo) frame =
  fdims :: "'d fset"
  amb :: "'r sel"
  slice :: 'f

definition dims :: "('d::type, 'f::type, 'r::pcpo) frame \<Rightarrow> 'd set" where
  "dims F = fset (fdims F)"

lemma finite_dims [simp]: "finite (dims F)"
  by (simp add: dims_def)

section \<open>Grouping drops points undefined on the grouping dimensions\<close>

text \<open>Data points need not be defined on every dimension (\<open>\<bottom>\<close> = label absent, e.g.\ in a union
  of tables over different label sets).  Grouping by \<^term>\<open>D\<close> first \<^emph>\<open>drops\<close> the points
  undefined on some dimension of \<^term>\<open>D\<close>; promotion of absent values to NULL is left to an
  expression-level primitive.  For flat values and finite \<^term>\<open>D\<close>, ``defined on
  \<^term>\<open>D\<close>'' is itself a filter, and on the surviving points the grouping keys are maximal
  among \<^term>\<open>D\<close>-keys (an antichain) with exactly the coordinates \<^term>\<open>D\<close>.\<close>

lemma cont_defd: "cont (\<lambda>v::'v::flat. if v = \<bottom> then \<bottom> else ONE)"
proof (rule chfindom_monofun2cont, rule monofunI)
  fix x y :: 'v assume "x \<sqsubseteq> y"
  then have "x = \<bottom> \<or> x = y" by (rule ax_flat)
  then show "(if x = \<bottom> then \<bottom> else ONE) \<sqsubseteq> (if y = \<bottom> then \<bottom> else ONE)" by auto
qed

definition defd :: "'v::flat \<rightarrow> one" where
  "defd = (\<Lambda> v. if v = \<bottom> then \<bottom> else ONE)"

lemma defd_beta: "defd\<cdot>v = (if v = \<bottom> then \<bottom> else ONE)"
  unfolding defd_def by (simp add: cont_defd)

locale flat_eval = dim_eval deval
  for deval :: "'d \<Rightarrow> ('r::pcpo \<rightarrow> 'v::flat)" (\<open>\<lbrakk>_\<rbrakk>\<close>)
begin

definition defined :: "'d set \<Rightarrow> 'r \<rightarrow> one" where
  "defined D = (\<Lambda> r. if (\<forall>d\<in>D. \<lbrakk>d\<rbrakk>\<cdot>r \<noteq> \<bottom>) then ONE else \<bottom>)"

lemma cont_defined: "finite D \<Longrightarrow> cont (\<lambda>r. if (\<forall>d\<in>D. \<lbrakk>d\<rbrakk>\<cdot>r \<noteq> \<bottom>) then ONE else \<bottom>)"
proof (induct rule: finite_induct)
  case empty then show ?case by simp
next
  case (insert d D)
  have "(\<lambda>r. if \<forall>x\<in>insert d D. \<lbrakk>x\<rbrakk>\<cdot>r \<noteq> \<bottom> then ONE else \<bottom>)
      = (\<lambda>r. seq\<cdot>(defd\<cdot>(\<lbrakk>d\<rbrakk>\<cdot>r))\<cdot>(if \<forall>x\<in>D. \<lbrakk>x\<rbrakk>\<cdot>r \<noteq> \<bottom> then ONE else \<bottom>))"
    by (auto simp: fun_eq_iff defd_beta seq_conv_if)
  with insert.hyps(3) show ?case by simp
qed

lemma selected_defined: "finite D \<Longrightarrow> selected (defined D) = {r. \<forall>d\<in>D. \<lbrakk>d\<rbrakk>\<cdot>r \<noteq> \<bottom>}"
  by (simp add: selected_def defined_def cont_defined)

lemma keyof_defined_maximal:
  assumes "\<forall>d\<in>D. \<lbrakk>d\<rbrakk>\<cdot>x \<noteq> \<bottom>" and "keyof D\<cdot>x \<sqsubseteq> keyof D\<cdot>y"
  shows "keyof D\<cdot>x = keyof D\<cdot>y"
proof (rule tuple_eqI)
  fix d
  from assms(2) have "(keyof D\<cdot>x)\<langle>d\<rangle> \<sqsubseteq> (keyof D\<cdot>y)\<langle>d\<rangle>"
    by (simp add: below_tuple_def fun_below_iff)
  with assms(1) show "(keyof D\<cdot>x)\<langle>d\<rangle> = (keyof D\<cdot>y)\<langle>d\<rangle>"
    by (auto simp: keyof_tget split: if_splits dest: ax_flat)
qed

lemma keyof_defined_dims: "\<forall>d\<in>D. \<lbrakk>d\<rbrakk>\<cdot>x \<noteq> \<bottom> \<Longrightarrow> (keyof D\<cdot>x)\<langle>d\<rangle> \<noteq> \<bottom> \<longleftrightarrow> d \<in> D"
  by (simp add: keyof_tget)

end

section \<open>Frame semantics\<close>

text \<open>\<^term>\<open>spin K\<close> is the slice pinning the key \<^term>\<open>K\<close>: on keys, the principal upset of
  \<^term>\<open>K\<close>, which is open exactly when \<^term>\<open>K\<close> is compact, with support \<^term>\<open>tsupp K\<close>.
  Pins coarsen by cutting the key, and compatible pins conjoin to the pin of the join.\<close>


locale frame_sem = flat_eval deval + slicer conj sunit ssel sdims coarsen
  for deval :: "'d \<Rightarrow> ('r::pcpo \<rightarrow> 'v::flat)" (\<open>\<lbrakk>_\<rbrakk>\<close>)
    and conj :: "'f \<Rightarrow> 'f \<Rightarrow> 'f" (infixl \<open>\<^bold>*\<close> 70) and sunit :: 'f (\<open>\<^bold>1\<close>)
    and ssel :: "'f \<Rightarrow> ('d, 'v) tuple sel" and sdims coarsen +
  fixes spin :: "('d, 'v) tuple \<Rightarrow> 'f"
  assumes ssel_spin: "compact K \<Longrightarrow> sel_rows (ssel (spin K)) = {t. K \<sqsubseteq> t}"
    and sdims_spin: "compact K \<Longrightarrow> sdims (spin K) \<subseteq> tsupp K"
    and coarsen_spin: "coarsen A (spin K) = spin (tcut A\<cdot>K)"
    and spin_join: "K1 \<Up> K2 \<Longrightarrow> spin (K1 \<squnion> K2) = spin K1 \<^bold>* spin K2"
begin

text \<open>A row's full key, and the rows a frame selects: those in the ambient filter whose key is
  in the slice.\<close>

definition rkey :: "'r \<Rightarrow> ('d, 'v) tuple" where
  "rkey r = keyof UNIV\<cdot>r"

definition frows :: "('d, 'f, 'r) frame \<Rightarrow> 'r set" where
  "frows F = sel_rows (amb F) \<inter> {r. rkey r \<in> sel_rows (ssel (slice F))}"

lemma pin_rkey: "K \<sqsubseteq> rkey r \<longleftrightarrow> K \<sqsubseteq> keyof (tsupp K)\<cdot>r"
  by (auto simp: rkey_def below_tuple_def fun_below_iff keyof_tget tsupp_def)

definition grp :: "('d, 'f, 'r) frame \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> bool" where
  "grp F x y \<longleftrightarrow> x \<in> frows F \<and> y \<in> frows F \<and> keyof (dims F)\<cdot>x = keyof (dims F)\<cdot>y"

lemma grp_iff_kern:
  "grp F x y \<longleftrightarrow> x \<in> frows F \<and> y \<in> frows F \<and> kern (dims F) x y \<and> kern (dims F) y x"
  unfolding grp_def kern_def by (auto intro: below_antisym)

lemma grp_sym: "grp F x y \<Longrightarrow> grp F y x"
  unfolding grp_def by simp

lemma grp_trans: "grp F x y \<Longrightarrow> grp F y z \<Longrightarrow> grp F x z"
  unfolding grp_def by simp

lemma grp_refl: "x \<in> frows F \<Longrightarrow> grp F x x"
  unfolding grp_def by simp

lemma grp_fdep:
  assumes "fdep (frows F) D (dims F)" and "grp F x y"
  shows "keyof D\<cdot>x = keyof D\<cdot>y"
  using assms unfolding grp_iff_kern fdep_def kern_def by (blast intro: below_antisym)

text \<open>The rows a frame groups under at key dimensions \<^term>\<open>D\<close>: its own, defined on
  \<^term>\<open>D\<close>.\<close>

definition gfilt where
  "gfilt F D = frows F \<inter> {r. \<forall>d\<in>fset D. \<lbrakk>d\<rbrakk>\<cdot>r \<noteq> \<bottom>}"

lemma grouped_keys_maximal:
  assumes "dataset S"
    and "x \<in> pts (filtered S (gfilt F D))" and "keyof (fset D)\<cdot>x \<sqsubseteq> keyof (fset D)\<cdot>y"
  shows "keyof (fset D)\<cdot>x = keyof (fset D)\<cdot>y"
  using assms by (auto simp: dataset.pts_filtered gfilt_def intro: keyof_defined_maximal)

end

section \<open>Frame transformers\<close>

text \<open>The level-of-detail constructs act on the frame an inner expression is evaluated under.
  \<open>INCLUDE D\<close> adds dimensions; \<open>GROUP BY ONLY D\<close> replaces them by \<open>D\<close> and coarsens the slice
  to \<open>D\<close> (\<open>TOTAL\<close> is \<open>GROUP BY ONLY \<emptyset>\<close>); \<open>ISOLATE\<close> evaluates under the empty frame, with
  neither filter; \<open>E FOR W G\<close> (e.g.\ \<open>E FOR Y = Z AND ALL(W)\<close>) drops the dimensions \<open>W\<close>,
  coarsens the slice away from them, and conjoins \<open>G\<close> (whose support should lie in \<open>W\<close>);
  \<open>EXCLUDE W\<close> is \<open>FOR W \<top>\<close>; \<open>RESTRICT \<phi>\<close> adds \<open>\<phi>\<close> to the ambient filter.\<close>

definition finclude :: "'d::type fset \<Rightarrow> ('d, 'f::type, 'r::pcpo) frame \<Rightarrow> ('d, 'f, 'r) frame" where
  "finclude D F = F\<lparr>fdims := fdims F |\<union>| D\<rparr>"

lemma dims_finclude [simp]: "dims (finclude D F) = dims F \<union> fset D"
  by (simp add: dims_def finclude_def)

lemma fdims_finclude [simp]: "fdims (finclude D F) = fdims F |\<union>| D"
  by (simp add: finclude_def)

lemma amb_finclude [simp]: "amb (finclude D F) = amb F"
  by (simp add: finclude_def)

lemma slice_finclude [simp]: "slice (finclude D F) = slice F"
  by (simp add: finclude_def)

definition frestrict :: "'r::pcpo sel \<Rightarrow> ('d::type, 'f::type, 'r) frame \<Rightarrow> ('d, 'f, 'r) frame" where
  "frestrict \<phi> F = F\<lparr>amb := inf (amb F) \<phi>\<rparr>"

lemma fdims_frestrict [simp]: "fdims (frestrict \<phi> F) = fdims F"
  by (simp add: frestrict_def)

lemma slice_frestrict [simp]: "slice (frestrict \<phi> F) = slice F"
  by (simp add: frestrict_def)

lemma amb_frestrict [simp]: "amb (frestrict \<phi> F) = inf (amb F) \<phi>"
  by (simp add: frestrict_def)

context frame_sem
begin

definition fgroupby :: "'d fset \<Rightarrow> ('d, 'f, 'r) frame \<Rightarrow> ('d, 'f, 'r) frame" where
  "fgroupby D F = F\<lparr>fdims := D, slice := coarsen (fset D) (slice F)\<rparr>"

definition fisolate :: "('d, 'f, 'r) frame \<Rightarrow> ('d, 'f, 'r) frame" where
  "fisolate F = \<lparr>fdims = {||}, amb = top, slice = \<^bold>1\<rparr>"

definition ffor :: "'d fset \<Rightarrow> 'f \<Rightarrow> ('d, 'f, 'r) frame \<Rightarrow> ('d, 'f, 'r) frame" where
  "ffor W G F = F\<lparr>fdims := fdims F |-| W, slice := coarsen (- fset W) (slice F) \<^bold>* G\<rparr>"

definition peg :: "('d, 'v) tuple \<Rightarrow> ('d, 'f, 'r) frame \<Rightarrow> ('d, 'f, 'r) frame" where
  "peg K F = F\<lparr>slice := slice F \<^bold>* spin K\<rparr>"

lemma fdims_peg [simp]: "fdims (peg K F) = fdims F"
  by (simp add: peg_def)

lemma dims_peg [simp]: "dims (peg K F) = dims F"
  by (simp add: dims_def)

lemma frows_finclude [simp]: "frows (finclude D F) = frows F"
  by (simp add: frows_def)

lemma frows_frestrict: "frows (frestrict \<phi> F) = frows F \<inter> sel_rows \<phi>"
  by (auto simp: frows_def inf_sel.rep_eq)

lemma frows_peg_sub: "frows (peg K F) \<subseteq> frows F"
  by (auto simp: frows_def peg_def ssel.hom_f inf_sel.rep_eq)

lemma frows_peg:
  "compact K \<Longrightarrow> frows (peg K F) = frows F \<inter> {r. K \<sqsubseteq> keyof (tsupp K)\<cdot>r}"
  by (auto simp: frows_def peg_def ssel.hom_f inf_sel.rep_eq ssel_spin
      pin_rkey)

text \<open>Pegging commutes with the transformers, up to cutting the key to what survives.\<close>

lemma peg_finclude: "peg K (finclude D F) = finclude D (peg K F)"
  by (simp add: peg_def finclude_def)

lemma peg_frestrict: "peg K (frestrict \<phi> F) = frestrict \<phi> (peg K F)"
  by (simp add: peg_def frestrict_def)

lemma fgroupby_peg: "fgroupby D (peg K F) = peg (tcut (fset D)\<cdot>K) (fgroupby D F)"
  by (simp add: fgroupby_def peg_def coarsen_conj coarsen_spin)

lemma fisolate_peg: "fisolate (peg K F) = fisolate F"
  by (simp add: fisolate_def)

lemma ffor_peg: "ffor W G (peg K F) = peg (tcut (- fset W)\<cdot>K) (ffor W G F)"
  by (simp add: ffor_def peg_def coarsen_conj coarsen_spin conj.assoc conj.commute conj.left_commute)

text \<open>Pegging to a key, then to a finer one, is pegging to the finer one.\<close>

lemma peg_peg_below:
  assumes "K' \<sqsubseteq> K"
  shows "peg K (peg K' F) = peg K F"
proof -
  have j: "spin K' \<^bold>* spin K = spin K"
    using spin_join[OF joinableI[OF assms below_refl]] join_absorbI[OF assms] by simp
  show ?thesis by (simp add: peg_def conj.assoc j)
qed

end

section \<open>Pins and key images\<close>

text \<open>Every construct's result table is keyed by the key images of the data points the frame
  groups, at the expression's key dimensions.  Since grouping drops points undefined on the key
  dimensions, keys are exactly such images (no partial keys).\<close>

context frame_sem
begin

definition keyimg where
  "keyimg S F D = (\<lambda>m. keyof (fset D)\<cdot>m) ` pts (filtered S (gfilt F D))"

text \<open>A frame \<^emph>\<open>pins\<close> a key when its slice syntactically entails the key's pin; \<open>peg\<close> is the
  canonical way.  (Pinning is syntactic so that it survives coarsening: a slice may pin a
  dimension semantically through a condition that coarsening away another dimension loses.)\<close>

definition pins where
  "pins F K \<longleftrightarrow> compact K \<and> slice F \<^bold>\<le> spin K"

lemma pins_peg: "compact K \<Longrightarrow> pins (peg K F) K"
  by (simp add: pins_def peg_def)

lemma frows_pinned:
  assumes "pins F K" "r \<in> frows F"
  shows "K \<sqsubseteq> keyof (tsupp K)\<cdot>r"
proof -
  from assms(1) have "ssel (slice F) \<le> ssel (spin K)" and fin: "compact K"
    by (auto simp: pins_def intro: ssel_mono)
  with assms(2) have "rkey r \<in> {t. K \<sqsubseteq> t}"
    by (auto simp: frows_def less_eq_sel.rep_eq ssel_spin[OF fin])
  then show ?thesis by (simp add: pin_rkey)
qed

lemma keyimg_cong: "frows F = frows F' \<Longrightarrow> keyimg S F D = keyimg S F' D"
  by (simp add: keyimg_def gfilt_def)

lemma keyimg_mono: "dataset S \<Longrightarrow> frows F \<subseteq> frows F' \<Longrightarrow> keyimg S F D \<subseteq> keyimg S F' D"
  by (auto simp: keyimg_def dataset.pts_filtered gfilt_def)

lemma keyimg_at:
  assumes "dataset S" "m \<in> pts S" "m \<in> frows F" "\<forall>d\<in>fset D. \<lbrakk>d\<rbrakk>\<cdot>m \<noteq> \<bottom>"
  shows "keyof (fset D)\<cdot>m \<in> keyimg S F D"
  using assms by (auto simp: keyimg_def dataset.pts_filtered gfilt_def)

text \<open>Keys carry their own dimensions.\<close>

lemma keyimg_tsupp:
  assumes "dataset S" "K \<in> keyimg S F D"
  shows "tsupp K = fset D"
proof -
  from assms(2) obtain m where K: "K = keyof (fset D)\<cdot>m" and m: "m \<in> pts (filtered S (gfilt F D))"
    by (auto simp: keyimg_def)
  then have "\<forall>d\<in>fset D. \<lbrakk>d\<rbrakk>\<cdot>m \<noteq> \<bottom>"
    by (auto simp: dataset.pts_filtered[OF assms(1)] gfilt_def)
  then show ?thesis by (auto simp: tsupp_def K keyof_tget)
qed

lemma keyimg_antichain:
  assumes "dataset S" "k \<in> keyimg S F D" "k' \<in> keyimg S F D" "k \<sqsubseteq> k'"
  shows "k = k'"
  using assms by (auto simp: keyimg_def dataset.pts_filtered gfilt_def intro: keyof_defined_maximal)

text \<open>Coarser key dimensions see every truncation of a finer key.\<close>

lemma keyimg_trunc:
  assumes "dataset S" "D1 |\<subseteq>| D2" "k \<in> keyimg S F D2"
  shows "tcut (fset D1)\<cdot>k \<in> keyimg S F D1"
proof -
  from assms(3) obtain m where k: "k = keyof (fset D2)\<cdot>m" and m: "m \<in> pts (filtered S (gfilt F D2))"
    by (auto simp: keyimg_def)
  from m assms(2) have "m \<in> pts (filtered S (gfilt F D1))"
    by (auto simp: dataset.pts_filtered[OF assms(1)] gfilt_def less_eq_fset.rep_eq)
  moreover from assms(2) have "tcut (fset D1)\<cdot>k = keyof (fset D1)\<cdot>m"
    by (simp add: k tcut_keyof less_eq_fset.rep_eq Int_absorb1)
  ultimately show ?thesis by (auto simp: keyimg_def)
qed

text \<open>A pinned key is matched exactly on its own dimensions (flat values).\<close>

lemma pin_eq: "K \<sqsubseteq> keyof (tsupp K)\<cdot>m \<Longrightarrow> K = keyof (tsupp K)\<cdot>m"
proof (rule tuple_eqI)
  fix d assume "K \<sqsubseteq> keyof (tsupp K)\<cdot>m"
  then have "K\<langle>d\<rangle> \<sqsubseteq> (keyof (tsupp K)\<cdot>m)\<langle>d\<rangle>" by (simp add: below_tuple_def fun_below_iff)
  then show "K\<langle>d\<rangle> = (keyof (tsupp K)\<cdot>m)\<langle>d\<rangle>"
    by (cases "d \<in> tsupp K") (auto simp: keyof_tget tsupp_def dest: ax_flat)
qed

text \<open>A key of a frame pinning \<^term>\<open>K\<close> comes from a data point on which \<^term>\<open>K\<close> is a key
  as well.\<close>

lemma pinned_witness:
  assumes "dataset S" "pins F K" "K1 \<in> keyimg S F D"
  obtains m where "m \<in> pts S" "m \<in> frows F" "\<forall>d\<in>fset D \<union> tsupp K. \<lbrakk>d\<rbrakk>\<cdot>m \<noteq> \<bottom>"
    "K1 = keyof (fset D)\<cdot>m" "K = keyof (tsupp K)\<cdot>m"
proof -
  from assms(3) obtain m where K1: "K1 = keyof (fset D)\<cdot>m" and m: "m \<in> pts S" "m \<in> frows F"
      and dD: "\<forall>d\<in>fset D. \<lbrakk>d\<rbrakk>\<cdot>m \<noteq> \<bottom>"
    by (auto simp: keyimg_def dataset.pts_filtered[OF assms(1)] gfilt_def)
  have K: "K = keyof (tsupp K)\<cdot>m" using frows_pinned[OF assms(2) m(2)] by (rule pin_eq)
  then have "tsupp (keyof (tsupp K)\<cdot>m) = tsupp K" by simp
  then have "\<forall>d\<in>tsupp K. \<lbrakk>d\<rbrakk>\<cdot>m \<noteq> \<bottom>" by (auto simp: tsupp_keyof)
  with dD have "\<forall>d\<in>fset D \<union> tsupp K. \<lbrakk>d\<rbrakk>\<cdot>m \<noteq> \<bottom>" by blast
  then show ?thesis using that m K1 K by blast
qed

text \<open>In a frame pinning \<^term>\<open>K\<close>, every key (at any key dimensions) is compatible with
  \<^term>\<open>K\<close>, and their join is the data point's key on both dimension sets together.\<close>

lemma pinned_compat:
  assumes "dataset S" "pins F K" "K1 \<in> keyimg S F D"
  shows "K1 \<Up> K" "tcut (fset D)\<cdot>(K1 \<squnion> K) = K1" "tcut (tsupp K)\<cdot>(K1 \<squnion> K) = K"
proof -
  obtain m where "K1 = keyof (fset D)\<cdot>m" "K = keyof (tsupp K)\<cdot>m"
    using pinned_witness[OF assms] by blast
  moreover define T where "T = tsupp K"
  ultimately have K1: "K1 = keyof (fset D)\<cdot>m" and K: "K = keyof T\<cdot>m" by simp_all
  define t where "t = Abs_tuple (\<lambda>d. \<lbrakk>d\<rbrakk>\<cdot>m)"
  have K1t: "K1 = tcut (fset D)\<cdot>t" and Kt: "K = tcut T\<cdot>t"
    using K1 K by (simp_all add: t_def keyof_beta)
  have j: "K1 \<squnion> K = tcut (fset D \<union> T)\<cdot>t"
    unfolding K1t Kt by (rule tcut_join)
  show "K1 \<Up> K" unfolding K1t Kt by (rule tcut_joinable)
  show "tcut (fset D)\<cdot>(K1 \<squnion> K) = K1"
    unfolding j by (simp add: K1t tcut_compose)
  show "tcut (tsupp K)\<cdot>(K1 \<squnion> K) = K"
    unfolding T_def[symmetric] j by (simp add: Kt tcut_compose)
qed

text \<open>A frame pinning a key with dimensions \<^term>\<open>D2\<close> has, at any coarser key dimensions
  \<^term>\<open>D1\<close>, at most the truncation of that key.\<close>

lemma keyimg_pinned:
  assumes "dataset S" "pins F K" "tsupp K = fset D2" "D1 |\<subseteq>| D2"
  shows "keyimg S F D1 \<subseteq> {tcut (fset D1)\<cdot>K}"
proof
  fix k assume "k \<in> keyimg S F D1"
  then obtain m where k: "k = keyof (fset D1)\<cdot>m" and mF: "m \<in> frows F"
    by (auto simp: keyimg_def dataset.pts_filtered[OF assms(1)] gfilt_def)
  have "K \<sqsubseteq> keyof (tsupp K)\<cdot>m" using frows_pinned[OF assms(2) mF] .
  then have "K = keyof (fset D2)\<cdot>m" using pin_eq assms(3) by metis
  then have "tcut (fset D1)\<cdot>K = keyof (fset D1)\<cdot>m"
    using assms(4) by (simp add: tcut_keyof less_eq_fset.rep_eq Int_absorb1)
  with k show "k \<in> {tcut (fset D1)\<cdot>K}" by simp
qed

text \<open>Pegging a frame to one of its keys leaves exactly that key.\<close>

lemma keyimg_peg:
  assumes "dataset S" "K \<in> keyimg S F D"
  shows "keyimg S (peg K F) D = {K}"
proof
  have ts: "tsupp K = fset D" by (rule keyimg_tsupp[OF assms])
  then have fin: "compact K" by (intro compact_tsupp) simp
  from assms(2) obtain m where K: "K = keyof (fset D)\<cdot>m" and m: "m \<in> pts (filtered S (gfilt F D))"
    by (auto simp: keyimg_def)
  have "tcut (fset D)\<cdot>K = K" by (simp add: K tcut_keyof)
  then show "keyimg S (peg K F) D \<subseteq> {K}"
    using keyimg_pinned[OF assms(1) pins_peg[OF fin] ts order_refl] by simp
  from m have mS: "m \<in> pts S" "m \<in> frows F" "\<forall>d\<in>fset D. \<lbrakk>d\<rbrakk>\<cdot>m \<noteq> \<bottom>"
    by (auto simp: dataset.pts_filtered[OF assms(1)] gfilt_def)
  have "K \<sqsubseteq> keyof (tsupp K)\<cdot>m" by (simp add: ts K[symmetric])
  with mS(2) have "m \<in> frows (peg K F)" by (simp add: frows_peg[OF fin])
  then have "keyof (fset D)\<cdot>m \<in> keyimg S (peg K F) D"
    by (rule keyimg_at[OF assms(1) mS(1) _ mS(3)])
  then show "{K} \<subseteq> keyimg S (peg K F) D" using K by simp
qed

lemma keyimg_peg_iff: "dataset S \<Longrightarrow> K \<in> keyimg S (peg K F) D \<longleftrightarrow> K \<in> keyimg S F D"
  using keyimg_mono[OF _ frows_peg_sub] keyimg_peg by blast

end

section \<open>Laws for an abstract semantics\<close>

text \<open>A fixed expression has dimension sets \<^term>\<open>mind\<close> \<open>\<subseteq>\<close> \<^term>\<open>maxd\<close> and a semantics:
  a map from frames and keys to values, with \<^term>\<open>\<bottom>\<close> for ``no entry'' (a group always has a
  non-\<^term>\<open>\<bottom>\<close> value).  The laws pin down each table's dimensions without storing them: the
  \<^emph>\<open>key law\<close> says that keys are key images at the expression's key dimensions; the \<^emph>\<open>peg law\<close>
  says that pegging the frame to a key does not change the value there (it only removes
  rows of other keys); the \<^emph>\<open>dims law\<close> says that in frames pinning a key \<^term>\<open>K\<close>, varying
  the dimensions along \<^term>\<open>K\<close>'s moves each entry to the corresponding key (the truncated
  join with \<^term>\<open>K\<close>) without changing its value; the \<^emph>\<open>effective-dimensions law\<close> says that
  the semantics depends on a frame's dimensions only through the key dimensions they induce.
  The slice is compared syntactically (up to the lattice laws), since coarsening is not
  extensional.  Combinators such as \<open>INCLUDE\<close> are then maps from lawful semantics to lawful
  semantics.\<close>

text \<open>A \<^emph>\<open>dataspace\<close>: frame semantics together with the dataset frames range over.\<close>

locale dataspace = frame_sem deval conj sunit ssel sdims coarsen spin
  for deval :: "'d \<Rightarrow> ('r::pcpo \<rightarrow> 'v::flat)" (\<open>\<lbrakk>_\<rbrakk>\<close>)
    and conj :: "'f \<Rightarrow> 'f \<Rightarrow> 'f" (infixl \<open>\<^bold>*\<close> 70) and sunit :: 'f (\<open>\<^bold>1\<close>)
    and ssel :: "'f \<Rightarrow> ('d, 'v) tuple sel" and sdims coarsen spin +
  fixes S :: "'r set"
  assumes dataset_S: "dataset S"

locale expr_sem = dataspace +
  fixes mind maxd sem
  assumes mind_maxd: "mind |\<subseteq>| maxd"
    and key_law: "sem F k \<noteq> \<bottom> \<Longrightarrow> k \<in> keyimg S F ((mind |\<union>| fdims F) |\<inter>| maxd)"
    and peg_law: "sem (peg K F) K = sem F K"
    and dims_law: "\<lbrakk>amb F = amb F'; slice F = slice F'; pins F K;
                    dims F - tsupp K = dims F' - tsupp K; sem F K1 \<noteq> \<bottom>\<rbrakk>
                   \<Longrightarrow> sem F' (tcut (fset ((mind |\<union>| fdims F') |\<inter>| maxd))\<cdot>(K1 \<squnion> K)) = sem F K1"
    and eff_law: "\<lbrakk>amb F = amb F'; slice F = slice F';
                   (mind |\<union>| fdims F) |\<inter>| maxd = (mind |\<union>| fdims F') |\<inter>| maxd\<rbrakk>
                  \<Longrightarrow> sem F = sem F'"
begin

text \<open>The key dimensions under a frame: what the expression decides itself, plus what of the
  frame it can be evaluated up to.  (Row-level and \<open>FIXED\<close> expressions have \<open>mind = maxd\<close> and
  ignore the frame; a plain aggregate has \<open>mind = \<emptyset>\<close>.)\<close>

abbreviation "kd F \<equiv> (mind |\<union>| fdims F) |\<inter>| maxd"

text \<open>The compatibility the dims law relies on is automatic.\<close>

lemma pinned_entry_compat: "pins F K \<Longrightarrow> sem F K1 \<noteq> \<bottom> \<Longrightarrow> K1 \<Up> K"
  by (rule pinned_compat(1)[OF dataset_S _ key_law])

text \<open>Pegging to a coarser key does not change the value either.\<close>

lemma peg_below: "K' \<sqsubseteq> K \<Longrightarrow> sem (peg K' F) K = sem F K"
  by (metis peg_law peg_peg_below)

text \<open>Pegging to a key with the expression's key dimensions leaves at most that key; the
  assumption cannot be dropped (pegging to the empty key changes nothing).\<close>

theorem strong_peg:
  assumes "tsupp K = fset (kd F)"
  shows "sem (peg K F) k = (if k = K then sem F K else \<bottom>)"
proof (cases "k = K")
  case True then show ?thesis by (simp add: peg_law)
next
  case False
  have KK: "tcut (fset (kd F))\<cdot>K = K"
    using tcut_tsupp[of K] by (simp add: assms)
  have fin: "compact K" by (intro compact_tsupp) (simp add: assms)
  show ?thesis
  proof (rule ccontr)
    assume "sem (peg K F) k \<noteq> (if k = K then sem F K else \<bottom>)"
    with False have "sem (peg K F) k \<noteq> \<bottom>" by simp
    then have "k \<in> keyimg S (peg K F) (kd F)" using key_law by fastforce
    with keyimg_pinned[OF dataset_S pins_peg[OF fin] assms order_refl] KK False show False
      by auto
  qed
qed

text \<open>Values at different levels of detail: the value at a finer key is the value at its
  truncation, once the finer key is pinned by the filter.  The finer frame is first trimmed
  to dimensions the expression can see (effective-dimensions law), so that the extra
  dimensions lie within the finer key's; then the dims law moves the entry.\<close>

theorem lod_shift:
  assumes "amb F1 = amb F2" "slice F1 = slice F2" "dims F1 \<subseteq> dims F2" "sem F2 K2 \<noteq> \<bottom>"
  shows "sem (peg K2 F1) k = (if k = tcut (fset (kd F1))\<cdot>K2 then sem F2 K2 else \<bottom>)"
proof -
  define F2' where "F2' = F2\<lparr>fdims := fdims F1 |\<union>| (fdims F2 |\<inter>| maxd)\<rparr>"
  let ?k = "tcut (fset (kd F1))\<cdot>K2"
  have d1: "fset (fdims F1) \<subseteq> fset (fdims F2)" using assms(3) by (simp add: dims_def)
  have "kd F2' = kd F2" using d1 by (auto simp: F2'_def)
  then have same: "sem F2' = sem F2" by (intro eff_law) (simp_all add: F2'_def)
  have nb: "sem F2' K2 \<noteq> \<bottom>" using assms(4) same by simp
  have Kin: "K2 \<in> keyimg S F2' (kd F2')" by (rule key_law[OF nb])
  have ts: "tsupp K2 = fset (kd F2')" by (rule keyimg_tsupp[OF dataset_S Kin])
  then have fin: "compact K2" by (intro compact_tsupp) simp
  have sp: "sem (peg K2 F2') K2 = sem F2 K2" using peg_law same by simp
  have f1: "amb (peg K2 F2') = amb (peg K2 F1)" "slice (peg K2 F2') = slice (peg K2 F1)"
    by (simp_all add: peg_def F2'_def assms(1,2))
  have f2: "dims (peg K2 F2') - tsupp K2 = dims (peg K2 F1) - tsupp K2"
    by (auto simp: ts dims_def F2'_def)
  have f3: "sem (peg K2 F2') K2 \<noteq> \<bottom>" using assms(4) sp by simp
  have v: "sem (peg K2 F1) ?k = sem F2 K2"
    using dims_law[OF f1 pins_peg[OF fin] f2 f3] by (simp add: sp)
  have sub: "kd F1 |\<subseteq>| kd F2'" by (auto simp: F2'_def)
  show ?thesis
  proof (cases "k = ?k")
    case True with v show ?thesis by simp
  next
    case False
    show ?thesis
    proof (rule ccontr)
      assume "sem (peg K2 F1) k \<noteq> (if k = ?k then sem F2 K2 else \<bottom>)"
      with False have "sem (peg K2 F1) k \<noteq> \<bottom>" by simp
      then have "k \<in> keyimg S (peg K2 F1) (kd F1)" using key_law by fastforce
      with keyimg_pinned[OF dataset_S pins_peg[OF fin] ts sub] False show False by auto
    qed
  qed
qed

end

text \<open>Within a dataspace, a semantics is \<^emph>\<open>lawful\<close> when it forms an \<^locale>\<open>expr_sem\<close>
  instance; combinators are then plain theorems concluding lawfulness.\<close>

context dataspace
begin

abbreviation lawful where "lawful \<equiv> expr_sem deval conj sunit ssel sdims coarsen spin S"

lemma lawfulI:
  assumes "mind |\<subseteq>| maxd"
    and "\<And>F k. sem F k \<noteq> \<bottom> \<Longrightarrow> k \<in> keyimg S F ((mind |\<union>| fdims F) |\<inter>| maxd)"
    and "\<And>F K. sem (peg K F) K = sem F K"
    and "\<And>F F' K K1. \<lbrakk>amb F = amb F'; slice F = slice F'; pins F K;
                      dims F - tsupp K = dims F' - tsupp K; sem F K1 \<noteq> \<bottom>\<rbrakk>
                     \<Longrightarrow> sem F' (tcut (fset ((mind |\<union>| fdims F') |\<inter>| maxd))\<cdot>(K1 \<squnion> K)) = sem F K1"
    and "\<And>F F'. \<lbrakk>amb F = amb F'; slice F = slice F';
                 (mind |\<union>| fdims F) |\<inter>| maxd = (mind |\<union>| fdims F') |\<inter>| maxd\<rbrakk>
                 \<Longrightarrow> sem F = sem F'"
  shows "lawful mind maxd sem"
  by (intro expr_sem.intro dataspace_axioms expr_sem_axioms.intro) (fact assms)+

lemma frows_cong: "amb F = amb F' \<Longrightarrow> slice F = slice F' \<Longrightarrow> frows F = frows F'"
  by (simp add: frows_def)

end

section \<open>Combinators\<close>

subsection \<open>\<open>INCLUDE\<close>\<close>

definition group_by where
  "group_by D sem = (\<lambda>F. sem (finclude D F))"

theorem (in expr_sem) lawful_group_by:
  "lawful (mind |\<union>| (D |\<inter>| maxd)) maxd (group_by D sem)"
proof (rule lawfulI)
  have kd: "\<And>F. (mind |\<union>| (fdims F |\<union>| D)) |\<inter>| maxd = (mind |\<union>| (D |\<inter>| maxd) |\<union>| fdims F) |\<inter>| maxd"
    by auto
  show "mind |\<union>| (D |\<inter>| maxd) |\<subseteq>| maxd" using mind_maxd by auto
  show "group_by D sem F k \<noteq> \<bottom> \<Longrightarrow>
        k \<in> keyimg S F ((mind |\<union>| (D |\<inter>| maxd) |\<union>| fdims F) |\<inter>| maxd)" for F k
    using key_law[of "finclude D F" k] keyimg_cong[of "finclude D F" F S]
    by (simp add: group_by_def kd)
  show "group_by D sem (peg K F) K = group_by D sem F K" for F K
    by (simp add: group_by_def peg_finclude[symmetric] peg_law)
  show "group_by D sem F' (tcut (fset ((mind |\<union>| (D |\<inter>| maxd) |\<union>| fdims F') |\<inter>| maxd))\<cdot>(K1 \<squnion> K))
          = group_by D sem F K1"
    if "amb F = amb F'" "slice F = slice F'" "pins F K" "dims F - tsupp K = dims F' - tsupp K"
       "group_by D sem F K1 \<noteq> \<bottom>" for F F' K K1
  proof -
    have "pins (finclude D F) K" using that(3) by (simp add: pins_def)
    moreover have "dims (finclude D F) - tsupp K = dims (finclude D F') - tsupp K"
      using that(4) by auto
    ultimately show ?thesis
      using dims_law[of "finclude D F" "finclude D F'" K K1] that(1,2,5)
      by (simp add: group_by_def kd)
  qed
  show "group_by D sem F = group_by D sem F'"
    if "amb F = amb F'" "slice F = slice F'"
       "(mind |\<union>| (D |\<inter>| maxd) |\<union>| fdims F) |\<inter>| maxd = (mind |\<union>| (D |\<inter>| maxd) |\<union>| fdims F') |\<inter>| maxd"
    for F F'
  proof -
    have "sem (finclude D F) = sem (finclude D F')"
      by (rule eff_law) (use that in \<open>simp_all add: kd\<close>)
    then show ?thesis by (simp add: group_by_def)
  qed
qed

subsection \<open>Fixed-level constructs: \<open>GROUP BY ONLY\<close>, \<open>TOTAL\<close>, \<open>ISOLATE\<close>\<close>

text \<open>A construct that evaluates its argument under a transformed frame at fixed key dimensions
  \<^term>\<open>E\<close>, restricted back to the incoming frame's keys.  It is lawful whenever the
  transformer sees the incoming frame only through its filters, and pegging the incoming frame
  does not change the inner value at the key.  This needs nothing of the inner semantics.\<close>

context dataspace
begin

definition fixed where
  "fixed E T sem F k = (if k \<in> keyimg S F E then sem (T F) k else \<bottom>)"

theorem lawful_fixed:
  assumes "\<And>F K. sem (T (peg K F)) K = sem (T F) K"
    and "\<And>F F'. amb F = amb F' \<Longrightarrow> slice F = slice F' \<Longrightarrow> T F = T F'"
  shows "lawful E E (fixed E T sem)"
proof (rule lawfulI)
  have E: "\<And>X. (E |\<union>| X) |\<inter>| E = E" by auto
  show "E |\<subseteq>| E" by simp
  show "fixed E T sem F k \<noteq> \<bottom> \<Longrightarrow> k \<in> keyimg S F ((E |\<union>| fdims F) |\<inter>| E)" for F k
    by (auto simp: fixed_def E split: if_splits)
  show "fixed E T sem (peg K F) K = fixed E T sem F K" for F K
    by (simp add: fixed_def keyimg_peg_iff[OF dataset_S] assms(1))
  show "fixed E T sem F' (tcut (fset ((E |\<union>| fdims F') |\<inter>| E))\<cdot>(K1 \<squnion> K)) = fixed E T sem F K1"
    if "amb F = amb F'" "slice F = slice F'" "pins F K" "dims F - tsupp K = dims F' - tsupp K"
       "fixed E T sem F K1 \<noteq> \<bottom>" for F F' K K1
  proof -
    have K1: "K1 \<in> keyimg S F E" using that(5) by (auto simp: fixed_def split: if_splits)
    have "tcut (fset E)\<cdot>(K1 \<squnion> K) = K1" by (rule pinned_compat(2)[OF dataset_S that(3) K1])
    moreover have "keyimg S F' E = keyimg S F E"
      using keyimg_cong[OF frows_cong[OF that(1,2)]] by simp
    moreover have "T F' = T F" using assms(2)[OF that(1,2)] by simp
    ultimately show ?thesis by (simp add: fixed_def E)
  qed
  show "fixed E T sem F = fixed E T sem F'"
    if "amb F = amb F'" "slice F = slice F'" "(E |\<union>| fdims F) |\<inter>| E = (E |\<union>| fdims F') |\<inter>| E"
    for F F'
  proof -
    have "keyimg S F E = keyimg S F' E" by (rule keyimg_cong[OF frows_cong[OF that(1,2)]])
    then show ?thesis using assms(2)[OF that(1,2)] by (simp add: fixed_def fun_eq_iff)
  qed
qed

end

context expr_sem
begin

definition group_by_only where
  "group_by_only D = fixed ((mind |\<union>| D) |\<inter>| maxd) (fgroupby D) sem"

abbreviation total where
  "total \<equiv> group_by_only {||}"

theorem lawful_group_by_only:
  "lawful ((mind |\<union>| D) |\<inter>| maxd) ((mind |\<union>| D) |\<inter>| maxd) (group_by_only D)"
  unfolding group_by_only_def
proof (rule lawful_fixed)
  show "sem (fgroupby D (peg K F)) K = sem (fgroupby D F) K" for F K
    by (simp add: fgroupby_peg peg_below tcut_below)
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

text \<open>\<open>E FOR W G\<close> is evaluated at the incoming frame's keys, cut to the key dimensions of the
  inner frame.\<close>

context expr_sem
begin

definition filtfor where
  "filtfor W G F k =
     (if k \<in> keyimg S F (kd F) then sem (ffor W G F) (tcut (fset (kd (ffor W G F)))\<cdot>k) else \<bottom>)"

abbreviation exclude where
  "exclude W \<equiv> filtfor W \<^bold>1"

lemma fdims_ffor [simp]: "fdims (ffor W G F) = fdims F |-| W"
  by (simp add: ffor_def)

theorem lawful_filtfor: "lawful mind maxd (filtfor W G)"
proof (rule lawfulI)
  show "mind |\<subseteq>| maxd" by (rule mind_maxd)
  show "filtfor W G F k \<noteq> \<bottom> \<Longrightarrow> k \<in> keyimg S F (kd F)" for F k
    by (auto simp: filtfor_def split: if_splits)
  show "filtfor W G (peg K F) K = filtfor W G F K" for F K
  proof (cases "K \<in> keyimg S F (kd F)")
    case False
    then show ?thesis by (simp add: filtfor_def keyimg_peg_iff[OF dataset_S])
  next
    case True
    let ?H = "ffor W G F" and ?K' = "tcut (- fset W)\<cdot>K"
    let ?k = "tcut (fset (kd (ffor W G F)))\<cdot>K"
    have ts: "tsupp K = fset (kd F)" by (rule keyimg_tsupp[OF dataset_S True])
    have "?K' \<sqsubseteq> ?k" by (rule tcut_below_tcut) (auto simp: ts)
    then have "sem (peg ?K' ?H) ?k = sem ?H ?k" by (rule peg_below)
    then show ?thesis using True by (simp add: filtfor_def keyimg_peg_iff[OF dataset_S] ffor_peg)
  qed
  show "filtfor W G F' (tcut (fset (kd F'))\<cdot>(K1 \<squnion> K)) = filtfor W G F K1"
    if "amb F = amb F'" "slice F = slice F'" "pins F K" "dims F - tsupp K = dims F' - tsupp K"
       "filtfor W G F K1 \<noteq> \<bottom>" for F F' K K1
  proof -
    note asm = that
    let ?H = "ffor W G F" and ?H' = "ffor W G F'" and ?K'' = "tcut (- fset W)\<cdot>K"
    define T where "T = tsupp K"
    have cut: "\<And>A B. B \<subseteq> A \<Longrightarrow> tcut B\<cdot>(keyof A\<cdot>m) = keyof B\<cdot>m" for m
      by (simp add: tcut_keyof Int_absorb1 Int_absorb2)
    from asm(5) have K1: "K1 \<in> keyimg S F (kd F)" and ni: "sem ?H (tcut (fset (kd ?H))\<cdot>K1) \<noteq> \<bottom>"
      by (auto simp: filtfor_def split: if_splits)
    obtain m where m: "m \<in> pts S" "m \<in> frows F" "\<forall>d\<in>fset (kd F) \<union> tsupp K. \<lbrakk>d\<rbrakk>\<cdot>m \<noteq> \<bottom>"
        "K1 = keyof (fset (kd F))\<cdot>m" "K = keyof (tsupp K)\<cdot>m"
      by (rule pinned_witness[OF dataset_S asm(3) K1])
    have KT: "K = keyof T\<cdot>m" unfolding T_def by (rule m(5))
    have dF': "dims F' \<subseteq> dims F \<union> T" using asm(4) unfolding T_def by blast
    have s1: "fset (kd F') \<subseteq> fset (kd F) \<union> T" using dF' by (auto simp: dims_def)
    have s2: "fset (kd ?H') \<subseteq> fset (kd ?H) \<union> (T - fset W)" using dF' by (auto simp: dims_def)
    have s3: "fset (kd ?H) \<subseteq> fset (kd F)" by auto
    have s4: "fset (kd ?H') \<subseteq> fset (kd F')" by auto
    have mF': "m \<in> frows F'" using m(2) frows_cong[OF asm(1,2)] by simp
    have j: "K1 \<squnion> K = keyof (fset (kd F) \<union> T)\<cdot>m" by (simp only: m(4) KT keyof_Un)
    have k2: "tcut (fset (kd F'))\<cdot>(K1 \<squnion> K) = keyof (fset (kd F'))\<cdot>m"
      unfolding j by (rule cut[OF s1])
    have k2in: "keyof (fset (kd F'))\<cdot>m \<in> keyimg S F' (kd F')"
      by (rule keyimg_at[OF dataset_S m(1) mF']) (use m(3) s1 T_def in blast)
    have pH: "pins ?H ?K''"
    proof -
      from asm(3) have fin: "compact K" and le: "slice F \<^bold>\<le> spin K"
        by (auto simp: pins_def)
      have "slice ?H \<^bold>\<le> coarsen (- fset W) (slice F)" by (simp add: ffor_def)
      moreover have "coarsen (- fset W) (slice F) \<^bold>\<le> spin ?K''"
        using coarsen_mono[OF le] by (simp add: coarsen_spin)
      ultimately have "slice ?H \<^bold>\<le> spin ?K''" by (rule sord.trans)
      then show ?thesis using compact_tcut_compact[OF fin] by (simp add: pins_def)
    qed
    have dH: "dims ?H - tsupp ?K'' = dims ?H' - tsupp ?K''"
      using asm(4) by (auto simp: dims_def tsupp_tcut)
    have fH: "amb ?H = amb ?H'" "slice ?H = slice ?H'" by (simp_all add: ffor_def asm(1,2))
    have IH: "sem ?H' (tcut (fset (kd ?H'))\<cdot>(tcut (fset (kd ?H))\<cdot>K1 \<squnion> ?K''))
              = sem ?H (tcut (fset (kd ?H))\<cdot>K1)"
      by (rule dims_law[OF fH pH dH ni])
    have e1: "tcut (fset (kd ?H))\<cdot>K1 = keyof (fset (kd ?H))\<cdot>m"
      unfolding m(4) by (rule cut[OF s3])
    have e2: "?K'' = keyof (T - fset W)\<cdot>m" by (simp add: KT tcut_keyof Diff_eq)
    have key: "tcut (fset (kd ?H'))\<cdot>(tcut (fset (kd ?H))\<cdot>K1 \<squnion> ?K'')
               = tcut (fset (kd ?H'))\<cdot>(keyof (fset (kd F'))\<cdot>m)"
      unfolding e1 e2 keyof_Un[symmetric] cut[OF s2] cut[OF s4] ..
    have "filtfor W G F' (tcut (fset (kd F'))\<cdot>(K1 \<squnion> K))
          = sem ?H' (tcut (fset (kd ?H'))\<cdot>(keyof (fset (kd F'))\<cdot>m))"
      unfolding filtfor_def k2 by (simp only: if_P[OF k2in])
    also have "\<dots> = sem ?H (tcut (fset (kd ?H))\<cdot>K1)" using IH unfolding key .
    also have "\<dots> = filtfor W G F K1" unfolding filtfor_def by (simp only: if_P[OF K1])
    finally show ?thesis .
  qed
  show "filtfor W G F = filtfor W G F'"
    if "amb F = amb F'" "slice F = slice F'" "kd F = kd F'" for F F'
  proof -
    have k: "keyimg S F (kd F) = keyimg S F' (kd F')"
      using keyimg_cong[OF frows_cong[OF that(1,2)]] that(3) by simp
    have kH: "kd (ffor W G F) = kd (ffor W G F')"
      using that(3) unfolding fset_eq_iff by auto
    have "sem (ffor W G F) = sem (ffor W G F')"
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
  show "mind |\<subseteq>| maxd" by (rule mind_maxd)
  show "restrict \<phi> sem F k \<noteq> \<bottom> \<Longrightarrow> k \<in> keyimg S F (kd F)" for F k
    using key_law[of "frestrict \<phi> F" k] keyimg_mono[OF dataset_S, of "frestrict \<phi> F" F]
    by (auto simp: restrict_def frows_frestrict)
  show "restrict \<phi> sem (peg K F) K = restrict \<phi> sem F K" for F K
    by (simp add: restrict_def peg_frestrict[symmetric] peg_law)
  show "restrict \<phi> sem F' (tcut (fset (kd F'))\<cdot>(K1 \<squnion> K)) = restrict \<phi> sem F K1"
    if "amb F = amb F'" "slice F = slice F'" "pins F K" "dims F - tsupp K = dims F' - tsupp K"
       "restrict \<phi> sem F K1 \<noteq> \<bottom>" for F F' K K1
  proof -
    have "pins (frestrict \<phi> F) K" using that(3) by (simp add: pins_def)
    moreover have "dims (frestrict \<phi> F) - tsupp K = dims (frestrict \<phi> F') - tsupp K"
      using that(4) by (simp add: dims_def)
    ultimately show ?thesis
      using dims_law[of "frestrict \<phi> F" "frestrict \<phi> F'" K K1] that(1,2,5)
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