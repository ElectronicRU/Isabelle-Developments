theory Slicer
  imports ValsetBase Congruence "HOL-Library.FSet"
begin

default_sort type

section \<open>Levels of detail as syntactic dimension sets\<close>

text \<open>
  Dimensions are drawn from a (countable, nominal) label set \<^typ>\<open>'d\<close>; each label is
  evaluated on rows by a continuous row-level expression into a value domain.  Two labels may
  share an expression: they are then functionally dependent, but distinct.  A level of detail
  is a set of labels, and its meaning on a row is the tuple of its dimensions' values, with the
  other coordinates cut to \<^term>\<open>\<bottom>\<close>.

  The image of a row under this map need \<^emph>\<open>not\<close> be a stable subdomain of the tuple domain
  (with an expression dimension \<open>c \<approx> a + b\<close> the allowable sub-rows are not closed under existing
  joins), and we never require it to be: the domain stays the source rows, and functional
  dependence is stated relationally via kernel orders.
\<close>

locale dim_eval =
  fixes deval :: "'d \<Rightarrow> ('r::pcpo \<rightarrow> 'v::pcpo)" (\<open>\<lbrakk>_\<rbrakk>\<close>)
begin

definition keyof :: "'d set \<Rightarrow> 'r \<rightarrow> ('d, 'v) tuple" where
  "keyof D = (\<Lambda> r. tcut D\<cdot>(Abs_tuple (\<lambda>d. \<lbrakk>d\<rbrakk>\<cdot>r)))"

lemma keyof_beta: "keyof D\<cdot>r = tcut D\<cdot>(Abs_tuple (\<lambda>d. \<lbrakk>d\<rbrakk>\<cdot>r))"
  unfolding keyof_def by (simp add: cont_Abs_tuple)

lemma keyof_tget: "(keyof D\<cdot>r)\<langle>d\<rangle> = (if d \<in> D then \<lbrakk>d\<rbrakk>\<cdot>r else \<bottom>)"
  by (simp add: keyof_beta tcut_tget Abs_tuple_inverse')

lemma keyof_empty [simp]: "keyof {} = \<bottom>"
  by (intro cfun_eqI tuple_eqI) (simp add: keyof_tget tget_strict)

lemma keyof_mono: "D \<subseteq> E \<Longrightarrow> keyof D \<sqsubseteq> keyof E"
  by (simp add: cfun_below_iff below_tuple_def fun_below_iff keyof_tget subset_iff)

text \<open>Coarsening a level of detail is cutting its key: \<^term>\<open>keyof E\<close> determines
  \<^term>\<open>keyof D\<close> for \<^term>\<open>D \<subseteq> E\<close> uniformly, by \<^term>\<open>tcut D\<close>.\<close>

lemma tcut_keyof: "tcut E\<cdot>(keyof D\<cdot>r) = keyof (D \<inter> E)\<cdot>r"
  by (simp add: keyof_beta tcut_compose Int_commute)

lemma tsupp_keyof: "tsupp (keyof A\<cdot>m) = {d \<in> A. \<lbrakk>d\<rbrakk>\<cdot>m \<noteq> \<bottom>}"
  by (auto simp: tsupp_def keyof_tget)

subsection \<open>Kernel orders and functional dependence\<close>

definition kern :: "'d set \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> bool" where
  "kern D x y \<longleftrightarrow> keyof D\<cdot>x \<sqsubseteq> keyof D\<cdot>y"

lemma kern_iff: "kern D x y \<longleftrightarrow> (\<forall>d\<in>D. \<lbrakk>d\<rbrakk>\<cdot>x \<sqsubseteq> \<lbrakk>d\<rbrakk>\<cdot>y)"
  unfolding kern_def below_tuple_def fun_below_iff by (auto simp: keyof_tget)

lemma is_cong_kern: "is_cong (kern D)"
  unfolding kern_def by unfold_locales (auto intro: below_trans monofun_cfun_arg)

lemma kern_empty: "kern {} x y"
  by (simp add: kern_iff)

lemma kern_Un: "kern (D \<union> E) = inf (kern D) (kern E)"
  by (auto simp: kern_iff fun_eq_iff)

lemma kern_antimono: "D \<subseteq> E \<Longrightarrow> kern E x y \<Longrightarrow> kern D x y"
  by (auto simp: kern_iff)

text \<open>Functional dependence of \<^term>\<open>D\<close> on \<^term>\<open>E\<close>, relative to a support set
  \<^term>\<open>S\<close> of source rows: rows that \<^term>\<open>E\<close> cannot tell apart (in the kernel order),
  \<^term>\<open>D\<close> cannot either.  Taking \<^term>\<open>S = UNIV\<close> gives schema-level dependence; taking
  \<^term>\<open>S\<close> to be the rows a filter selects gives the data-level one.\<close>

definition fdep :: "'r set \<Rightarrow> 'd set \<Rightarrow> 'd set \<Rightarrow> bool" where
  "fdep S D E \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. kern E x y \<longrightarrow> kern D x y)"

lemma fdep_refl: "fdep S D D"
  by (simp add: fdep_def)

lemma fdep_trans: "fdep S D E \<Longrightarrow> fdep S E F \<Longrightarrow> fdep S D F"
  unfolding fdep_def by blast

lemma fdep_subset: "D \<subseteq> E \<Longrightarrow> fdep S D E"
  unfolding fdep_def by (blast intro: kern_antimono)

lemma fdep_Un: "fdep S D F \<Longrightarrow> fdep S E F \<Longrightarrow> fdep S (D \<union> E) F"
  unfolding fdep_def by (simp add: kern_Un)

lemma fdep_support_mono: "S' \<subseteq> S \<Longrightarrow> fdep S D E \<Longrightarrow> fdep S' D E"
  unfolding fdep_def by blast

end

text \<open>A single dimension into a flat value domain is a flat congruence: the generators.\<close>

lemma is_flat_cong_kern_single:
  fixes deval :: "'d \<Rightarrow> ('r::pcpo \<rightarrow> 'v::flat)"
  shows "is_flat_cong (dim_eval.kern deval {d})"
  unfolding dim_eval.kern_iff by (simp add: is_flat_cong_eq_on)

text \<open>With bounded-complete values (in particular flat ones, via the subclass
  \<open>flat \<subseteq> bounded_complete\<close>), the union of dimension sets is the pointwise join.\<close>

lemma keyof_Un:
  fixes deval :: "'d \<Rightarrow> ('r::pcpo \<rightarrow> 'v::bounded_complete)"
  shows "dim_eval.keyof deval (D \<union> E)\<cdot>r = dim_eval.keyof deval D\<cdot>r \<squnion> dim_eval.keyof deval E\<cdot>r"
  by (simp add: dim_eval.keyof_beta tcut_join)

section \<open>Filters\<close>

text \<open>A filter is a continuous predicate into \<^typ>\<open>one\<close> (Sierpinski space): the rows it
  \<^emph>\<open>selects\<close> are those it maps to \<^term>\<open>ONE\<close>, a Scott-open set.  Several filters are
  combined by continuous conjunction.\<close>

definition selected :: "('r::pcpo \<rightarrow> one) \<Rightarrow> 'r set" where
  "selected \<phi> = {r. \<phi>\<cdot>r = ONE}"

lemma selected_upclosed: "x \<in> selected \<phi> \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> y \<in> selected \<phi>"
  unfolding selected_def by (cases "\<phi>\<cdot>y") (auto dest: monofun_cfun_arg[of x y \<phi>])

lemma selected_open: "adm (\<lambda>r. r \<notin> selected \<phi>)"
proof -
  have "r \<notin> selected \<phi> \<longleftrightarrow> \<phi>\<cdot>r \<sqsubseteq> \<bottom>" for r
    unfolding selected_def by (cases "\<phi>\<cdot>r") simp_all
  then show ?thesis by simp
qed

definition fconj :: "('r::pcpo \<rightarrow> one) \<Rightarrow> ('r \<rightarrow> one) \<Rightarrow> ('r \<rightarrow> one)" where
  "fconj \<phi> \<psi> = (\<Lambda> r. seq\<cdot>(\<phi>\<cdot>r)\<cdot>(\<psi>\<cdot>r))"

lemma selected_fconj: "selected (fconj \<phi> \<psi>) = selected \<phi> \<inter> selected \<psi>"
  unfolding selected_def fconj_def by (auto simp: seq_conv_if split: if_splits)

lemma selected_ftrue: "selected (\<Lambda> _. ONE) = UNIV"
  by (simp add: selected_def)

section \<open>Datasets\<close>

text \<open>A dataset is a Scott-closed set \<^term>\<open>S\<close> of rows whose \<^emph>\<open>maximal\<close> elements are the
  actual data points; the rest are their partial approximations (sub-rows).  These need not be
  maximal in the row \<^emph>\<open>type\<close>.  Applying a filter keeps the selected data points and everything
  below them.  The result is generally \<^emph>\<open>not\<close> a stable subdomain (it need not be closed under
  joins of compatible sub-rows), but it is again a dataset, with exactly the selected points as
  its maximal elements.  We assume finitely many data points, which also makes closedness
  automatic.\<close>

definition pts :: "'r::pcpo set \<Rightarrow> 'r set" where
  "pts S = {m \<in> S. \<forall>y\<in>S. m \<sqsubseteq> y \<longrightarrow> y = m}"

definition filtered :: "'r::pcpo set \<Rightarrow> 'r set \<Rightarrow> 'r set" where
  "filtered S P = {x. \<exists>m \<in> pts S \<inter> P. x \<sqsubseteq> m}"

lemma adm_below_finite: "finite P \<Longrightarrow> adm (\<lambda>x. \<exists>m\<in>P. x \<sqsubseteq> m)"
  by (induct rule: finite_induct) simp_all

locale dataset =
  fixes S :: "'r::pcpo set"
  assumes downward: "y \<in> S \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> x \<in> S"
    and max_above: "x \<in> S \<Longrightarrow> \<exists>m\<in>pts S. x \<sqsubseteq> m"
    and finite_pts: "finite (pts S)"
begin

lemma S_eq: "S = {x. \<exists>m\<in>pts S. x \<sqsubseteq> m}"
  using max_above downward unfolding pts_def by blast

lemma closed: "adm (\<lambda>x. x \<in> S)"
  by (subst S_eq) (simp add: adm_below_finite finite_pts)

lemma filtered_subset: "filtered S P \<subseteq> S"
  unfolding filtered_def pts_def using downward by blast

lemma pts_filtered: "pts (filtered S P) = pts S \<inter> P"
  using filtered_subset unfolding filtered_def pts_def by (auto 6 3)

lemma dataset_filtered: "dataset (filtered S P)"
proof
  show "y \<in> filtered S P \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> x \<in> filtered S P" for x y
    unfolding filtered_def by (blast intro: below_trans)
  show "x \<in> filtered S P \<Longrightarrow> \<exists>m\<in>pts (filtered S P). x \<sqsubseteq> m" for x
    unfolding pts_filtered by (auto simp: filtered_def)
  show "finite (pts (filtered S P))"
    unfolding pts_filtered using finite_pts by simp
qed

lemma filtered_filtered: "filtered (filtered S P) Q = filtered S (P \<inter> Q)"
  unfolding filtered_def[of "filtered S P"] pts_filtered
  by (auto simp: filtered_def)

lemma filtered_UNIV: "filtered S UNIV = S"
  by (subst (2) S_eq) (simp add: filtered_def)

end

section \<open>Dropping dimensions from filters: the existential projection\<close>

text \<open>Keeping only the dimensions \<^term>\<open>A\<close>, the best a filter can do is select every row whose
  \<open>A\<close>-information lies above that of some row the original filter selects (over the row
  \<^emph>\<open>type\<close>, not the data).  This set reads only \<open>A\<close>, contains the original selection, and is
  the least such set.  It is a specification, not a computation: concrete dropping procedures
  are required to select \<^emph>\<open>at least\<close> this set.\<close>

context dim_eval
begin

definition exsel :: "'d set \<Rightarrow> 'r set \<Rightarrow> 'r set" where
  "exsel A U = {x. \<exists>y\<in>U. kern A y x}"

lemma subset_exsel: "U \<subseteq> exsel A U"
  unfolding exsel_def kern_def by auto

lemma exsel_up: "x \<in> exsel A U \<Longrightarrow> kern A x x' \<Longrightarrow> x' \<in> exsel A U"
  unfolding exsel_def kern_def by (blast intro: below_trans)

lemma exsel_least:
  assumes "U \<subseteq> V" and "\<And>x x'. x \<in> V \<Longrightarrow> kern A x x' \<Longrightarrow> x' \<in> V"
  shows "exsel A U \<subseteq> V"
  unfolding exsel_def using assms by blast

lemma exsel_antimono: "A \<subseteq> B \<Longrightarrow> exsel B U \<subseteq> exsel A U"
  unfolding exsel_def using kern_antimono by blast

text \<open>If the selection only reads dimensions in \<^term>\<open>A\<close>, keeping \<^term>\<open>A\<close> loses nothing.\<close>

lemma exsel_supported:
  assumes "\<And>x y. kern A x y \<Longrightarrow> x \<in> U \<Longrightarrow> y \<in> U"
  shows "exsel A U = U"
  using assms subset_exsel unfolding exsel_def by blast

lemma selected_kern:
  assumes "\<And>x y. kern A x y \<Longrightarrow> \<phi>\<cdot>x \<sqsubseteq> \<phi>\<cdot>y" and "kern A x y" and "x \<in> selected \<phi>"
  shows "y \<in> selected \<phi>"
  using assms(1)[OF assms(2)] assms(3) by (cases "\<phi>\<cdot>y") (simp_all add: selected_def)

end

section \<open>Slicers\<close>


subsection \<open>Selections\<close>

text \<open>What slices select: Scott-open sets of rows, i.e.\ upward closed and
  inaccessible by directed sups.  These correspond one-to-one to filters
  \<^typ>\<open>'r \<rightarrow> one\<close> (via \<^term>\<open>selected\<close>), but as sets they are plainly a distributive
  bounded lattice under intersection and union.\<close>

typedef 'r sel = "{U :: 'r::pcpo set. (\<forall>x y. x \<in> U \<longrightarrow> x \<sqsubseteq> y \<longrightarrow> y \<in> U) \<and> adm (\<lambda>x. x \<notin> U)}"
  morphisms sel_rows Abs_sel
  by (rule exI[of _ UNIV]) simp

setup_lifting type_definition_sel

lift_definition sel_of :: "('r::pcpo \<rightarrow> one) \<Rightarrow> 'r sel" is selected
  using selected_upclosed selected_open by blast

instantiation sel :: (pcpo) "{distrib_lattice, bounded_lattice}"
begin

lift_definition less_eq_sel :: "'a sel \<Rightarrow> 'a sel \<Rightarrow> bool" is "(\<subseteq>)" .
lift_definition less_sel :: "'a sel \<Rightarrow> 'a sel \<Rightarrow> bool" is "(\<subset>)" .
lift_definition inf_sel :: "'a sel \<Rightarrow> 'a sel \<Rightarrow> 'a sel" is "(\<inter>)"
  by (auto intro!: adm_disj)
lift_definition sup_sel :: "'a sel \<Rightarrow> 'a sel \<Rightarrow> 'a sel" is "(\<union>)"
  by (auto intro!: adm_conj)
lift_definition bot_sel :: "'a sel" is "{}" by simp
lift_definition top_sel :: "'a sel" is UNIV by simp

instance by standard (transfer; auto)+

end

lemma sel_eqI: "(\<And>x. x \<in> sel_rows a \<longleftrightarrow> x \<in> sel_rows b) \<Longrightarrow> a = b"
  by (simp add: sel_rows_inject[symmetric] set_eq_iff)

subsection \<open>Semilattice homomorphisms\<close>

text \<open>Slices are an algebra given by laws (e.g.\ a quotient of syntax), not a type class:
  conjunction alone is assumed to form a semilattice with unit.  Their selections, their
  dimensions and their coarsening are all homomorphisms of such, into different targets.\<close>

locale semilattice_hom = src: semilattice_neutr f z + tgt: semilattice_neutr g w
  for f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and z :: 'a and g :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" and w :: 'b +
  fixes h :: "'a \<Rightarrow> 'b"
  assumes hom_f: "h (f a b) = g (h a) (h b)"
    and hom_z: "h z = w"

subsection \<open>Key-level projection\<close>

text \<open>Slices select keys, not rows.  Coarsening to the dimensions \<^term>\<open>A\<close> must
  accept the \<open>A\<close>-cut of every key the original accepts.  This ranges over all keys, not only
  those some row realises: under a functional dependency \<open>c = a + b\<close>, coarsening
  \<open>a = 1 \<and> c = 3\<close> to \<open>b\<close> must accept every \<open>b\<close>, not just \<open>b = 2\<close>.\<close>

lemma sel_rows_upclosed: "x \<in> sel_rows s \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> y \<in> sel_rows s"
  using sel_rows[of s] by blast

subsection \<open>Slice selections\<close>

text \<open>Slices are given by their conjunction \<open>\<^bold>*\<close> and its unit \<open>\<^bold>1\<close>, nothing more: the slicer
  constructs only conjoin.  The order is the one conjunction induces.  Each slice comes with the
  dimensions it is written with, \<open>sdims\<close> (an upper bound on what it reads, not the least one);
  its selection \<open>ssel\<close>, an open set of keys, is a meet-semilattice homomorphism reading only
  those dimensions, and selects only keys defined on all of them.\<close>

locale slice_sel = conj: semilattice_neutr conj sunit +
  ssel: semilattice_hom conj sunit inf top ssel +
  sdims: semilattice_hom conj sunit sup bot sdims
  for conj :: "'f \<Rightarrow> 'f \<Rightarrow> 'f" (infixl \<open>\<^bold>*\<close> 70) and sunit :: 'f (\<open>\<^bold>1\<close>)
    and ssel :: "'f \<Rightarrow> ('d, 'v::pcpo) tuple sel" and sdims :: "'f \<Rightarrow> 'd set" +
  assumes ssel_sdims: "t \<in> sel_rows (ssel f) \<Longrightarrow> tcut (sdims f)\<cdot>t \<in> sel_rows (ssel f)"
    and ssel_total: "t \<in> sel_rows (ssel f) \<Longrightarrow> sdims f \<subseteq> tsupp t"
begin

lemmas sdims_conj [simp] = sdims.hom_f and sdims_unit [simp] = sdims.hom_z

definition sle :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix \<open>\<^bold>\<le>\<close> 50) where
  "a \<^bold>\<le> b \<longleftrightarrow> a = a \<^bold>* b"

definition slt :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix \<open>\<^bold><\<close> 50) where
  "a \<^bold>< b \<longleftrightarrow> a \<^bold>\<le> b \<and> a \<noteq> b"

sublocale sord: semilattice_neutr_order conj sunit sle slt
  by unfold_locales (simp_all add: sle_def slt_def)

lemma ssel_mono: "a \<^bold>\<le> b \<Longrightarrow> ssel a \<le> ssel b"
  unfolding sle_def by (metis ssel.hom_f inf.orderI)

lemma ssel_dim:
  assumes "sdims f \<subseteq> D" and "t \<in> sel_rows (ssel f)"
  shows "tcut D\<cdot>t \<in> sel_rows (ssel f)"
  using ssel_sdims[OF assms(2)] tcut_mono_set[OF assms(1)] by (rule sel_rows_upclosed)

lemma ssel_dim_iff:
  "sdims f \<subseteq> D \<Longrightarrow> tcut D\<cdot>t \<in> sel_rows (ssel f) \<longleftrightarrow> t \<in> sel_rows (ssel f)"
  using ssel_dim sel_rows_upclosed tcut_below by blast

end

subsection \<open>Slicers\<close>

text \<open>A slicer adds \<^emph>\<open>coarsening\<close> of a slice to a given (possibly co-finite) set of dimensions
  to keep: \<open>GROUP BY ONLY D\<close> keeps \<open>D\<close>, \<open>FOR W\<close> keeps \<open>- W\<close>.  It distributes over conjunction,
  leaves slices written inside the target alone, keeps only target dimensions, and accepts the
  cut of every key the original accepts.  It is \<^emph>\<open>not\<close> extensional: coarsening
  \<open>b = 2 \<and> b \<noteq> 2\<close> away from \<open>b\<close> gives \<open>True\<close>, coarsening \<open>False\<close> gives \<open>False\<close>.\<close>

locale slicer = slice_sel conj sunit ssel sdims
  for conj :: "'f \<Rightarrow> 'f \<Rightarrow> 'f" (infixl \<open>\<^bold>*\<close> 70) and sunit :: 'f (\<open>\<^bold>1\<close>)
    and ssel :: "'f \<Rightarrow> ('d, 'v::pcpo) tuple sel" and sdims +
  fixes coarsen :: "'d set \<Rightarrow> 'f \<Rightarrow> 'f"
  assumes coarsen_conj: "coarsen A (a \<^bold>* b) = coarsen A a \<^bold>* coarsen A b"
    and coarsen_inside: "sdims f \<subseteq> A \<Longrightarrow> coarsen A f = f"
    and sdims_coarsen: "sdims (coarsen A f) \<subseteq> sdims f \<inter> A"
    and coarsen_cut: "t \<in> sel_rows (ssel f) \<Longrightarrow> tcut A\<cdot>t \<in> sel_rows (ssel (coarsen A f))"
begin

lemma coarsen_unit [simp]: "coarsen A \<^bold>1 = \<^bold>1"
  by (rule coarsen_inside) simp

lemma coarsen_hom: "semilattice_hom conj sunit conj sunit (coarsen A)"
  by unfold_locales (fact coarsen_conj coarsen_unit)+

lemma coarsen_mono: "a \<^bold>\<le> b \<Longrightarrow> coarsen A a \<^bold>\<le> coarsen A b"
  unfolding sle_def by (metis coarsen_conj)

lemma sdims_coarsen_target: "sdims (coarsen A f) \<subseteq> A"
  by (rule subset_trans[OF sdims_coarsen Int_lower2])

lemma selected_coarsen: "t \<in> sel_rows (ssel f) \<Longrightarrow> t \<in> sel_rows (ssel (coarsen A f))"
  using coarsen_cut tcut_below by (rule sel_rows_upclosed)

lemma ssel_coarsen_reads:
  "t \<in> sel_rows (ssel (coarsen A f)) \<Longrightarrow> tcut A\<cdot>t \<in> sel_rows (ssel (coarsen A f))"
  by (rule ssel_dim[OF sdims_coarsen_target])

text \<open>A slice written entirely outside the target coarsens to a constant, which is
  \<^term>\<open>top\<close> as soon as the slice selects anything.  Syntactically this fails:
  \<open>False \<and> a = 1\<close> coarsens to \<open>False\<close> away from \<open>a\<close>.\<close>

lemma coarsen_outside:
  assumes "sdims f \<inter> A = {}" and "t \<in> sel_rows (ssel f)"
  shows "ssel (coarsen A f) = top"
proof (rule sel_eqI)
  fix u
  have "sdims (coarsen A f) \<subseteq> {}"
    using sdims_coarsen[of A f] assms(1) by blast
  moreover have "t \<in> sel_rows (ssel (coarsen A f))"
    using selected_coarsen assms(2) by blast
  moreover have "tcut {}\<cdot>t = \<bottom>"
    by (rule tuple_eqI) (simp add: tget_strict)
  ultimately have "\<bottom> \<in> sel_rows (ssel (coarsen A f))"
    using ssel_dim[of "coarsen A f" "{}" t] by simp
  then show "u \<in> sel_rows (ssel (coarsen A f)) \<longleftrightarrow> u \<in> sel_rows top"
    by (auto simp: top_sel.rep_eq intro: sel_rows_upclosed)
qed

end

subsection \<open>Rows versus keys\<close>

text \<open>A row selection reading only the dimensions \<^term>\<open>D\<close> is the same thing as a key selection,
  via the level-of-detail map: its up-image is open (for finite \<^term>\<open>D\<close> and chain-finite
  values, where the cut keys are compact), and its preimage gives back the row selection.
  Preimages of open key sets are open for any \<^term>\<open>D\<close>.\<close>


context dim_eval
begin

definition keyup :: "'d set \<Rightarrow> 'r set \<Rightarrow> ('d, 'v) tuple set" where
  "keyup D V = {t. \<exists>r\<in>V. keyof D\<cdot>r \<sqsubseteq> t}"

definition rowpre :: "'d set \<Rightarrow> ('d, 'v) tuple set \<Rightarrow> 'r set" where
  "rowpre D U = {r. keyof D\<cdot>r \<in> U}"

lemma keyup_upclosed: "t \<in> keyup D V \<Longrightarrow> t \<sqsubseteq> t' \<Longrightarrow> t' \<in> keyup D V"
  unfolding keyup_def by (blast intro: below_trans)

lemma rowpre_keyup:
  assumes "\<And>x y. kern D x y \<Longrightarrow> x \<in> V \<Longrightarrow> y \<in> V"
  shows "rowpre D (keyup D V) = V"
  using assms unfolding rowpre_def keyup_def kern_def by blast

lemma rowpre_upclosed: "(\<And>t t'. t \<in> U \<Longrightarrow> t \<sqsubseteq> t' \<Longrightarrow> t' \<in> U) \<Longrightarrow> r \<in> rowpre D U \<Longrightarrow> r \<sqsubseteq> r' \<Longrightarrow> r' \<in> rowpre D U"
  unfolding rowpre_def by (blast intro: monofun_cfun_arg)

lemma rowpre_open: "adm (\<lambda>t. t \<notin> U) \<Longrightarrow> adm (\<lambda>r. r \<notin> rowpre D U)"
  unfolding rowpre_def mem_Collect_eq
  by (rule adm_subst[of "\<lambda>r. keyof D\<cdot>r" "\<lambda>t. t \<notin> U", simplified]) simp_all

end

lemma keyup_open:
  fixes deval :: "'d \<Rightarrow> ('r::pcpo \<rightarrow> 'v::{pcpo, chfin})"
  assumes "finite D"
  shows "adm (\<lambda>t. t \<notin> dim_eval.keyup deval D V)"
proof (rule admI)
  fix Y :: "nat \<Rightarrow> ('d, 'v) tuple"
  assume Y: "chain Y" "\<forall>i. Y i \<notin> dim_eval.keyup deval D V"
  show "(\<Squnion>i. Y i) \<notin> dim_eval.keyup deval D V"
  proof
    assume "(\<Squnion>i. Y i) \<in> dim_eval.keyup deval D V"
    then obtain r where "r \<in> V" "dim_eval.keyof deval D\<cdot>r \<sqsubseteq> (\<Squnion>i. Y i)"
      by (auto simp: dim_eval.keyup_def)
    moreover have "compact (dim_eval.keyof deval D\<cdot>r)"
      using assms by (simp add: dim_eval.keyof_beta compact_tcut)
    ultimately obtain i where "dim_eval.keyof deval D\<cdot>r \<sqsubseteq> Y i"
      using Y(1) compact_below_lub_iff by blast
    with \<open>r \<in> V\<close> Y(2) show False by (auto simp: dim_eval.keyup_def)
  qed
qed

end
