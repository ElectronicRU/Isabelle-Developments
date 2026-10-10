theory SlicerToy
  imports Slicer
begin

section \<open>A toy slice syntax\<close>

text \<open>A throwaway model of slicers: a free syntax of atoms, conjunction, disjunction and
  negation, evaluated strictly (an error anywhere is an error of the whole), quotiented by the
  regular De Morgan laws.  Dimensions, values and atoms are fresh types; atoms are abstract
  expressions with lawful dimensions, negation and coarsening.\<close>

typedecl dim
typedecl vbase
type_synonym val = "vbase lift"
type_synonym key = "(dim, val) tuple"

subsection \<open>Three-valued predicates\<close>

text \<open>Where a three-valued predicate is true.\<close>

lift_definition holds :: "('a::pcpo \<rightarrow> tr) \<Rightarrow> 'a sel" is "\<lambda>p. {x. p\<cdot>x = TT}"
proof -
  fix p :: "'a \<rightarrow> tr"
  have "adm (\<lambda>x. p\<cdot>x \<noteq> TT)" by simp
  moreover have "p\<cdot>x = TT \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> p\<cdot>y = TT" for x y
    by (metis monofun_cfun_arg ax_flat dist_eq_tr(1))
  ultimately show "(\<forall>x y. x \<in> {x. p\<cdot>x = TT} \<longrightarrow> x \<sqsubseteq> y \<longrightarrow> y \<in> {x. p\<cdot>x = TT}) \<and>
      adm (\<lambda>x. x \<notin> {x. p\<cdot>x = TT})" by (simp only: mem_Collect_eq) blast
qed

lemma holds_TT [simp]: "holds (\<Lambda> _. TT) = top"
  by transfer simp

lemma neg_neg_tr [simp]: "neg\<cdot>(neg\<cdot>x) = x"
  by (cases x rule: trE) simp_all

lemma neg_eq_TT [simp]: "neg\<cdot>x = TT \<longleftrightarrow> x = FF"
  by (cases x rule: trE) simp_all

lemma neg_eq_FF [simp]: "neg\<cdot>x = FF \<longleftrightarrow> x = TT"
  by (cases x rule: trE) simp_all

lemma neg_eq_bot [simp]: "neg\<cdot>x = \<bottom> \<longleftrightarrow> x = \<bottom>"
  by (cases x rule: trE) simp_all

text \<open>Strict conjunction and disjunction: undefined (an error) as soon as either side is.
  (HOLCF's \<open>andalso\<close> and \<open>orelse\<close> are strict on the left only.)\<close>

definition sand :: "tr \<rightarrow> tr \<rightarrow> tr" where
  "sand = (\<Lambda> x y. If x then y else If y then FF else FF)"

definition sor :: "tr \<rightarrow> tr \<rightarrow> tr" where
  "sor = (\<Lambda> x y. If x then If y then TT else TT else y)"

lemma sand_TT_iff [simp]: "sand\<cdot>x\<cdot>y = TT \<longleftrightarrow> x = TT \<and> y = TT"
  by (cases x rule: trE; cases y rule: trE) (simp_all add: sand_def)

lemma sand_FF_iff [simp]: "sand\<cdot>x\<cdot>y = FF \<longleftrightarrow> x \<noteq> \<bottom> \<and> y \<noteq> \<bottom> \<and> (x = FF \<or> y = FF)"
  by (cases x rule: trE; cases y rule: trE) (simp_all add: sand_def)

lemma sand_bot_iff [simp]: "sand\<cdot>x\<cdot>y = \<bottom> \<longleftrightarrow> x = \<bottom> \<or> y = \<bottom>"
  by (cases x rule: trE; cases y rule: trE) (simp_all add: sand_def)

lemma sor_TT_iff [simp]: "sor\<cdot>x\<cdot>y = TT \<longleftrightarrow> x \<noteq> \<bottom> \<and> y \<noteq> \<bottom> \<and> (x = TT \<or> y = TT)"
  by (cases x rule: trE; cases y rule: trE) (simp_all add: sor_def)

lemma sor_FF_iff [simp]: "sor\<cdot>x\<cdot>y = FF \<longleftrightarrow> x = FF \<and> y = FF"
  by (cases x rule: trE; cases y rule: trE) (simp_all add: sor_def)

lemma sor_bot_iff [simp]: "sor\<cdot>x\<cdot>y = \<bottom> \<longleftrightarrow> x = \<bottom> \<or> y = \<bottom>"
  by (cases x rule: trE; cases y rule: trE) (simp_all add: sor_def)

text \<open>The regular De Morgan laws hold for strict evaluation (Bochvar's logic); absorption does
  not: \<open>sand\<cdot>x\<cdot>(sor\<cdot>x\<cdot>\<bottom>) = \<bottom>\<close>.\<close>

lemma sand_assoc: "sand\<cdot>(sand\<cdot>x\<cdot>y)\<cdot>z = sand\<cdot>x\<cdot>(sand\<cdot>y\<cdot>z)"
  by (cases x rule: trE; cases y rule: trE; cases z rule: trE) (simp_all add: sand_def)

lemma sor_assoc: "sor\<cdot>(sor\<cdot>x\<cdot>y)\<cdot>z = sor\<cdot>x\<cdot>(sor\<cdot>y\<cdot>z)"
  by (cases x rule: trE; cases y rule: trE; cases z rule: trE) (simp_all add: sor_def)

lemma sand_comm: "sand\<cdot>x\<cdot>y = sand\<cdot>y\<cdot>x"
  by (cases x rule: trE; cases y rule: trE) (simp_all add: sand_def)

lemma sor_comm: "sor\<cdot>x\<cdot>y = sor\<cdot>y\<cdot>x"
  by (cases x rule: trE; cases y rule: trE) (simp_all add: sor_def)

lemma sand_left_comm: "sand\<cdot>x\<cdot>(sand\<cdot>y\<cdot>z) = sand\<cdot>y\<cdot>(sand\<cdot>x\<cdot>z)"
  by (cases x rule: trE; cases y rule: trE; cases z rule: trE) (simp_all add: sand_def)

lemma sor_left_comm: "sor\<cdot>x\<cdot>(sor\<cdot>y\<cdot>z) = sor\<cdot>y\<cdot>(sor\<cdot>x\<cdot>z)"
  by (cases x rule: trE; cases y rule: trE; cases z rule: trE) (simp_all add: sor_def)

lemmas sand_ac = sand_assoc sand_comm sand_left_comm
  and sor_ac = sor_assoc sor_comm sor_left_comm

lemma sand_idem: "sand\<cdot>x\<cdot>x = x"
  by (cases x rule: trE) (simp_all add: sand_def)

lemma sor_idem: "sor\<cdot>x\<cdot>x = x"
  by (cases x rule: trE) (simp_all add: sor_def)

lemma sand_sor_distrib: "sand\<cdot>x\<cdot>(sor\<cdot>y\<cdot>z) = sor\<cdot>(sand\<cdot>x\<cdot>y)\<cdot>(sand\<cdot>x\<cdot>z)"
  by (cases x rule: trE; cases y rule: trE; cases z rule: trE) (simp_all add: sand_def sor_def)

lemma sor_sand_distrib: "sor\<cdot>x\<cdot>(sand\<cdot>y\<cdot>z) = sand\<cdot>(sor\<cdot>x\<cdot>y)\<cdot>(sor\<cdot>x\<cdot>z)"
  by (cases x rule: trE; cases y rule: trE; cases z rule: trE) (simp_all add: sand_def sor_def)

lemma sand_TT: "sand\<cdot>x\<cdot>TT = x" "sand\<cdot>TT\<cdot>x = x"
  by (cases x rule: trE; simp add: sand_def)+

lemma sor_FF: "sor\<cdot>x\<cdot>FF = x" "sor\<cdot>FF\<cdot>x = x"
  by (cases x rule: trE; simp add: sor_def)+

lemma neg_sand: "neg\<cdot>(sand\<cdot>x\<cdot>y) = sor\<cdot>(neg\<cdot>x)\<cdot>(neg\<cdot>y)"
  by (cases x rule: trE; cases y rule: trE) (simp_all add: sand_def sor_def)

lemma neg_sor: "neg\<cdot>(sor\<cdot>x\<cdot>y) = sand\<cdot>(neg\<cdot>x)\<cdot>(neg\<cdot>y)"
  by (cases x rule: trE; cases y rule: trE) (simp_all add: sand_def sor_def)

text \<open>The order strict conjunction induces is the chain \<open>\<bottom> < FF < TT\<close>: \<open>x\<close> implies \<open>y\<close> when \<open>y\<close>
  is true wherever \<open>x\<close> is, and defined wherever \<open>x\<close> is.\<close>

lemma sand_left_iff: "sand\<cdot>x\<cdot>y = x \<longleftrightarrow> (x = TT \<longrightarrow> y = TT) \<and> (x \<noteq> \<bottom> \<longrightarrow> y \<noteq> \<bottom>)"
  by (cases x rule: trE; cases y rule: trE) (simp_all add: sand_def)

subsection \<open>Atoms\<close>

text \<open>Atoms are abstract expressions: each has finitely many dimensions and a three-valued
  interpretation on keys, reading only those dimensions and strict in them (an error where one
  is missing); negation (an involution, interpreted pointwise); a constant true atom; and
  coarsening to a set of dimensions, which keeps only those dimensions, is implied at the cut
  of every key (so holds there if the original does, and adds no errors), and leaves atoms
  inside the target alone.\<close>

typedecl atom

consts
  adims :: "atom \<Rightarrow> dim fset"
  aeval :: "atom \<Rightarrow> key \<rightarrow> tr"
  aneg :: "atom \<Rightarrow> atom"
  atop :: atom
  acrs :: "dim set \<Rightarrow> atom \<Rightarrow> atom"

axiomatization where
  aeval_dims: "aeval a oo tcut (fset (adims a)) = aeval a"
  and aeval_strict: "aeval a\<cdot>t \<noteq> \<bottom> \<Longrightarrow> fset (adims a) \<subseteq> tsupp t"
  and aeval_aneg: "aeval (aneg a) = neg oo aeval a"
  and adims_aneg [simp]: "adims (aneg a) = adims a"
  and aneg_aneg [simp]: "aneg (aneg a) = a"
  and aeval_atop [simp]: "aeval atop = (\<Lambda> _. TT)"
  and adims_atop [simp]: "adims atop = {||}"
  and adims_acrs: "fset (adims (acrs A a)) \<subseteq> fset (adims a) \<inter> A"
  and acrs_cut: "sand\<cdot>(aeval a\<cdot>u)\<cdot>(aeval (acrs A a)\<cdot>(tcut A\<cdot>u)) = aeval a\<cdot>u"
  and acrs_inside: "fset (adims a) \<subseteq> A \<Longrightarrow> acrs A a = a"

lemma aeval_tcut: "fset (adims a) \<subseteq> D \<Longrightarrow> aeval a\<cdot>(tcut D\<cdot>t) = aeval a\<cdot>t"
proof -
  assume D: "fset (adims a) \<subseteq> D"
  have "tcut (fset (adims a))\<cdot>(tcut D\<cdot>t) = tcut (fset (adims a))\<cdot>t"
    using D by (intro tuple_eqI) (auto simp: tcut_tget)
  then show ?thesis by (metis aeval_dims cfcomp2)
qed


subsection \<open>Syntax and semantics\<close>

datatype filt = Atom atom | Conj filt filt | Disj filt filt | Neg filt

definition ftop where "ftop = Atom atop"
definition fbot where "fbot = Atom (aneg atop)"

primrec sdim :: "filt \<Rightarrow> dim fset" where
  "sdim (Atom a) = adims a"
| "sdim (Conj a b) = sdim a |\<union>| sdim b"
| "sdim (Disj a b) = sdim a |\<union>| sdim b"
| "sdim (Neg a) = sdim a"

text \<open>Strict evaluation of a filter at a key; it selects the keys where it is true.\<close>

primrec teval :: "filt \<Rightarrow> key \<rightarrow> tr" where
  "teval (Atom a) = aeval a"
| "teval (Conj a b) = (\<Lambda> t. sand\<cdot>(teval a\<cdot>t)\<cdot>(teval b\<cdot>t))"
| "teval (Disj a b) = (\<Lambda> t. sor\<cdot>(teval a\<cdot>t)\<cdot>(teval b\<cdot>t))"
| "teval (Neg a) = (\<Lambda> t. neg\<cdot>(teval a\<cdot>t))"

definition fsel :: "filt \<Rightarrow> key sel" where
  "fsel f = holds (teval f)"

lemma fsel_rows: "t \<in> sel_rows (fsel f) \<longleftrightarrow> teval f\<cdot>t = TT"
  by (simp add: fsel_def holds.rep_eq)

lemma fsel_conj: "fsel (Conj a b) = inf (fsel a) (fsel b)"
  by (rule sel_eqI) (simp add: fsel_rows inf_sel.rep_eq)

lemma fsel_ftop: "fsel ftop = top"
  by (simp add: fsel_def ftop_def)

text \<open>A filter reads only its dimensions, and strictness lifts from its atoms: it is defined
  only where all of them are.\<close>

lemma teval_tcut: "fset (sdim f) \<subseteq> D \<Longrightarrow> teval f\<cdot>(tcut D\<cdot>t) = teval f\<cdot>t"
  by (induct f) (simp_all add: aeval_tcut)

lemma teval_strict: "teval f\<cdot>t \<noteq> \<bottom> \<Longrightarrow> fset (sdim f) \<subseteq> tsupp t"
  by (induct f) (auto dest: aeval_strict)


subsection \<open>Coarsening\<close>

text \<open>Coarsening coarsens literals and dualizes the connectives under negation.\<close>

function crs :: "dim set \<Rightarrow> filt \<Rightarrow> filt" where
  "crs A (Atom a) = Atom (acrs A a)"
| "crs A (Conj a b) = Conj (crs A a) (crs A b)"
| "crs A (Disj a b) = Disj (crs A a) (crs A b)"
| "crs A (Neg (Atom a)) = Atom (acrs A (aneg a))"
| "crs A (Neg (Conj a b)) = Disj (crs A (Neg a)) (crs A (Neg b))"
| "crs A (Neg (Disj a b)) = Conj (crs A (Neg a)) (crs A (Neg b))"
| "crs A (Neg (Neg a)) = crs A a"
  by pat_completeness auto
termination by (relation "measure (\<lambda>(A, f). size f)") auto

lemma crs_ftop [simp]: "crs A ftop = ftop"
  by (simp add: ftop_def acrs_inside)

lemma crs_neg_ftop [simp]: "crs A (Neg ftop) = fbot"
  by (simp add: fbot_def ftop_def acrs_inside)

lemma crs_fbot [simp]: "crs A fbot = fbot"
  by (simp add: fbot_def acrs_inside)

lemma crs_neg_fbot [simp]: "crs A (Neg fbot) = ftop"
  by (simp add: fbot_def ftop_def acrs_inside)

subsection \<open>The De Morgan congruence\<close>

text \<open>The least congruence generated by the \<^emph>\<open>regular\<close> De Morgan lattice laws: those whose two
  sides mention the same atoms.  Absorption (and the annihilators it derives) would change the
  atoms, hence the dimensions a filter is written with, on which strict evaluation depends.
  The result is a De Morgan bisemilattice: conjunction and disjunction induce different orders.
  The law set is closed under duality, which coarsening under negation needs.\<close>

inductive feq :: "filt \<Rightarrow> filt \<Rightarrow> bool" (infix \<open>\<approx>\<close> 50) where
  refl: "a \<approx> a"
| sym: "a \<approx> b \<Longrightarrow> b \<approx> a"
| trans: "a \<approx> b \<Longrightarrow> b \<approx> c \<Longrightarrow> a \<approx> c"
| conj_cong: "a \<approx> a' \<Longrightarrow> b \<approx> b' \<Longrightarrow> Conj a b \<approx> Conj a' b'"
| disj_cong: "a \<approx> a' \<Longrightarrow> b \<approx> b' \<Longrightarrow> Disj a b \<approx> Disj a' b'"
| neg_cong: "a \<approx> a' \<Longrightarrow> Neg a \<approx> Neg a'"
| conj_assoc: "Conj (Conj a b) c \<approx> Conj a (Conj b c)"
| disj_assoc: "Disj (Disj a b) c \<approx> Disj a (Disj b c)"
| conj_comm: "Conj a b \<approx> Conj b a"
| disj_comm: "Disj a b \<approx> Disj b a"
| conj_idem: "Conj a a \<approx> a"
| disj_idem: "Disj a a \<approx> a"
| conj_distrib: "Conj a (Disj b c) \<approx> Disj (Conj a b) (Conj a c)"
| disj_distrib: "Disj a (Conj b c) \<approx> Conj (Disj a b) (Disj a c)"
| conj_top: "Conj a ftop \<approx> a"
| disj_bot: "Disj a fbot \<approx> a"
| neg_neg: "Neg (Neg a) \<approx> a"
| neg_atom: "Neg (Atom a) \<approx> Atom (aneg a)"
| neg_conj: "Neg (Conj a b) \<approx> Disj (Neg a) (Neg b)"
| neg_disj: "Neg (Disj a b) \<approx> Conj (Neg a) (Neg b)"

lemma equivp_feq: "equivp (\<approx>)"
  by (intro equivpI reflpI sympI transpI) (blast intro: feq.intros)+

text \<open>Evaluation and coarsening respect the congruence, coarsening also under negation (which the
  \<open>neg_cong\<close> case needs); the dimensions written respect it outright.\<close>

lemma teval_feq: "a \<approx> a' \<Longrightarrow> teval a = teval a'"
  by (induct rule: feq.induct)
    (auto simp: cfun_eq_iff sand_ac sor_ac sand_idem sor_idem sand_TT sor_FF neg_sand neg_sor
      ftop_def fbot_def aeval_aneg intro: sand_sor_distrib sor_sand_distrib)

lemma fsel_feq: "a \<approx> a' \<Longrightarrow> fsel a = fsel a'"
  by (simp add: fsel_def teval_feq)

lemma crs_feq:
  assumes "a \<approx> a'"
  shows "crs A a \<approx> crs A a'" and "crs A (Neg a) \<approx> crs A (Neg a')"
  using assms
  by (induct rule: feq.induct) (auto intro: feq.intros)

lemma fset_sdim_feq: "a \<approx> a' \<Longrightarrow> fset (sdim a) = fset (sdim a')"
  by (induct rule: feq.induct) (auto simp: ftop_def fbot_def)

subsection \<open>Coarsening: dimensions, errors, and the projection\<close>

text \<open>Coarsening keeps only target dimensions, never adds errors, and holds at least on the
  projection.\<close>

lemma crs_sdim: "fset (sdim (crs A f)) \<subseteq> fset (sdim f) \<inter> A"
  by (induct A f rule: crs.induct) (auto dest: adims_acrs[THEN subsetD])

lemma crs_cut: "sand\<cdot>(teval f\<cdot>u)\<cdot>(teval (crs A f)\<cdot>(tcut A\<cdot>u)) = teval f\<cdot>u"
proof (induct A f rule: crs.induct)
  case (1 A a) show ?case by (simp add: acrs_cut)
next
  case (4 A a) show ?case using acrs_cut[of "aneg a" u A] by (simp add: aeval_aneg)
qed (auto simp: sand_left_iff)

lemma crs_holds: "teval f\<cdot>u = TT \<Longrightarrow> teval (crs A f)\<cdot>(tcut A\<cdot>u) = TT"
  using crs_cut[of f u A] by (simp add: sand_left_iff)

subsection \<open>Slices: the quotient\<close>

quotient_type slice = filt / feq
  by (rule equivp_feq)

instantiation slice :: "{inf, sup, bot, top, uminus}"
begin

lift_definition inf_slice :: "slice \<Rightarrow> slice \<Rightarrow> slice" is Conj by (rule feq.conj_cong)
lift_definition sup_slice :: "slice \<Rightarrow> slice \<Rightarrow> slice" is Disj by (rule feq.disj_cong)
lift_definition uminus_slice :: "slice \<Rightarrow> slice" is Neg by (rule feq.neg_cong)
lift_definition top_slice :: slice is ftop .
lift_definition bot_slice :: slice is fbot .

instance ..

end

interpretation slice_conj: semilattice_neutr "inf :: slice \<Rightarrow> slice \<Rightarrow> slice" top
  by unfold_locales (transfer, rule feq.conj_assoc feq.conj_comm feq.conj_idem feq.conj_top)+

subsection \<open>Selections, dimensions and coarsening of slices\<close>

lift_definition slice_ssel :: "slice \<Rightarrow> key sel" is fsel by (rule fsel_feq)

lift_definition slice_dims :: "slice \<Rightarrow> dim set" is "\<lambda>f. fset (sdim f)" by (rule fset_sdim_feq)

lift_definition slice_coarsen :: "dim set \<Rightarrow> slice \<Rightarrow> slice" is crs by (rule crs_feq)

text \<open>Selections are a lifted type too, so \<open>transfer\<close> on goals mentioning their constants
  alone (\<open>\<top>\<close>) gets confused; those go via the abstraction equations instead.\<close>

interpretation slice_ssel: semilattice_hom "inf :: slice \<Rightarrow> slice \<Rightarrow> slice" top inf top slice_ssel
proof unfold_locales
  show "slice_ssel (inf a b) = inf (slice_ssel a) (slice_ssel b)" for a b
    by transfer (rule fsel_conj)
  show "slice_ssel top = top" by (simp add: top_slice_def slice_ssel.abs_eq fsel_ftop)
qed

interpretation slice_dims: semilattice_hom "inf :: slice \<Rightarrow> slice \<Rightarrow> slice" top sup bot slice_dims
  by unfold_locales (transfer, simp add: ftop_def)+

subsection \<open>Dimensioning\<close>

text \<open>Coarsening a representative inside the target gives it back up to the congruence.\<close>

lemma crs_inside: "fset (sdim r) \<subseteq> A \<Longrightarrow> crs A r \<approx> r \<and> crs A (Neg r) \<approx> Neg r"
proof (induct r)
  case (Atom a)
  then show ?case by (simp add: acrs_inside feq.refl feq.sym[OF feq.neg_atom])
next
  case (Conj a b)
  then have a: "crs A a \<approx> a" "crs A (Neg a) \<approx> Neg a"
    and b: "crs A b \<approx> b" "crs A (Neg b) \<approx> Neg b" by auto
  show ?case
    using feq.conj_cong[OF a(1) b(1)]
      feq.trans[OF feq.disj_cong[OF a(2) b(2)] feq.sym[OF feq.neg_conj]]
    by simp
next
  case (Disj a b)
  then have a: "crs A a \<approx> a" "crs A (Neg a) \<approx> Neg a"
    and b: "crs A b \<approx> b" "crs A (Neg b) \<approx> Neg b" by auto
  show ?case
    using feq.disj_cong[OF a(1) b(1)]
      feq.trans[OF feq.conj_cong[OF a(2) b(2)] feq.sym[OF feq.neg_disj]]
    by simp
next
  case (Neg a)
  then have a: "crs A a \<approx> a" "crs A (Neg a) \<approx> Neg a" by auto
  show ?case using a(2) feq.trans[OF a(1) feq.sym[OF feq.neg_neg]] by simp
qed

text \<open>The slice-level facts.\<close>

lemma slice_ssel_dims:
  "t \<in> sel_rows (slice_ssel s) \<Longrightarrow> tcut (slice_dims s)\<cdot>t \<in> sel_rows (slice_ssel s)"
  by transfer (simp add: fsel_rows teval_tcut)

lemma slice_ssel_total: "t \<in> sel_rows (slice_ssel s) \<Longrightarrow> slice_dims s \<subseteq> tsupp t"
  by transfer (simp add: fsel_rows teval_strict)

lemma slice_coarsen_conj:
  "slice_coarsen A (inf a b) = inf (slice_coarsen A a) (slice_coarsen A b)"
  by transfer (simp add: feq.refl)

lemma slice_coarsen_inside: "slice_dims s \<subseteq> A \<Longrightarrow> slice_coarsen A s = s"
  by transfer (simp add: crs_inside)

lemma slice_dims_coarsen: "slice_dims (slice_coarsen A s) \<subseteq> slice_dims s \<inter> A"
  by transfer (rule crs_sdim)

lemma slice_coarsen_cut:
  "t \<in> sel_rows (slice_ssel f) \<Longrightarrow> tcut A\<cdot>t \<in> sel_rows (slice_ssel (slice_coarsen A f))"
  by transfer (simp add: fsel_rows crs_holds)

text \<open>The toy slices form a slicer.\<close>

interpretation toy: slicer "inf :: slice \<Rightarrow> slice \<Rightarrow> slice" top slice_ssel slice_dims slice_coarsen
  by unfold_locales
    (fact slice_ssel_dims slice_ssel_total slice_coarsen_conj slice_coarsen_inside
      slice_dims_coarsen slice_coarsen_cut)+

end

