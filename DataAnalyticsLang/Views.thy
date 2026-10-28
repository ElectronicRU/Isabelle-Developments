theory Views
  imports Schema
begin

default_sort "{bifinite, distributive_cpo}"

section \<open>Views and functional dependencies\<close>

text \<open>A \<^emph>\<open>view\<close> reads a section of the row and a part of its key: a pair of a column-side and a
  key-side semi-factor.  Functional dependencies between views cover all four combinations of
  sides (columns to columns, columns to keys, keys to columns, keys to keys) at once.  The key of a
  row is computed from a declared column support, so columns-to-keys dependencies hold on every
  set of rows; the others are properties of datasets.\<close>

type_synonym ('r, 'k) view = "'r semi_factor \<times> 'k semi_factor"

text \<open>Projecting a pair of a row and a key onto a view's parts.\<close>

definition pproj :: "('r, 'k) view \<Rightarrow> 'r \<times> 'k \<rightarrow> 'r \<times> 'k" where
  "pproj v = (\<Lambda> p. (fst p \<downharpoonright> fst v, proj (snd v)\<cdot>(snd p)))"

lemma pproj_apply [simp]: "pproj v\<cdot>(r, k) = (r \<downharpoonright> fst v, proj (snd v)\<cdot>k)"
  by (simp add: pproj_def)

text \<open>A keying computes keys from rows and declares the column support of each key part.\<close>

record ('r, 'k) keying =
  key_fun :: "'r \<rightarrow> 'k"
  key_supp :: "'k semi_factor \<Rightarrow> 'r semi_factor"

hide_const (open) keying.truncate

locale keyed =
  fixes keying :: "('r::{domain, lod_domain}, 'k::lod_domain) keying"
  assumes csupp_reads: "proj a\<cdot>(key_fun keying\<cdot>(x \<downharpoonright> key_supp keying a)) = proj a\<cdot>(key_fun keying\<cdot>x)"
    and csupp_bot: "key_supp keying \<bottom> = \<bottom>"
    and csupp_sup: "key_supp keying (a \<squnion> b) = key_supp keying a \<squnion> key_supp keying b"
    and csupp_compact: "compact a \<Longrightarrow> compact (key_supp keying a)"
begin

abbreviation rkey :: "'r \<rightarrow> 'k" where "rkey \<equiv> key_fun keying"
abbreviation csupp :: "'k semi_factor \<Rightarrow> 'r semi_factor" where "csupp \<equiv> key_supp keying"

abbreviation rproj :: "'k semi_factor \<Rightarrow> 'r \<Rightarrow> 'k" where
  "rproj a x \<equiv> proj a\<cdot>(rkey\<cdot>x)"

definition vpart :: "('r, 'k) view \<Rightarrow> 'r \<Rightarrow> 'r \<times> 'k" where
  "vpart v x = (x \<downharpoonright> fst v, rproj (snd v) x)"

lemma vpart_pair [simp]: "vpart (c, a) x = (x \<downharpoonright> c, rproj a x)"
  by (simp add: vpart_def)

text \<open>A view part projects onto the parts of smaller views.\<close>

lemma vpart_pproj: "v \<sqsubseteq> w \<Longrightarrow> pproj v\<cdot>(vpart w x) = vpart v x"
  by (simp add: vpart_def below_prod_def proj_le)

text \<open>A key part is read off any section covering its support.\<close>

lemma rproj_section: "csupp a \<sqsubseteq> c \<Longrightarrow> rproj a (y \<downharpoonright> c) = rproj a y"
  by (metis csupp_reads proj_le)

lemma csupp_mono: "a \<sqsubseteq> b \<Longrightarrow> csupp a \<sqsubseteq> csupp b"
  by (metis csupp_sup join_absorb lattice_join_ge1)

subsection \<open>Dependencies on a set of rows\<close>

text \<open>A view determines a function on a set of rows when the function is monotone in the view
  there: a row reading less on the view gives less.  On all rows this makes the function factor
  continuously through the view; in particular rows agreeing on the view agree on the function.  A
  dependency between views is the case where the function is the other view.\<close>

definition determines :: "'r set \<Rightarrow> ('r, 'k) view \<Rightarrow> ('r \<rightarrow> 'b::cpo) \<Rightarrow> bool" where
  "determines P v g \<longleftrightarrow> (\<forall>x\<in>P. \<forall>y\<in>P. vpart v x \<sqsubseteq> vpart v y \<longrightarrow> g\<cdot>x \<sqsubseteq> g\<cdot>y)"

text \<open>The view part as a continuous function, for dependencies between views.\<close>

definition vproj :: "('r, 'k) view \<Rightarrow> 'r \<rightarrow> 'r \<times> 'k" where
  "vproj v = (\<Lambda> x. vpart v x)"

lemma vproj_apply [simp]: "vproj v\<cdot>x = vpart v x"
  by (simp add: vproj_def vpart_def)

abbreviation vfd :: "'r set \<Rightarrow> ('r, 'k) view \<Rightarrow> ('r, 'k) view \<Rightarrow> bool" where
  "vfd P v w \<equiv> determines P v (vproj w)"

lemma determines_belowD:
  "determines P v g \<Longrightarrow> x \<in> P \<Longrightarrow> y \<in> P \<Longrightarrow> vpart v x \<sqsubseteq> vpart v y \<Longrightarrow> g\<cdot>x \<sqsubseteq> g\<cdot>y"
  unfolding determines_def vproj_apply by blast

lemma determinesD: "determines P v g \<Longrightarrow> x \<in> P \<Longrightarrow> y \<in> P \<Longrightarrow> vpart v x = vpart v y \<Longrightarrow> g\<cdot>x = g\<cdot>y"
  by (rule below_antisym) (simp_all add: determines_belowD)

lemma vfdD: "vfd P v w \<Longrightarrow> x \<in> P \<Longrightarrow> y \<in> P \<Longrightarrow> vpart v x = vpart v y \<Longrightarrow> vpart w x = vpart w y"
  using determinesD[of P v "vproj w" x y] by simp

lemma determines_subset: "determines P v g \<Longrightarrow> Q \<subseteq> P \<Longrightarrow> determines Q v g"
  unfolding determines_def vproj_apply by blast

lemma determines_trans: "vfd P u v \<Longrightarrow> determines P v g \<Longrightarrow> determines P u g"
  unfolding determines_def vproj_apply by blast

lemma vpart_below_iff: "vpart (c, a) x \<sqsubseteq> vpart (c, a) y \<longleftrightarrow> x \<downharpoonright> c \<sqsubseteq> y \<downharpoonright> c \<and> rproj a x \<sqsubseteq> rproj a y"
  by (simp add: below_prod_def)

lemma determines_key: "determines P (c, a) (h oo proj a oo rkey)"
  unfolding determines_def vproj_apply by (simp add: vpart_below_iff monofun_cfun_arg)

lemma determines_comp:
  assumes g: "determines P v g"
  shows "determines P v (h oo g)"
  unfolding determines_def vproj_apply
  using determines_belowD[OF g] by (simp add: monofun_cfun_arg)

lemma determines_pair:
  assumes f: "determines P v f" and g: "determines P v g"
  shows "determines P v (\<Lambda> x. h\<cdot>(f\<cdot>x)\<cdot>(g\<cdot>x))"
  unfolding determines_def vproj_apply
  using determines_belowD[OF f] determines_belowD[OF g] by (simp add: monofun_cfun)

lemma determines_prod:
  assumes f: "determines P v f" and g: "determines P v g"
  shows "determines P v (\<Lambda> x. (f\<cdot>x, g\<cdot>x))"
  unfolding determines_def vproj_apply
  using determines_belowD[OF f] determines_belowD[OF g] by (simp add: below_prod_def)

text \<open>Views are ordered structurally, as a product: a larger view reads more.\<close>

lemma vpart_le:
  assumes le: "v \<sqsubseteq> w" and below: "vpart w x \<sqsubseteq> vpart w y"
  shows "vpart v x \<sqsubseteq> vpart v y"
proof -
  have c: "x \<downharpoonright> fst w \<sqsubseteq> y \<downharpoonright> fst w" and k: "rproj (snd w) x \<sqsubseteq> rproj (snd w) y"
    using below by (simp_all add: vpart_def below_prod_def)
  have "x \<downharpoonright> fst v \<sqsubseteq> y \<downharpoonright> fst v"
    using monofun_cfun_arg[OF c, of "proj (fst v)"] le by (simp add: below_prod_def proj_le)
  moreover have "rproj (snd v) x \<sqsubseteq> rproj (snd v) y"
    using monofun_cfun_arg[OF k, of "proj (snd v)"] le by (simp add: below_prod_def proj_le)
  ultimately show ?thesis by (simp add: vpart_def below_prod_def)
qed

lemma vfd_refl: "w \<sqsubseteq> v \<Longrightarrow> vfd P v w"
  unfolding determines_def vproj_apply by (blast intro: vpart_le)

lemma determines_mono: "determines P v g \<Longrightarrow> v \<sqsubseteq> w \<Longrightarrow> determines P w g"
  by (rule determines_trans[OF vfd_refl])

text \<open>Projections to two LODs below a third join monotonically.\<close>

lemma proj_sup_mono:
  fixes x y :: "'a::{bifinite, distributive_cpo}"
  assumes "proj a\<cdot>x \<sqsubseteq> proj a\<cdot>y" and "proj b\<cdot>x \<sqsubseteq> proj b\<cdot>y"
  shows "proj (a \<squnion> b)\<cdot>x \<sqsubseteq> proj (a \<squnion> b)\<cdot>y"
proof -
  have ub: "proj a\<cdot>y \<sqsubseteq> proj a\<cdot>y \<squnion> proj b\<cdot>y" "proj b\<cdot>y \<sqsubseteq> proj a\<cdot>y \<squnion> proj b\<cdot>y"
    using join_is_lub[OF proj_below proj_below, of a y b, THEN is_lubD1, THEN is_ubD] by simp_all
  show ?thesis unfolding proj_sup
    by (rule join_belowI) (rule below_trans[OF assms(1) ub(1)], rule below_trans[OF assms(2) ub(2)])
qed

lemma vpart_join:
  assumes v: "vpart v x \<sqsubseteq> vpart v y" and w: "vpart w x \<sqsubseteq> vpart w y"
  shows "vpart (v \<squnion> w) x \<sqsubseteq> vpart (v \<squnion> w) y"
proof -
  have "x \<downharpoonright> fst v \<sqsubseteq> y \<downharpoonright> fst v" "x \<downharpoonright> fst w \<sqsubseteq> y \<downharpoonright> fst w"
    "rproj (snd v) x \<sqsubseteq> rproj (snd v) y" "rproj (snd w) x \<sqsubseteq> rproj (snd w) y"
    using v w by (simp_all add: vpart_def below_prod_def)
  then show ?thesis unfolding vpart_def lattice_join_prod fst_conv snd_conv below_prod_def
    by (simp add: proj_sup_mono)
qed

lemma vfd_sup: "vfd P u v \<Longrightarrow> vfd P u w \<Longrightarrow> vfd P u (v \<squnion> w)"
  unfolding determines_def vproj_apply by (blast intro: vpart_join)

text \<open>Columns-to-keys dependencies are a matter of computation.\<close>

lemma vfd_support: "csupp a \<sqsubseteq> c \<Longrightarrow> vfd P (c, \<bottom>) (\<bottom>, a)"
  unfolding determines_def vproj_apply
proof (intro ballI impI)
  fix x y assume le: "csupp a \<sqsubseteq> c" and below: "vpart (c, \<bottom>) x \<sqsubseteq> vpart (c, \<bottom>) y"
  have "x \<downharpoonright> c \<sqsubseteq> y \<downharpoonright> c" using below by (simp add: vpart_below_iff)
  then have "rproj a (x \<downharpoonright> c) \<sqsubseteq> rproj a (y \<downharpoonright> c)" by (rule monofun_cfun_arg[OF monofun_cfun_arg])
  then have "rproj a x \<sqsubseteq> rproj a y" by (simp only: rproj_section[OF le])
  then show "vpart (\<bottom>, a) x \<sqsubseteq> vpart (\<bottom>, a) y" by (simp add: vpart_below_iff proj_bot)
qed

subsection \<open>The key part, the section, and the determination order\<close>

text \<open>The key part of a view drops its column part: it is the meet with the fixed view \<open>(\<bottom>, \<top>)\<close>,
  so it is below the view and preserves joins.  The section of a view is the pure-column view
  reading the columns and the declared support of the key part.  Views are also preordered
  semantically, by \<^emph>\<open>determination\<close> on all rows: the structural order implies it, the key part
  is below the view and the section above it.  On pure-column views the two orders agree.\<close>

definition vkey :: "('r, 'k) view \<Rightarrow> ('r, 'k) view" where
  "vkey v = (\<bottom>, snd v)"

definition vsec :: "('r, 'k) view \<Rightarrow> ('r, 'k) view" where
  "vsec v = (fst v \<squnion> csupp (snd v), \<bottom>)"

definition vdet :: "('r, 'k) view \<Rightarrow> ('r, 'k) view \<Rightarrow> bool" (infix \<open>\<preceq>\<close> 50) where
  "v \<preceq> w \<longleftrightarrow> vfd UNIV w v"

lemma vkey_meet: "vkey v = v \<sqinter> (\<bottom>, lattice_top)"
  by (simp add: vkey_def prod_meet lattice_meet_commute[of _ lattice_top] lattice_meet_top_left)

lemma vkey_below: "vkey v \<sqsubseteq> v"
  by (simp add: vkey_def below_prod_def)

lemma vkey_idem [simp]: "vkey (vkey v) = vkey v"
  by (simp add: vkey_def)

lemma vkey_join: "vkey (v \<squnion> w) = vkey v \<squnion> vkey w"
  by (simp add: vkey_def lattice_join_prod)

lemma vsec_idem [simp]: "vsec (vsec v) = vsec v"
  by (simp add: vsec_def csupp_bot)

lemma vdet_refl [simp]: "v \<preceq> v"
  unfolding vdet_def by (rule vfd_refl) simp

lemma vdet_trans: "u \<preceq> v \<Longrightarrow> v \<preceq> w \<Longrightarrow> u \<preceq> w"
  unfolding vdet_def by (rule determines_trans)

lemma below_vdet: "v \<sqsubseteq> w \<Longrightarrow> v \<preceq> w"
  unfolding vdet_def by (rule vfd_refl)

lemma vdet_vfd: "v \<preceq> w \<Longrightarrow> vfd P w v"
  unfolding vdet_def by (erule determines_subset) simp

lemma determines_vdet: "determines P v g \<Longrightarrow> v \<preceq> w \<Longrightarrow> determines P w g"
  by (rule determines_trans[OF vdet_vfd])

lemma vkey_vdet: "vkey v \<preceq> v"
  by (rule below_vdet[OF vkey_below])

lemma vdet_vsec: "v \<preceq> vsec v"
  unfolding vdet_def determines_def vproj_apply
proof (intro ballI impI)
  fix x y assume below: "vpart (vsec v) x \<sqsubseteq> vpart (vsec v) y"
  let ?s = "fst v \<squnion> csupp (snd v)"
  have s: "x \<downharpoonright> ?s \<sqsubseteq> y \<downharpoonright> ?s" using below by (simp add: vsec_def vpart_def below_prod_def)
  have "x \<downharpoonright> fst v \<sqsubseteq> y \<downharpoonright> fst v"
    using monofun_cfun_arg[OF s, of "proj (fst v)"] by (simp add: proj_le lattice_join_ge1)
  moreover have "rproj (snd v) x \<sqsubseteq> rproj (snd v) y"
  proof -
    have le: "csupp (snd v) \<sqsubseteq> ?s" by (rule lattice_join_ge2)
    have "rproj (snd v) (x \<downharpoonright> ?s) \<sqsubseteq> rproj (snd v) (y \<downharpoonright> ?s)" by (rule monofun_cfun_arg[OF monofun_cfun_arg[OF s]])
    then show ?thesis by (simp only: rproj_section[OF le])
  qed
  ultimately show "vpart v x \<sqsubseteq> vpart v y" by (simp add: vpart_def below_prod_def)
qed

text \<open>Factoring: a continuous function determined by a view on all rows factors continuously
  through the view's section, which rows realise (a section of a row is a row).\<close>

theorem determines_factor:
  assumes "determines UNIV v f"
  shows "f = f oo proj (fst v \<squnion> csupp (snd v))"
proof (rule cfun_eqI)
  fix x
  let ?s = "fst v \<squnion> csupp (snd v)"
  have p: "vsec v = (?s, \<bottom>)" by (rule vsec_def)
  have s: "determines UNIV (?s, \<bottom>) f"
    using determines_vdet[OF assms vdet_vsec] unfolding p .
  have "vpart (?s, \<bottom>) (x \<downharpoonright> ?s) = vpart (?s, \<bottom>) x" by (simp add: proj_bot)
  then have "f\<cdot>(x \<downharpoonright> ?s) = f\<cdot>x" by (rule determinesD[OF s UNIV_I UNIV_I])
  then show "f\<cdot>x = (f oo proj ?s)\<cdot>x" by (simp only: cfcomp2)
qed

text \<open>In general a function factors continuously through the view's parts, read as a pair, into
  the values with a top adjoined: the least upper bound of what rows reading at most a given pair
  give (a left Kan extension along the view part).  For a compact view it is continuous and reads
  only the view's parts of its argument; on view parts it is the function, if the view determines
  it.\<close>

definition vfactor_set :: "('r, 'k) view \<Rightarrow> ('r \<rightarrow> 'b::bounded_complete) \<Rightarrow> 'r \<times> 'k \<Rightarrow> 'b top set" where
  "vfactor_set v f p = {down\<cdot>(f\<cdot>x) |x. vpart v x \<sqsubseteq> p}"

definition vfactor :: "('r, 'k) view \<Rightarrow> ('r \<rightarrow> 'b::bounded_complete) \<Rightarrow> 'r \<times> 'k \<rightarrow> 'b top" where
  "vfactor v f = (\<Lambda> p. lub (vfactor_set v f p))"

lemma compact_vpart: "compact v \<Longrightarrow> compact x \<Longrightarrow> compact (vpart v x)"
  by (simp add: vpart_def compact_proj_compact proj_compact[OF compact_snd])

lemma lattice_lub_max: "x \<in> S \<Longrightarrow> (\<And>y. y \<in> S \<Longrightarrow> y \<sqsubseteq> x) \<Longrightarrow> lub S = (x :: 'a::lattice_complete)"
  by (rule below_antisym) (blast intro: lattice_lub_least is_ubI, rule lattice_lub_upper)

lemma vfactor_beta:
  fixes f :: "'r \<rightarrow> 'b::bounded_complete"
  assumes cv: "compact v"
  shows "vfactor v f\<cdot>p = lub (vfactor_set v f p)"
  unfolding vfactor_def
proof (rule beta_cfun)
  let ?G = "\<lambda>p. lub (vfactor_set v f p)"
  have mono: "?G p \<sqsubseteq> ?G q" if "p \<sqsubseteq> q" for p q
    by (rule lattice_lub_least, rule is_ubI, rule lattice_lub_upper)
      (auto simp: vfactor_set_def intro: below_trans[OF _ that])
  obtain A :: "nat \<Rightarrow> 'r \<rightarrow> 'r" where A: "approx_chain A" using bifinite by blast
  have app: "x = (\<Squnion>j. A j\<cdot>x)" for x
    using approx_chain.lub_approx[OF A] approx_chain.chain_approx[OF A]
    by (metis ID1 contlub_cfun_fun)
  have chain_bound: "?G (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. ?G (Y i))" if Y: "chain Y" for Y
  proof (rule lattice_lub_least, rule is_ubI)
    have GY: "chain (\<lambda>i. ?G (Y i))" using Y by (auto intro: chainI mono chainE)
    fix u assume "u \<in> vfactor_set v f (\<Squnion>i. Y i)"
    then obtain x where u: "u = down\<cdot>(f\<cdot>x)" and x: "vpart v x \<sqsubseteq> (\<Squnion>i. Y i)"
      by (auto simp: vfactor_set_def)
    have chA: "chain (\<lambda>j. A j\<cdot>x)" using approx_chain.chain_approx[OF A] by (simp add: ch2ch_Rep_cfunL)
    have each: "down\<cdot>(f\<cdot>(A j\<cdot>x)) \<sqsubseteq> (\<Squnion>i. ?G (Y i))" for j
    proof -
      have "vpart v (A j\<cdot>x) \<sqsubseteq> vpart v x"
        using monofun_cfun_arg[OF approx_chain.approx_below[OF A], of "vproj v"] by simp
      then have "vpart v (A j\<cdot>x) \<sqsubseteq> (\<Squnion>i. Y i)" using x by (rule below_trans)
      then obtain i where i: "vpart v (A j\<cdot>x) \<sqsubseteq> Y i"
        using compactD2[OF compact_vpart[OF cv approx_chain.compact_approx[OF A]] Y] by blast
      have "down\<cdot>(f\<cdot>(A j\<cdot>x)) \<sqsubseteq> ?G (Y i)"
        by (rule lattice_lub_upper) (auto simp: vfactor_set_def intro: i)
      also have "\<dots> \<sqsubseteq> (\<Squnion>i. ?G (Y i))" by (rule is_ub_thelub[OF GY])
      finally show ?thesis .
    qed
    have "u = (\<Squnion>j. down\<cdot>(f\<cdot>(A j\<cdot>x)))"
      unfolding u by (subst app[of x]) (simp add: contlub_cfun_arg chA)
    then show "u \<sqsubseteq> (\<Squnion>i. ?G (Y i))" using each by (simp add: lub_below chA)
  qed
  show "cont ?G" by (rule contI2) (auto intro: monofunI mono chain_bound)
qed

lemma vfactor_reads:
  assumes cv: "compact v"
  shows "vfactor v f\<cdot>(s, \<kappa>) = vfactor v f\<cdot>(s \<downharpoonright> fst v, proj (snd v)\<cdot>\<kappa>)"
proof -
  have "vpart v x \<sqsubseteq> (s, \<kappa>) \<longleftrightarrow> vpart v x \<sqsubseteq> (s \<downharpoonright> fst v, proj (snd v)\<cdot>\<kappa>)" for x
  proof
    assume "vpart v x \<sqsubseteq> (s, \<kappa>)"
    then have "x \<downharpoonright> fst v \<sqsubseteq> s" "rproj (snd v) x \<sqsubseteq> \<kappa>" by (simp_all add: vpart_def below_prod_def)
    then show "vpart v x \<sqsubseteq> (s \<downharpoonright> fst v, proj (snd v)\<cdot>\<kappa>)"
      using monofun_cfun_arg[of _ _ "proj (fst v)"] monofun_cfun_arg[of _ _ "proj (snd v)"]
      by (fastforce simp: vpart_def below_prod_def)
  next
    assume "vpart v x \<sqsubseteq> (s \<downharpoonright> fst v, proj (snd v)\<cdot>\<kappa>)"
    then show "vpart v x \<sqsubseteq> (s, \<kappa>)" by (rule below_trans) (simp add: below_prod_def proj_below)
  qed
  then have "vfactor_set v f (s, \<kappa>) = vfactor_set v f (s \<downharpoonright> fst v, proj (snd v)\<cdot>\<kappa>)"
    by (simp add: vfactor_set_def)
  then show ?thesis by (simp add: vfactor_beta[OF cv])
qed

theorem vfactor_vpart:
  assumes cv: "compact v" and d: "determines UNIV v f"
  shows "vfactor v f\<cdot>(vpart v x) = down\<cdot>(f\<cdot>x)"
  unfolding vfactor_beta[OF cv]
proof (rule lattice_lub_max)
  show "down\<cdot>(f\<cdot>x) \<in> vfactor_set v f (vpart v x)" by (auto simp: vfactor_set_def)
  show "u \<sqsubseteq> down\<cdot>(f\<cdot>x)" if "u \<in> vfactor_set v f (vpart v x)" for u
    using that determines_belowD[OF d] by (auto simp: vfactor_set_def)
qed

corollary vfactor_vproj:
  "compact v \<Longrightarrow> determines UNIV v f \<Longrightarrow> vfactor v f oo vproj v = down oo f"
  by (rule cfun_eqI) (simp add: vfactor_vpart)

corollary determines_factor_ex:
  "determines UNIV v f \<Longrightarrow> \<exists>h. f = h oo proj (fst v \<squnion> csupp (snd v))"
  by (blast dest: determines_factor)

text \<open>Joins: a view determined by two views' join is bounded by both; a join is the least
  upper bound up to determination.\<close>

lemma vdet_join: "u \<preceq> w \<Longrightarrow> v \<preceq> w \<Longrightarrow> u \<squnion> v \<preceq> w"
  unfolding vdet_def by (rule vfd_sup)

lemma vdet_join_mono: "u \<preceq> u' \<Longrightarrow> v \<preceq> v' \<Longrightarrow> u \<squnion> v \<preceq> u' \<squnion> v'"
  by (rule vdet_join) (blast intro: vdet_trans below_vdet lattice_join_ge1 lattice_join_ge2)+

lemma view_split: "v = (fst v, \<bottom>) \<squnion> (\<bottom>, snd v)" for v :: "('r, 'k) view"
  by (simp add: lattice_join_prod lattice_join_bot_left lattice_join_bot_right)

text \<open>A key part is \<^emph>\<open>exact\<close> when it determines its declared column support on all rows: the key
  is one-to-one with those columns.  For exact key parts the section is equivalent to the view.\<close>

definition exact_key :: "'k semi_factor \<Rightarrow> bool" where
  "exact_key a \<longleftrightarrow> (csupp a, \<bottom>) \<preceq> (\<bottom>, a)"

theorem vsec_vdet_exact:
  assumes "exact_key (snd v)"
  shows "vsec v \<preceq> v"
proof -
  have "vsec v = (fst v, \<bottom>) \<squnion> (csupp (snd v), \<bottom>)"
    by (simp add: vsec_def lattice_join_prod lattice_join_bot_left)
  moreover have "(fst v, \<bottom>) \<preceq> v" by (rule below_vdet) (simp add: below_prod_def)
  moreover have "(csupp (snd v), \<bottom>) \<preceq> v"
    using assms unfolding exact_key_def
    by (rule vdet_trans) (rule below_vdet, simp add: below_prod_def)
  ultimately show ?thesis by (simp only: vdet_join)
qed

lemma vdet_sections: "(c, \<bottom>) \<preceq> (c', \<bottom>) \<longleftrightarrow> c \<sqsubseteq> c'"
proof
  assume d: "(c, \<bottom>) \<preceq> (c', \<bottom>)"
  have "proj (c \<sqinter> c')\<cdot>x = proj c\<cdot>x" for x
  proof -
    have "vpart (c', \<bottom>) (x \<downharpoonright> c') = vpart (c', \<bottom>) x" by (simp add: proj_bot)
    then have "vpart (c, \<bottom>) (x \<downharpoonright> c') = vpart (c, \<bottom>) x"
      using d unfolding vdet_def by (blast dest: vfdD)
    then show ?thesis by (simp add: proj_inf proj_bot)
  qed
  then have "c \<sqinter> c' = c" by (simp add: cfun_eqI semi_factor_p_inject[symmetric])
  then show "c \<sqsubseteq> c'" by (metis lattice_meet_le2)
qed (simp add: below_vdet below_prod_def)

subsection \<open>Weak dependencies\<close>

text \<open>A weak dependency only holds between rows where both sides are present, as for the two
  sides of a join.  Weak dependencies do not compose with each other (the middle view may be absent
  in one row), but they compose with dependencies on either side, given that presence passes from
  the outer view to the middle one.\<close>

definition vpresent :: "('r, 'k) view \<Rightarrow> 'r \<Rightarrow> bool" where
  "vpresent v x \<longleftrightarrow> vpart v x \<noteq> \<bottom>"

definition weak_fd :: "'r set \<Rightarrow> ('r, 'k) view \<Rightarrow> ('r, 'k) view \<Rightarrow> bool" where
  "weak_fd P v w \<longleftrightarrow> (\<forall>x\<in>P. \<forall>y\<in>P. vpart v x = vpart v y \<longrightarrow> vpresent v x \<longrightarrow>
    vpresent w x \<longrightarrow> vpresent w y \<longrightarrow> vpart w x = vpart w y)"

lemma vfd_weak_fd: "vfd P v w \<Longrightarrow> weak_fd P v w"
  unfolding weak_fd_def by (blast dest: vfdD)

lemma vfd_weak_fd_trans:
  "vfd P u v \<Longrightarrow> weak_fd P v w \<Longrightarrow> (\<forall>x\<in>P. vpresent u x \<longrightarrow> vpresent v x) \<Longrightarrow> weak_fd P u w"
  unfolding weak_fd_def by (blast dest: vfdD)

lemma weak_fd_vfd_trans:
  "weak_fd P u v \<Longrightarrow> vfd P v w \<Longrightarrow> (\<forall>x\<in>P. vpresent w x \<longrightarrow> vpresent v x) \<Longrightarrow> weak_fd P u w"
  unfolding weak_fd_def by (blast dest: vfdD)

text \<open>The chase only guarantees the guarded form: equal \<^emph>\<open>maximal\<close> determinants.  It becomes a
  dependency between views when the determinant is maximal where present and the dependent part
  is absent where the determinant is.\<close>

lemma fd_vfd:
  assumes f: "fd a b P" and m: "\<forall>x\<in>P. x \<downharpoonright> a \<noteq> \<bottom> \<longrightarrow> maximal_at a (x \<downharpoonright> a)"
    and abs: "\<forall>x\<in>P. x \<downharpoonright> a = \<bottom> \<longrightarrow> x \<downharpoonright> b = \<bottom>"
  shows "vfd P (a, \<bottom>) (b, \<bottom>)"
  unfolding determines_def vproj_apply
proof (intro ballI impI)
  fix x y assume x: "x \<in> P" and y: "y \<in> P" and below: "vpart (a, \<bottom>) x \<sqsubseteq> vpart (a, \<bottom>) y"
  have le: "x \<downharpoonright> a \<sqsubseteq> y \<downharpoonright> a" using below by (simp add: vpart_below_iff)
  have "x \<downharpoonright> b \<sqsubseteq> y \<downharpoonright> b"
  proof (cases "x \<downharpoonright> a = \<bottom>")
    case True
    then show ?thesis using abs x by simp
  next
    case False
    then have mx: "maximal_at a (x \<downharpoonright> a)" using m x by blast
    have eq: "x \<downharpoonright> a = y \<downharpoonright> a" by (rule maximal_at_eq[OF mx _ le, symmetric]) simp
    show ?thesis using fdD[OF f x y mx eq] by simp
  qed
  then show "vpart (b, \<bottom>) x \<sqsubseteq> vpart (b, \<bottom>) y" by (simp add: vpart_below_iff proj_bot)
qed

end

section \<open>Dependencies over all conforming datasets\<close>

locale keyed_schema = schema rules + keyed keying
  for rules :: "'r::{domain, lod_domain} schema_rules" and keying :: "('r, 'k::lod_domain) keying"
begin

definition universally :: "('r set \<Rightarrow> bool) \<Rightarrow> bool" where
  "universally Q \<longleftrightarrow> (\<forall>X. conforms X \<longrightarrow> Q (lower_maximal X))"

lemma universallyD: "universally Q \<Longrightarrow> conforms X \<Longrightarrow> Q (lower_maximal X)"
  unfolding universally_def by blast

lemma universally_mono: "universally Q \<Longrightarrow> (\<And>P. Q P \<Longrightarrow> T P) \<Longrightarrow> universally T"
  unfolding universally_def by blast

lemma universally_mono2:
  "universally Q \<Longrightarrow> universally Q' \<Longrightarrow> (\<And>P. Q P \<Longrightarrow> Q' P \<Longrightarrow> T P) \<Longrightarrow> universally T"
  unfolding universally_def by blast

text \<open>A functional dependency of the schema holds universally between views, given maximal
  determinants and absent dependents where the determinant is absent.\<close>

lemma universally_fd_rule:
  assumes r: "fd_rule a b \<in> chase_rules"
    and m: "universally (\<lambda>P. \<forall>x\<in>P. x \<downharpoonright> a \<noteq> \<bottom> \<longrightarrow> maximal_at a (x \<downharpoonright> a))"
    and abs: "universally (\<lambda>P. \<forall>x\<in>P. x \<downharpoonright> a = \<bottom> \<longrightarrow> x \<downharpoonright> b = \<bottom>)"
  shows "universally (\<lambda>P. vfd P (a, \<bottom>) (b, \<bottom>))"
  unfolding universally_def
  using fd_vfd conforms_fd[OF _ r] universallyD[OF m] universallyD[OF abs] by blast

subsection \<open>Strong keys\<close>

text \<open>A key is \<^emph>\<open>strong\<close> when it is functionally equivalent to its column support in every
  conforming dataset; one direction holds by computation.  Strong keys transfer column dependencies
  to keys: recover the columns from the key, then compute the other key from them.\<close>

definition strong_key :: "'k semi_factor \<Rightarrow> bool" where
  "strong_key a \<longleftrightarrow> universally (\<lambda>P. vfd P (\<bottom>, a) (csupp a, \<bottom>))"

lemma strong_key_equiv:
  "strong_key a \<Longrightarrow> conforms X \<Longrightarrow>
    vfd (lower_maximal X) (\<bottom>, a) (csupp a, \<bottom>) \<and> vfd (lower_maximal X) (csupp a, \<bottom>) (\<bottom>, a)"
  unfolding strong_key_def by (auto dest: universallyD intro: vfd_support)

theorem strong_key_transfer:
  assumes a: "strong_key a" and c: "universally (\<lambda>P. vfd P (csupp a, \<bottom>) (c, \<bottom>))"
    and b: "csupp b \<sqsubseteq> c"
  shows "universally (\<lambda>P. vfd P (\<bottom>, a) (\<bottom>, b))"
  using a c unfolding strong_key_def
  by (rule universally_mono2) (blast intro: determines_trans vfd_support[OF b])

subsection \<open>Supports of content functions\<close>

text \<open>A content function reads a section of the row together with a part of its key: on all rows,
  these two (its column and key supports) determine it, which is what it depends on across
  datasets.  Within every conforming dataset the key part alone determines it, as when it reads a
  value column whose primary key is in the key.\<close>

definition fun_support :: "('r, 'k) view \<Rightarrow> ('r \<rightarrow> 'b::cpo) \<Rightarrow> bool" where
  "fun_support v f \<longleftrightarrow> determines UNIV v f \<and> universally (\<lambda>P. determines P (vkey v) f)"

text \<open>A function whose view is its own key part is \<^emph>\<open>key-pure\<close>: determined by its key part on all
  rows.  A function reading only a section is supported by any key part determining that section
  in data.\<close>

lemma fun_support_key: "fun_support (vkey v) f \<longleftrightarrow> determines UNIV (vkey v) f"
  unfolding fun_support_def universally_def vkey_idem by (blast intro: determines_subset)

text \<open>A view is \<^emph>\<open>keyed\<close> when within every conforming dataset its key part determines it; then
  every function of its parts is supported by it.\<close>

definition keyed_view :: "('r, 'k) view \<Rightarrow> bool" where
  "keyed_view v \<longleftrightarrow> universally (\<lambda>P. vfd P (vkey v) v)"

lemma keyed_view_key: "keyed_view (\<bottom>, a)"
  unfolding keyed_view_def universally_def vkey_def by (simp add: vfd_refl)

lemma keyed_view_sup: "keyed_view v \<Longrightarrow> keyed_view w \<Longrightarrow> keyed_view (v \<squnion> w)"
  unfolding keyed_view_def
proof (erule universally_mono2, assumption)
  fix P assume v: "vfd P (vkey v) v" and w: "vfd P (vkey w) w"
  have "vfd P (vkey (v \<squnion> w)) v" "vfd P (vkey (v \<squnion> w)) w"
    unfolding vkey_join by (rule determines_mono[OF v lattice_join_ge1], rule determines_mono[OF w lattice_join_ge2])
  then show "vfd P (vkey (v \<squnion> w)) (v \<squnion> w)" by (rule vfd_sup)
qed

lemma keyed_view_columns:
  assumes fd: "universally (\<lambda>P. vfd P (\<bottom>, a) (c, \<bottom>))"
  shows "keyed_view (c, a)"
proof -
  have j: "(c, a) = (c, \<bottom>) \<squnion> (\<bottom>, a)" using view_split[of "(c, a)"] by simp
  have "universally (\<lambda>P. vfd P (\<bottom>, a) ((c, \<bottom>) \<squnion> (\<bottom>, a)))"
    using fd by (rule universally_mono) (rule vfd_sup[OF _ vfd_refl[OF below_refl]])
  then show ?thesis unfolding keyed_view_def vkey_def by (simp only: j[symmetric] snd_conv)
qed

lemma keyed_view_determines:
  "keyed_view v \<Longrightarrow> conforms X \<Longrightarrow> determines (lower_maximal X) (vkey v) (h oo vproj v)"
  unfolding keyed_view_def by (blast dest: universallyD intro: determines_comp)

lemma fun_support_columns:
  assumes reads: "\<And>x. f\<cdot>(x \<downharpoonright> c) = f\<cdot>x" and ka: "universally (\<lambda>P. vfd P (\<bottom>, a) (c, \<bottom>))"
  shows "fun_support (c, a) f"
proof -
  have c: "determines P (c, \<bottom>) f" for P
    unfolding determines_def vproj_apply vpart_below_iff by (metis reads monofun_cfun_arg)
  have "determines UNIV (c, a) f"
    by (rule determines_mono[OF c]) (simp add: below_prod_def)
  moreover have "universally (\<lambda>P. determines P (\<bottom>, a) f)"
    using ka by (rule universally_mono) (rule determines_trans[OF _ c])
  ultimately show ?thesis unfolding fun_support_def vkey_def by simp
qed

end

end
