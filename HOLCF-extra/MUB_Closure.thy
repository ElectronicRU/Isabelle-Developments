theory MUB_Closure
  imports Definitions Directed
begin

(* ===================================================================== *)
(*  MUB-closure and the defl_of_set construction                         *)
(*                                                                       *)
(*  Reusable infrastructure (no mention of 'a defl / cast):              *)
(*  - mub_closed / mub_closure: closure under minimal upper bounds of    *)
(*    finite subsets, at sort 'po' (so it applies to 'a and to           *)
(*    'a compact_basis alike); a closure operator (extensive, monotone,  *)
(*    idempotent), with KEYSTONE 'mub_closure_least'.                    *)
(*  - the fixed-point set of a deflation is mub-closed, and the          *)
(*    mub-closure of a set of fixed points stays fixed.                  *)
(*  - finiteness: a finite set of compacts is fixed by one               *)
(*    finite_deflation, hence has a finite mub-closure (lifted to        *)
(*    'a compact_basis).                                                  *)
(*  - locale 'mub_closed_basis': from a mub-closed set S of compact      *)
(*    basis elements, build the deflation 'defl_of_set S' that fixes     *)
(*    exactly S (a finite_deflation when S is finite).                   *)
(*                                                                       *)
(*  The deflation-lattice / 'a defl results built on top live in         *)
(*  Deflations.thy.                                                      *)
(* ===================================================================== *)

section \<open>MUB-closure (in an arbitrary partial order)\<close>

text \<open>The following closure operators are generic over sort @{class po}, so they
  apply both to \<open>'a\<close> itself and to \<open>'a compact_basis\<close>.\<close>

definition is_mub :: "'a::po set \<Rightarrow> 'a \<Rightarrow> bool"
  where "is_mub T a \<equiv> T <| a \<and> (\<forall>b. T <| b \<longrightarrow> b \<sqsubseteq> a \<longrightarrow> b = a)"

lemma is_mubI:
  assumes "T <| a"
    and "\<And>b. T <| b \<Longrightarrow> b \<sqsubseteq> a \<Longrightarrow> b = a"
  shows "is_mub T a"
  unfolding is_mub_def using assms by simp

lemma is_mubD1: "is_mub T a \<Longrightarrow> T <| a"
  by (simp add: is_mub_def)

lemma is_mubD2: "is_mub T a \<Longrightarrow> T <| b \<Longrightarrow> b \<sqsubseteq> a \<Longrightarrow> b = a"
  by (simp add: is_mub_def)

definition mub_closed :: "'a::po set \<Rightarrow> bool"
  where "mub_closed T \<longleftrightarrow> (\<forall>S \<subseteq> T. \<forall>s. finite S \<longrightarrow> is_mub S s \<longrightarrow> s \<in> T)"

definition mub_closure :: "'a::po set \<Rightarrow> 'a set"
  where "mub_closure S = \<Inter>{T. mub_closed T \<and> S \<subseteq> T}"

lemma mub_closed_UNIV: "mub_closed UNIV"
  by (simp add: mub_closed_def)

lemma mub_closed_Inter:
  assumes "\<And>T. T \<in> \<T> \<Longrightarrow> mub_closed T"
  shows "mub_closed (\<Inter>\<T>)"
  using assms unfolding mub_closed_def by blast

lemma mub_closed_mub_closure: "mub_closed (mub_closure S)"
  unfolding mub_closure_def by (rule mub_closed_Inter) blast

lemma mub_closure_extensive: "S \<subseteq> mub_closure S"
  unfolding mub_closure_def by blast

lemma mub_closure_least: "A \<subseteq> B \<Longrightarrow> mub_closed B \<Longrightarrow> mub_closure A \<subseteq> B"
  unfolding mub_closure_def by blast

lemma mub_closure_mono: "A \<subseteq> B \<Longrightarrow> mub_closure A \<subseteq> mub_closure B"
  by (meson mub_closed_mub_closure mub_closure_extensive mub_closure_least order_trans)

lemma mub_closure_idem: "mub_closure (mub_closure S) = mub_closure S"
  by (meson mub_closed_mub_closure mub_closure_extensive mub_closure_least subset_antisym)

lemma mub_closedI:
  fixes T
  assumes "\<And>S s. finite S \<Longrightarrow> S \<subseteq> T \<Longrightarrow> is_mub S s \<Longrightarrow> s \<in> T"
  shows "mub_closed T"
  unfolding mub_closed_def
  using assms by blast

lemma mub_closedD:
  assumes "mub_closed T"
    "finite S" "S \<subseteq> T" "is_mub S s"
  shows "s \<in> T"
  using assms unfolding mub_closed_def by blast

section \<open>Fixed sets of deflations are MUB-closed\<close>

lemma is_ub_mono:
  assumes "\<And>x y. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y"
  shows "A <| a \<Longrightarrow> f ` A <| f a"
  by (auto intro: is_ubI assms dest: is_ubD)

lemma deflation_ub:
  assumes d: "deflation d"
    and fixed: "A \<subseteq> {x. d\<cdot>x = x}"
    and ub: "A <| b"
  shows "A <| d\<cdot>b"
proof -
  from d interpret deflation d .
  from monofun_cfun_arg[of _ _ d] ub have "(\<lambda>x. d\<cdot>x) ` A <| d\<cdot>b"
    by (rule is_ub_mono)
  also from fixed have "(\<lambda>x. d\<cdot>x) ` A = A" by force
  finally show ?thesis .
qed

lemma deflation_preserves_mub:
  assumes d: "deflation d" and F: "\<And>f. f \<in> F \<Longrightarrow> d \<cdot> f = f"
    and mub: "is_mub F f"
  shows "d\<cdot>f = f"
proof -
  from mub have "F <| f" by (rule is_mubD1)
  with monofun_cfun_arg have "(\<lambda>x. d\<cdot>x) ` F <| d\<cdot>f"
    by (rule is_ub_mono)
  also have "(\<lambda>x. d\<cdot>x) ` F = F" using F by (simp add: image_def)
  finally show ?thesis using deflation.below[OF d]
    by (rule mub[THEN is_mubD2])
qed

lemma deflation_fixes_mub_closed:
  assumes "deflation d"
  shows "mub_closed {x. d\<cdot>x = x}"
  using deflation_preserves_mub[OF assms]
  by (blast intro!: mub_closedI)

lemma deflation_mub_closure_fixed:
  assumes "deflation d" and "S \<subseteq> {x. d\<cdot>x = x}"
  shows "mub_closure S \<subseteq> {x. d\<cdot>x = x}"
  by (rule mub_closure_least[OF assms(2) deflation_fixes_mub_closed[OF assms(1)]])


section \<open>Finiteness of MUB-closures in bifinite domains\<close>

lemma finite_compacts_fixed:
  fixes S :: "'a::bifinite set"
  assumes finS: "finite S" and cpt: "\<And>x. x \<in> S \<Longrightarrow> compact x"
  obtains d where "finite_deflation d" and "S \<subseteq> {x. d\<cdot>x = x}"
proof -
  from bifinite obtain approx :: "nat \<Rightarrow> 'a \<rightarrow> 'a" where "approx_chain approx" ..
  then interpret approx_chain approx .
  have idem_mono: "approx j\<cdot>x = x" if ij: "i \<le> j" and fx: "approx i\<cdot>x = x" for i j x
  proof -
    have "approx i\<cdot>x \<sqsubseteq> approx j\<cdot>x"
      using ij by (rule chain_approx[THEN chain_mono, THEN monofun_cfun_fun])
    with fx have "x \<sqsubseteq> approx j\<cdot>x" by simp
    with approx_below show ?thesis by (metis below_antisym)
  qed
  have ex_i: "\<exists>i. approx i\<cdot>x = x" if "x \<in> S" for x
    using compact_eq_approx[OF cpt[OF that]] .
  obtain idx where idx: "\<And>x. x \<in> S \<Longrightarrow> approx (idx x)\<cdot>x = x"
    using ex_i by metis
  define k where "k = Max (insert 0 (idx ` S))"
  have finI: "finite (insert 0 (idx ` S))" using finS by simp
  have k_ge: "idx x \<le> k" if "x \<in> S" for x
  proof -
    have "idx x \<in> insert 0 (idx ` S)" using that by blast
    with finI show ?thesis unfolding k_def by (simp add: Max_ge)
  qed
  have fixes_k: "approx k\<cdot>x = x" if "x \<in> S" for x
    using idem_mono[OF k_ge[OF that] idx[OF that]] .
  have "finite_deflation (approx k)" by (rule finite_deflation_approx)
  moreover have "S \<subseteq> {x. approx k\<cdot>x = x}" using fixes_k by blast
  ultimately show thesis using that by blast
qed

lemma finite_mub_closure:
  fixes S :: "'a::bifinite set"
  assumes finS: "finite S" and cpt: "\<And>x. x \<in> S \<Longrightarrow> compact x"
  shows "finite (mub_closure S)" and "\<And>x. x \<in> mub_closure S \<Longrightarrow> compact x"
proof -
  obtain d where d: "finite_deflation d" and Ssub: "S \<subseteq> {x. d\<cdot>x = x}"
    by (rule finite_compacts_fixed[OF finS cpt])
  from d have defl: "deflation d" by (rule finite_deflation_imp_deflation)
  have clo_sub: "mub_closure S \<subseteq> {x. d\<cdot>x = x}"
    by (rule deflation_mub_closure_fixed[OF defl Ssub])
  have "finite {x. d\<cdot>x = x}" using d by (rule finite_deflation.finite_fixes)
  with clo_sub show "finite (mub_closure S)" by (rule finite_subset)
  show "compact x" if "x \<in> mub_closure S" for x
  proof -
    from that clo_sub have "d\<cdot>x = x" by blast
    then show "compact x" using finite_deflation.compact[OF d] by metis
  qed
qed

text \<open>Lifting the bounding results from \<open>'a\<close> to \<open>'a compact_basis\<close>.\<close>

lemma compact_mub_bound_below:
  fixes A :: "'a::bifinite set"
  assumes fin: "finite A" and compact: "\<And>a. a \<in> A \<Longrightarrow> compact a"
    and ub: "A <| b"
  obtains a where "is_mub A a" "compact a" "a \<sqsubseteq> b"
proof - 
  from fin compact obtain d where d: "finite_deflation d"
    and sub: "A \<subseteq> {x. d\<cdot>x = x}"
    using finite_compacts_fixed[of A]
    by force
  from d interpret d: finite_deflation d .
  from d.deflation_axioms sub ub have ub_db: "A <| d\<cdot>b"
    by (rule deflation_ub)
  define bounds where "bounds = {x. d\<cdot>x = x \<and> A <| x \<and> x \<sqsubseteq> b}"
  from bounds_def d.finite_fixes have "finite bounds" by auto
  moreover from ub_db d.idem d.below[of b] have "bounds \<noteq> {}"
    unfolding bounds_def by blast
  ultimately have "\<exists>m \<in> bounds. \<forall>b \<in> bounds. b \<sqsubseteq> m \<longrightarrow> m = b"
    by (rule order.finite_has_minimal[OF below_order])
  then obtain m where 1: "m \<in> bounds" 
    and 2: "\<forall>b \<in> bounds. b \<sqsubseteq> m \<longrightarrow> m = b"..
  from 1 have fixm: "d\<cdot>m = m" and ubm: "A <| m" and mleb: "m \<sqsubseteq> b"
    unfolding bounds_def by auto

  from fixm have p2: "compact m" using d.compact[of m]
    by simp
  have p1: "is_mub A m"
  proof (rule is_mubI)
    from 1 show "A <| m" by (simp add: bounds_def)
  next
    fix c assume "A <| c" "c \<sqsubseteq> m"
    from \<open>c \<sqsubseteq> m\<close> fixm monofun_cfun_arg[of c m d]
    have dclem: "d\<cdot>c \<sqsubseteq> m" by simp
    with mleb have "d\<cdot>c \<sqsubseteq> b" by (rule below_trans[rotated])
    moreover from d.deflation_axioms sub \<open>A <| c\<close> have "A <| d\<cdot>c"
      by (rule deflation_ub)
    ultimately have "d\<cdot>c \<in> bounds" unfolding bounds_def using d.idem
      by auto
    with dclem 2 have "m = d\<cdot>c" by fast
    with d.below[of c] \<open>c \<sqsubseteq> m\<close> show "c = m" by (metis below_antisym)
  qed
  from p1 p2 mleb show thesis by (rule that)
qed

lemma Rep_compact_basis_ub:
"Rep_compact_basis ` A <| Rep_compact_basis b \<longleftrightarrow> A <| b"
  unfolding is_ub_def compact_le_def by auto

lemma mub_compact_basis_bwd:
  "is_mub (Rep_compact_basis ` A) (Rep_compact_basis b) \<Longrightarrow> is_mub A b"
  unfolding is_mub_def Rep_compact_basis_ub[symmetric] compact_le_def
  using Rep_compact_basis_inject by blast 

lemma compact_mub_basis_bound_below:
  fixes A :: "'a::bifinite compact_basis set"
  assumes fin: "finite A"
    and ub: "Rep_compact_basis ` A <| b"
  obtains a where "is_mub A a" "Rep_compact_basis a \<sqsubseteq> b"
proof -
  from assms compact_mub_bound_below[of "Rep_compact_basis ` A" b]
  obtain c where "compact c"
      and mub2: "is_mub (Rep_compact_basis ` A) c"
      and cleb: "c \<sqsubseteq> b"
    by (metis Rep_compact_basis' finite_imageI imageE)
  let ?c = "Abs_compact_basis c"
  from \<open>compact c\<close> have *: "Rep_compact_basis ?c = c" by simp
  with mub2 mub_compact_basis_bwd have "is_mub A ?c" by metis
  moreover from * cleb have "Rep_compact_basis ?c \<sqsubseteq> b" by simp
  ultimately show ?thesis by (rule that)
qed

lemma mub_compact_basis_fwd:
  fixes A :: "'a::bifinite compact_basis set" and a
  assumes fin: "finite A" and mub: "is_mub A a"
  shows "is_mub (Rep_compact_basis ` A) (Rep_compact_basis a)"
proof (rule is_mubI)
  show "(Rep_compact_basis ` A) <| Rep_compact_basis a"
    using mub[THEN is_mubD1] is_ub_mono compact_le_def by metis
next
  fix b assume b: "Rep_compact_basis ` A <| b"
  with fin obtain c where
     mub2: "is_mub A c"
    and cleb: "Rep_compact_basis c \<sqsubseteq> b"
    by (rule compact_mub_basis_bound_below)
  assume blea: "b \<sqsubseteq> Rep_compact_basis a"
  with cleb compact_le_def below_trans have clea: "c \<sqsubseteq> a" by metis
  from mub2[THEN is_mubD1] have "A <| c" .
  with mub[THEN is_mubD2] clea
  have "c = a" by fast
  with cleb blea show "b = Rep_compact_basis a" by (simp add: po_eq_conv)
qed

lemma finite_mub_closure_cb:
  fixes S :: "'a::bifinite compact_basis set"
  assumes finS: "finite S"
  shows "finite (mub_closure S)"
proof -
  let ?R = Rep_compact_basis
  have inj: "inj ?R"
    by (metis compact_basis.Rep_compact_basis_inject injI)
  have cpt: "compact x" if "x \<in> ?R ` S" for x
    using that using Rep_compact_basis' by auto
  have finRS: "finite (?R ` S)" using finS by simp
  define M where "M = mub_closure (?R ` S)"
  from finite_mub_closure[OF finRS cpt]
  have finM: "finite M" and compactM: "\<And>x. x \<in> M \<Longrightarrow> compact x"
    unfolding M_def by iprover+
  let ?T = "{a. ?R a \<in> M}"
  have Ssub: "S \<subseteq> ?T"
    using mub_closure_extensive[of "?R ` S"] unfolding M_def by auto
  have Tclosed: "mub_closed ?T"
  proof (intro mub_closedI)
    fix U u assume "U \<subseteq> ?T"
    then have 1: "?R ` U \<subseteq> M" by auto
    assume fin: "finite U" and "is_mub U u"
    then have 2: "is_mub (?R ` U) (?R u)"
      by (rule mub_compact_basis_fwd)
    from M_def have "mub_closed M" by (simp add: mub_closed_mub_closure)
    from this fin 1 2 have "?R u \<in> M" using mub_closedD by blast
    thus "u \<in> ?T" by simp
  qed
  with Ssub have "mub_closure S \<subseteq> ?T" by (rule mub_closure_least)
  hence "?R ` mub_closure S \<subseteq> M" by auto
  with finM have fin_img: "finite (?R ` mub_closure S)" by (rule finite_subset[rotated])
  have "inj_on ?R (mub_closure S)" using inj by (meson inj_eq inj_onI)
  with fin_img show "finite (mub_closure S)" by (rule finite_imageD)
qed

text \<open>Proposition 2.2.16 from Abramsky and Jung's Domain Theory - compactness for directed sets\<close>

lemma directed_compactD:
  fixes x :: "'a::bifinite" and D :: "'a set"
  assumes "compact x" "directed D" "D \<noteq> {}"
    "x \<sqsubseteq> lub D"
  shows "\<exists>y \<in> D. x \<sqsubseteq> y"
  using compactD[THEN directed_admD, of x D] assms
  by blast

section \<open>The deflation determined by a MUB-closed set of compacts\<close>

text \<open>For a MUB-closed set @{term S} of compact basis elements (containing the
  basis element of @{term \<open>\<bottom>\<close>}), the assignment
    @{term \<open>\<lambda>a. lub {Rep_compact_basis b |b. b \<in> S \<and> b \<sqsubseteq> a}\<close>}
  is monotone, and its @{const compact_basis.extension} is a deflation whose
  compact fixed points are exactly @{term S}.  Working in a locale à la
  \<open>stable_subdomain\<close>.\<close>

locale mub_closed_basis =
  fixes S :: "'a::bifinite compact_basis set"
  assumes mub_closed_S: "mub_closed S"
begin

lemma bot_in_S: "compact_bot \<in> S"
proof -
  have "x \<sqsubseteq> compact_bot \<Longrightarrow> x = compact_bot"
    for x :: "'a compact_basis"
    using compact_bot_minimal below_antisym by blast
  then have "is_mub ({}::'a compact_basis set) compact_bot"
    unfolding is_mub_def by auto
  with mub_closedD[OF mub_closed_S] show ?thesis by blast
qed

definition below_set :: "'a \<Rightarrow> 'a compact_basis set"
  where "below_set a = {x \<in> S. Rep_compact_basis x \<sqsubseteq> a}"

definition g :: "'a \<Rightarrow> 'a"
  where "g a = lub (Rep_compact_basis ` below_set a)"

lemma below_set_nonempty: "below_set a \<noteq> {}"
proof -
  have "Rep_compact_basis compact_bot \<sqsubseteq> a"
    by simp
  with bot_in_S show ?thesis unfolding below_set_def by blast
qed

lemma below_set_directed: "directed (below_set a)"
proof (rule directedI)
  fix x y assume "x \<in> below_set a" "y \<in> below_set a"
  then have S: "x \<in> S" "y \<in> S"
    and a: "Rep_compact_basis x \<sqsubseteq> a" "Rep_compact_basis y \<sqsubseteq> a"
    unfolding below_set_def by auto
  from a have "Rep_compact_basis ` {x, y} <| a"
    by (auto intro: is_ubI)
  with compact_mub_basis_bound_below[of "{x, y}" a]
  obtain z where mub: "is_mub {x, y} z" and az: "Rep_compact_basis z \<sqsubseteq> a"
    by blast
  from S have "{x, y} \<subseteq> S" by simp
  with mub_closed_S[THEN mub_closedD, of "{x, y}"] mub
  have "z \<in> S" by fast
  with az have "z \<in> below_set a" unfolding below_set_def by simp
  moreover from mub[THEN is_mubD1, THEN is_ubD]
  have "x \<sqsubseteq> z \<and> y \<sqsubseteq> z" by simp
  ultimately show "\<exists>z \<in> below_set a. x \<sqsubseteq> z \<and> y \<sqsubseteq> z"..
qed

corollary below_set_nonempty':
  "Rep_compact_basis ` below_set a \<noteq> {}"
  using below_set_nonempty by simp

corollary below_set_directed':
  "directed (Rep_compact_basis ` below_set a)"
  using compact_le_def below_set_directed
    directed_mono_image[of Rep_compact_basis "below_set a"]
  by metis

lemma g_lub: "Rep_compact_basis ` below_set a <<| g a"
    unfolding g_def using below_set_directed' by (rule directed_lub)

lemma g_approximant:
  "x \<in> approximants (g a) \<longleftrightarrow> (\<exists>b \<in> below_set a. x \<sqsubseteq> b)"
  unfolding approximants_def
proof (safe)
  fix x assume "Rep_compact_basis x \<sqsubseteq> g a"
  with directed_compactD[OF Rep_compact_basis' below_set_directed' below_set_nonempty']
  have "\<exists>y \<in> Rep_compact_basis ` below_set a. Rep_compact_basis x \<sqsubseteq> y"
    unfolding g_def by auto
  then show "\<exists>b\<in>below_set a. x \<sqsubseteq> b" by fastforce
next
  fix x b assume "b \<in> below_set a"
  with directed_lub[OF below_set_directed', THEN is_lubD1, THEN is_ubD]
  have "Rep_compact_basis b \<sqsubseteq> g a" unfolding g_def by blast
  moreover assume "x \<sqsubseteq> b"
  ultimately show "Rep_compact_basis x \<sqsubseteq> g a"
    unfolding compact_le_def by (rule below_trans[rotated])
qed

definition "down_closure (A::'b::po set) = {x. \<exists>y \<in> A. x \<sqsubseteq> y}"

lemma below_set_alt: "below_set a = S \<inter> approximants a"
  unfolding below_set_def approximants_def by blast

corollary approximants_g:
  "approximants (g a) = down_closure (below_set a)"
  unfolding down_closure_def using g_approximant
  by blast

lemma below_set_chain:
  fixes Y :: "nat \<Rightarrow> 'a"
  assumes "chain Y"
  shows "below_set (\<Squnion>i. Y i) = (\<Union>i. below_set (Y i))"
  unfolding below_set_alt compact_basis.rep_lub[OF assms]
  by simp

lemma down_closure_UN: "down_closure (\<Union>i. P i) = (\<Union>i. down_closure (P i))"
  unfolding down_closure_def by blast

lemma below_set_mono: "a \<sqsubseteq> b \<Longrightarrow> below_set a \<subseteq> below_set b"
  unfolding below_set_def using below_trans by blast

lemma g_mono: "monofun g"
proof (rule monofunI)
  fix a b :: "'a"
  assume ab: "a \<sqsubseteq> b"
  show "g a \<sqsubseteq> g b"
    using below_set_mono[OF ab] 
    by (fast intro: lub_subset_mono[OF g_lub g_lub])
qed

lemma g_cont: "cont g"
proof (rule contI2, rule g_mono)
  fix Y :: "nat \<Rightarrow> 'a"
  assume Y: "chain Y"
    and gY: "chain (\<lambda>i. g (Y i))"
  show "g (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. g (Y i))"
    apply (rule compact_basis.belowI)
    unfolding approximants_g below_set_chain[OF Y]
      compact_basis.rep_lub[OF gY] down_closure_UN ..
qed

definition d :: "'a \<rightarrow> 'a"
  where "d \<equiv> \<Lambda> x. g x"

lemma d_lub: "Rep_compact_basis ` below_set a <<| d\<cdot>a"
  unfolding d_def
  by (simp add: g_lub g_cont)

lemma d_eq_lub: "d\<cdot>a = lub (Rep_compact_basis ` below_set a)"
  using d_lub[THEN lub_eqI] ..

lemma below_set_ub: "Rep_compact_basis ` below_set a <| a"
  by (simp add: below_set_def is_ub_def)

corollary d_below: "d\<cdot>a \<sqsubseteq> a"
  using d_lub[THEN is_lubD2, OF below_set_ub] .

lemma d_fixed: "d\<cdot>(Rep_compact_basis a) = Rep_compact_basis a" if "a \<in> S"
proof (intro below_antisym d_below)
  let ?a = "Rep_compact_basis a"
  from that have "a \<in> below_set ?a" by (simp add: below_set_def)
  then have "?a \<in> Rep_compact_basis ` below_set ?a" by simp
  with d_lub[THEN is_lubD1, THEN is_ubD]
  show "?a \<sqsubseteq> d\<cdot>?a" .
qed

lemma approximants_closed_down: "x \<in> approximants a \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> y \<in> approximants a"
  unfolding approximants_def compact_le_def by (auto dest: below_trans)

lemma below_set_idem: "below_set (g a) = below_set a"
  unfolding below_set_alt approximants_g down_closure_def
  using approximants_closed_down
  by auto

corollary g_idem: "g (g a) = g a"
  using below_set_idem g_def by auto

lemma deflation_d: "deflation d"
proof (rule deflation.intro)
  fix x show "d\<cdot>(d\<cdot>x) = d\<cdot>x" by (simp add: g_idem g_cont d_def)
next
  fix x show "d\<cdot>x \<sqsubseteq> x" by (rule d_below)
qed

lemma d_fixes: "d\<cdot>(Rep_compact_basis a) = Rep_compact_basis a \<longleftrightarrow> a \<in> S"
proof
  assume "a \<in> S"
  thus "d\<cdot>(Rep_compact_basis a) = Rep_compact_basis a" by (rule d_fixed)
next
  let ?a = "Rep_compact_basis a"
  assume fx: "d\<cdot>?a = ?a"
  then have "?a \<sqsubseteq> g ?a" by (simp add: d_def g_cont)
  then have "a \<in> approximants (g ?a)" by (simp add: approximants_def)
  then have "\<exists>y \<in> below_set ?a. a \<sqsubseteq> y"
    by (simp add: g_approximant) 
  then obtain y where y: "y \<in> below_set ?a" and le: "a \<sqsubseteq> y" by blast
  from y have y: "y \<in> S" and le2: "y \<sqsubseteq> a"
    unfolding below_set_def compact_le_def by auto
  from le le2 have "a = y" by (rule below_antisym)
  with y show "a \<in> S" by simp
qed


text \<open>When @{term S} is finite the extension is a \emph{finite} deflation: its
  values, and hence its fixed points, all lie in the finite set @{term \<open>Rep_compact_basis ` S\<close>}.\<close>

lemma d_in_RepS:
  assumes "finite S"
  shows "d\<cdot>a \<in> Rep_compact_basis ` S"
proof -
  have sub: "Rep_compact_basis ` below_set a \<subseteq> Rep_compact_basis ` S"
    unfolding below_set_def by blast
  hence fin: "finite (Rep_compact_basis ` below_set a)" using assms
    by (meson finite_imageI finite_subset)
  have "lub (Rep_compact_basis ` below_set a) \<in>  Rep_compact_basis ` below_set a"
    by (rule finite_directed_lub_mem[OF below_set_directed' fin below_set_nonempty'])
  with sub show ?thesis using d_eq_lub by auto
qed

lemma finite_deflation_d:
  assumes "finite S"
  shows "finite_deflation d"
proof (rule finite_deflation_intro[OF deflation_d])
  have "{x. d\<cdot>x = x} \<subseteq> Rep_compact_basis ` S"
  proof
    fix x assume "x \<in> {x. d\<cdot>x = x}"
    hence "x = d\<cdot>x" by simp
    also have "d\<cdot>x \<in> Rep_compact_basis ` S" by (rule d_in_RepS[OF assms])
    finally show "x \<in> Rep_compact_basis ` S" .
  qed
  thus "finite {x. d\<cdot>x = x}" using assms by (meson finite_imageI finite_subset)
qed
end

end
