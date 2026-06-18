theory Deflations
  imports Bounded_Complete
begin

(* ===================================================================== *)
(*  Deflations via MUB-closures                                          *)
(*                                                                       *)
(*  Goal: for 'a::bifinite, 'cast :: 'a defl \<rightarrow> ('a \<rightarrow> 'a)' is a          *)
(*  bijection onto the set of all deflations.  Injectivity is free       *)
(*  (Algebraic.cast_eq_imp_eq); the content is SURJECTIVITY onto         *)
(*  {d. deflation d}, routed through MUB-closed sets of compacts.        *)
(*                                                                       *)
(*  Reused infrastructure                                                *)
(*  - Bounded_Complete: min_ub a b z  (z a minimal upper bound of a,b)   *)
(*      min_ub_of_compact: for compact a,b  ->  min_ub exists below any  *)
(*      bound, min_ubs are compact, and {z. min_ub a b z} is finite.     *)
(*  - HOLCF/Universal: compact_basis.extension f = (\<Lambda> x. lub (f `        *)
(*      approximants x)); extension_principal/beta/mono, cont_extension. *)
(*  - HOLCF/Algebraic: fin_defl (type of finite deflations) with         *)
(*      Rep_fin_defl, finite_fixes, fin_defl_eqI, fin_defl_belowI,       *)
(*      Rep_fin_defl.compact_belowI;  'a defl = ideal completion of      *)
(*      fin_defl via defl_principal (defl.principal_induct, ...);        *)
(*      cast = defl.extension Rep_fin_defl, cast_defl_principal,         *)
(*      deflation_cast, finite_deflation_cast, cast_below_cast (cast is  *)
(*      an ORDER-EMBEDDING), cast_eq_imp_eq (cast INJECTIVE).            *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(*  Section 1.  MUB-closure                                              *)
(* --------------------------------------------------------------------- *)
(*  Work at the compact-basis level:                                     *)
(*    min_ub_cb a b z  ==  min_ub (Rep_compact_basis a)                  *)
(*                                (Rep_compact_basis b)                  *)
(*                                (Rep_compact_basis z)                  *)
(*  mub_closed T   ==  \<forall>a\<in>T. \<forall>b\<in>T. \<forall>z. min_ub_cb a b z --> z \<in> T        *)
(*    (pairwise; equivalent by induction to closure under MUBs of every  *)
(*     finite subset).                                                   *)
(*  - mub_closed is preserved under arbitrary \<Inter>.                         *)
(*  mub_closure S  ==  \<Inter> {T. mub_closed T \<and> S \<subseteq> T}.                      *)
(*  - extensive:  S \<subseteq> mub_closure S                                      *)
(*  - mub_closed (mub_closure S);  monotone;  idempotent                 *)
(*  - KEYSTONE  mub_closure_least:                                       *)
(*        A \<subseteq> B \<Longrightarrow> mub_closed B \<Longrightarrow> mub_closure A \<subseteq> B                      *)
(*    (immediate from the \<Inter> definition; no induction required).          *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(*  Section 2.  Fixed sets of deflations are MUB-closed                  *)
(* --------------------------------------------------------------------- *)
(*  - deflation_preserves_min_ub:                                        *)
(*        deflation d \<Longrightarrow> d\<cdot>a = a \<Longrightarrow> d\<cdot>b = b \<Longrightarrow> min_ub a b z \<Longrightarrow> d\<cdot>z = z    *)
(*    (d\<cdot>z \<sqsubseteq> z by deflation; a,b \<sqsubseteq> d\<cdot>z by monotonicity; minimality of z) *)
(*  - deflation_fixes_mub_closed:                                        *)
(*        deflation d \<Longrightarrow> mub_closed {a. d\<cdot>(Rep_compact_basis a)          *)
(*                                       = Rep_compact_basis a}          *)
(*  - Corollary (via mub_closure_least):                                 *)
(*        S \<subseteq> fixes d \<Longrightarrow> mub_closure S \<subseteq> fixes d.                        *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(*  Section 3.  Finiteness in bifinite domains                          *)
(* --------------------------------------------------------------------- *)
(*  - finite_compacts_fixed: a finite set of compacts is fixed by a      *)
(*    single finite_deflation (generalise compact_eq_approx2 via         *)
(*    approx_chain + max-of-indices; the idem_mono trick from            *)
(*    min_ub_of_compact).                                                *)
(*  - finite_mub_closure: S finite (basis) \<Longrightarrow> mub_closure S finite       *)
(*    (it sits inside the finite fixed-set of that finite_deflation;     *)
(*    finite_deflation.finite_fixes).                                    *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(*  Section 4.  defl_of_set : a locale (à la stable_subdomain),         *)
(*              for ARBITRARY mub-closed S :: 'a compact_basis set       *)
(*              with \<bottom> \<in> S.                                              *)
(* --------------------------------------------------------------------- *)
(*  {b \<in> S. b \<sqsubseteq> a} is directed (mub-closedness + min_ub_below) and      *)
(*  nonempty (\<bottom>), hence has a lub:                                       *)
(*      g a  =  lub {Rep_compact_basis b | b \<in> S \<and> b \<sqsubseteq> a}               *)
(*      defl_of_set S  =  compact_basis.extension g.                     *)
(*  Prove, inside the locale:                                            *)
(*  - g monotone (so extension_beta/principal apply); cont side-conds    *)
(*  - deflation (defl_of_set S)                                          *)
(*  - fixes recover S:                                                   *)
(*        {x. compact x \<and> defl_of_set S\<cdot>x = x}  \<leftrightarrow>  S                     *)
(*  - finite S \<Longrightarrow> finite_deflation (defl_of_set S)   (Section 3).        *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(*  Section 5.  Lattice of finite deflations (fin_defl) and joins       *)
(* --------------------------------------------------------------------- *)
(*  fin_defl order IS fixes-inclusion (fin_defl_belowI / fin_defl_eqI):  *)
(*      A \<sqsubseteq> B  \<longleftrightarrow>  fixes A \<subseteq> fixes B.                                    *)
(*  Pairwise join exists:                                                *)
(*      A \<squnion> B  =  (fin_defl of) defl_of_set                             *)
(*                   (mub_closure (fixes A \<union> fixes B))                   *)
(*    finite by Section 3, mub-closed by construction; it is the LUB     *)
(*    because any upper bound's fixes form a mub-closed superset of      *)
(*    fixes A \<union> fixes B, hence \<supseteq> the mub_closure (mub_closure_least).    *)
(*  This is the "lattice-embedding" step: the fixes map is an order-     *)
(*  embedding of fin_defl into the lattice of mub-closed sets; cast      *)
(*  (cast_below_cast) transports it to 'a defl.                          *)
(*  Consequence: finite mub-closed sets  \<leftrightarrow>  fin_defl  \<leftrightarrow>  compact 'a defl.*)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(*  Section 6.  cast is surjective onto deflations  (the ideal-          *)
(*              completion step — NOT direct)                            *)
(* --------------------------------------------------------------------- *)
(*  NB: defl_of_set S_d = d (Section 4/5) only shows d is the deflation  *)
(*  determined by its compact fixes S_d; it does NOT itself give a       *)
(*  preimage in 'a defl.  Since 'a defl is the IDEAL COMPLETION of       *)
(*  fin_defl, the preimage must be built as a LUB OF PRINCIPALS, which   *)
(*  is why directedness (Section 5) is a prerequisite.                   *)
(*                                                                       *)
(*  Given deflation d, set S_d = compact fixes of d (mub-closed, Sec 2). *)
(*  For finite F \<subseteq> S_d let                                               *)
(*      e_F = defl_of_set (mub_closure (F \<union> {\<bottom>}))   : a fin_defl \<sqsubseteq> d     *)
(*  (\<sqsubseteq> d since its fixes \<subseteq> S_d which d fixes; finite by Section 3).      *)
(*  The family {e_F} is DIRECTED (Section 5 joins) and \<Squnion>_F e_F = d       *)
(*  (every compact fixed point of d is some e_{{c}}, so the lub fixes    *)
(*  all of S_d, hence dominates d; and each e_F \<sqsubseteq> d).                    *)
(*  Lift to principals:  D = (\<Squnion> F. defl_principal (fin_defl e_F))        *)
(*  exists (directed image of defl_principal in the cpo 'a defl) and     *)
(*      cast\<cdot>D = (\<Squnion> F. Rep_fin_defl (fin_defl e_F)) = (\<Squnion>_F e_F) = d      *)
(*  by continuity of cast and cast_defl_principal.                       *)
(*                                                                       *)
(*  - cast_surj:  deflation d \<Longrightarrow> \<exists>D. cast\<cdot>D = d                          *)
(*  - cast_bij:   bij_betw (Rep_cfun cast) UNIV {d. deflation d}         *)
(*                (injectivity from cast_eq_imp_eq).                     *)
(*  - optional: defl_of : ('a \<rightarrow> 'a) \<rightarrow> 'a defl with cast oo defl_of = ID  *)
(*    on deflations and defl_of oo cast = ID, transporting the lattice.  *)
(* --------------------------------------------------------------------- *)

section \<open>MUB-closure (in an arbitrary partial order)\<close>

text \<open>\<open>min_ub\<close> (from @{theory \<open>HOLCF-extra.Bounded_Complete\<close>}) is generic over
  sort @{class po}, so the following closure operators apply both to \<open>'a\<close> itself
  and to \<open>'a compact_basis\<close>.\<close>

definition mub_closed :: "'a::po set \<Rightarrow> bool"
  where "mub_closed T \<longleftrightarrow> (\<forall>a\<in>T. \<forall>b\<in>T. \<forall>z. min_ub a b z \<longrightarrow> z \<in> T)"

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


section \<open>Fixed sets of deflations are MUB-closed\<close>

lemma deflation_preserves_min_ub:
  assumes d: "deflation d" and a: "d\<cdot>a = a" and b: "d\<cdot>b = b" and z: "min_ub a b z"
  shows "d\<cdot>z = z"
proof -
  from z have az: "a \<sqsubseteq> z" and bz: "b \<sqsubseteq> z"
    and minz: "\<And>w. a \<sqsubseteq> w \<Longrightarrow> b \<sqsubseteq> w \<Longrightarrow> w \<sqsubseteq> z \<Longrightarrow> w = z"
    unfolding min_ub_def by auto
  from az a have "a \<sqsubseteq> d\<cdot>z" by (metis monofun_cfun_arg)
  moreover from bz b have "b \<sqsubseteq> d\<cdot>z" by (metis monofun_cfun_arg)
  moreover from d have "d\<cdot>z \<sqsubseteq> z" by (rule deflation.below)
  ultimately show ?thesis using minz by blast
qed

lemma deflation_fixes_mub_closed:
  assumes "deflation d"
  shows "mub_closed {x. d\<cdot>x = x}"
  unfolding mub_closed_def
  using deflation_preserves_min_ub[OF assms] by blast

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

text \<open>Lifting to \<open>'a compact_basis\<close>, bridging via @{thm min_ub_Cb_def} the way
  @{theory \<open>HOLCF-extra.Bounded_Complete\<close>} relates \<open>min_ub\<close> on compacts to \<open>min_ub\<close>
  on the basis.\<close>

lemma min_ub_compact_basis:
  fixes a b z :: "'a::bifinite compact_basis"
  shows "min_ub a b z \<longleftrightarrow>
    min_ub (Rep_compact_basis a) (Rep_compact_basis b) (Rep_compact_basis z)"
proof -
  have "min_ub a b z \<longleftrightarrow> (a \<sqsubseteq> z \<and> b \<sqsubseteq> z \<and> (\<forall>w. a \<sqsubseteq> w \<longrightarrow> b \<sqsubseteq> w \<longrightarrow> w \<sqsubseteq> z \<longrightarrow> w = z))"
    by (simp add: min_ub_def)
  also have "\<dots> \<longleftrightarrow> min_ub (Rep_compact_basis a) (Rep_compact_basis b) (Rep_compact_basis z)"
    by (rule min_ub_Cb_def[symmetric])
  finally show ?thesis .
qed

lemma finite_mub_closure_cb:
  fixes S :: "'a::bifinite compact_basis set"
  assumes finS: "finite S"
  shows "finite (mub_closure S)"
proof -
  define R where "R = (Rep_compact_basis :: 'a compact_basis \<Rightarrow> 'a)"
  have inj: "inj R" unfolding R_def
    by (metis compact_basis.Rep_compact_basis_inject injI)
  have cpt: "compact x" if "x \<in> R ` S" for x
    using that unfolding R_def using Rep_compact_basis' by auto
  have finRS: "finite (R ` S)" using finS by simp
  define M where "M = mub_closure (R ` S)"
  have finM: "finite M" unfolding M_def by (rule finite_mub_closure(1)[OF finRS cpt])
  let ?T = "{a. R a \<in> M}"
  have Ssub: "S \<subseteq> ?T"
    using mub_closure_extensive[of "R ` S"] unfolding M_def by auto
  have Tclosed: "mub_closed ?T"
    unfolding mub_closed_def
  proof (intro ballI allI impI)
    fix a b z assume ab: "a \<in> ?T" "b \<in> ?T" and mz: "min_ub a b z"
    from mz have "min_ub (R a) (R b) (R z)"
      unfolding R_def using min_ub_compact_basis by blast
    moreover from ab have "R a \<in> M" "R b \<in> M" by auto
    moreover have "mub_closed M" unfolding M_def by (rule mub_closed_mub_closure)
    ultimately have "R z \<in> M" unfolding mub_closed_def by blast
    thus "z \<in> ?T" by simp
  qed
  have "mub_closure S \<subseteq> ?T" by (rule mub_closure_least[OF Ssub Tclosed])
  hence "R ` mub_closure S \<subseteq> M" by auto
  with finM have fin_img: "finite (R ` mub_closure S)" by (rule finite_subset[rotated])
  have "inj_on R (mub_closure S)" using inj by (meson inj_eq inj_onI)
  with fin_img show "finite (mub_closure S)" by (rule finite_imageD)
qed


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
    and bot_in_S: "Abs_compact_basis \<bottom> \<in> S"
begin

definition below_set :: "'a compact_basis \<Rightarrow> 'a set"
  where "below_set a = {Rep_compact_basis b |b. b \<in> S \<and> b \<sqsubseteq> a}"

definition g :: "'a compact_basis \<Rightarrow> 'a"
  where "g a = lub (below_set a)"

definition d :: "'a \<rightarrow> 'a"
  where "d = compact_basis.extension g"

lemma below_set_nonempty: "below_set a \<noteq> {}"
proof -
  have "Abs_compact_basis \<bottom> \<sqsubseteq> a"
    by (simp add: compact_le_def Abs_compact_basis_inverse')
  with bot_in_S show ?thesis unfolding below_set_def by blast
qed

lemma below_set_directed: "directed (below_set a)"
proof (rule directedI)
  fix x y assume "x \<in> below_set a" "y \<in> below_set a"
  then obtain b1 b2 where b1: "b1 \<in> S" "b1 \<sqsubseteq> a" "x = Rep_compact_basis b1"
    and b2: "b2 \<in> S" "b2 \<sqsubseteq> a" "y = Rep_compact_basis b2"
    unfolding below_set_def by blast
  from min_ub_below'[OF b1(2) b2(2)] obtain w
    where mw: "min_ub (Rep_compact_basis b1) (Rep_compact_basis b2) (Rep_compact_basis w)"
      and wa: "w \<sqsubseteq> a" by blast
  from mw have "min_ub b1 b2 w" using min_ub_compact_basis by blast
  with b1(1) b2(1) mub_closed_S have wS: "w \<in> S" unfolding mub_closed_def by blast
  from mw have "x \<sqsubseteq> Rep_compact_basis w" "y \<sqsubseteq> Rep_compact_basis w"
    unfolding min_ub_def using b1(3) b2(3) by auto
  moreover from wS wa have "Rep_compact_basis w \<in> below_set a"
    unfolding below_set_def by blast
  ultimately show "\<exists>z\<in>below_set a. x \<sqsubseteq> z \<and> y \<sqsubseteq> z" by blast
qed

lemma below_set_mono: "a \<sqsubseteq> b \<Longrightarrow> below_set a \<subseteq> below_set b"
  unfolding below_set_def using below_trans by blast

lemma below_set_ub: "below_set a <| Rep_compact_basis a"
proof (rule is_ubI)
  fix x assume "x \<in> below_set a"
  then obtain b where "b \<sqsubseteq> a" "x = Rep_compact_basis b"
    unfolding below_set_def by blast
  thus "x \<sqsubseteq> Rep_compact_basis a" by (metis compact_le_def)
qed

lemma g_below: "g a \<sqsubseteq> Rep_compact_basis a"
proof -
  have lub: "below_set a <<| g a"
    unfolding g_def using below_set_directed by (rule directed_lub)
  from lub below_set_ub show ?thesis using is_lub_below_iff by blast
qed

lemma g_mono: "a \<sqsubseteq> b \<Longrightarrow> g a \<sqsubseteq> g b"
proof -
  assume ab: "a \<sqsubseteq> b"
  have ga: "below_set a <<| g a"
    unfolding g_def using below_set_directed by (rule directed_lub)
  have gb: "below_set b <<| g b"
    unfolding g_def using below_set_directed by (rule directed_lub)
  have ub_gb: "below_set b <| g b"
    using is_lub_below_iff[OF gb] below_refl by blast
  have "below_set a <| g b"
  proof (rule is_ubI)
    fix x assume "x \<in> below_set a"
    with below_set_mono[OF ab] have "x \<in> below_set b" by blast
    with ub_gb show "x \<sqsubseteq> g b" by (rule is_ubD)
  qed
  with ga show ?thesis using is_lub_below_iff by blast
qed

lemma d_app: "d\<cdot>(Rep_compact_basis a) = g a"
  unfolding d_def by (rule compact_basis.extension_principal[OF g_mono])

lemma g_fixed: "a \<in> S \<Longrightarrow> g a = Rep_compact_basis a"
proof -
  assume aS: "a \<in> S"
  have "below_set a <| Rep_compact_basis a" by (rule below_set_ub)
  moreover from aS have "Rep_compact_basis a \<in> below_set a"
    unfolding below_set_def using below_refl by auto
  ultimately show ?thesis unfolding g_def by (rule lub_maximal)
qed

lemma d_g_fixed: "d\<cdot>(g a) = g a"
proof -
  have img: "(\<lambda>y. d\<cdot>y) ` below_set a = below_set a"
  proof -
    have "d\<cdot>y = y" if "y \<in> below_set a" for y
    proof -
      from that obtain b where "b \<in> S" "y = Rep_compact_basis b"
        unfolding below_set_def by blast
      thus "d\<cdot>y = y" by (simp add: d_app g_fixed)
    qed
    thus ?thesis by force
  qed
  have "d\<cdot>(g a) = lub ((\<lambda>y. d\<cdot>y) ` below_set a)"
    unfolding g_def
    by (rule cont_directed_lub[symmetric, OF cont_Rep_cfun2 below_set_directed below_set_nonempty])
  also have "\<dots> = lub (below_set a)" by (simp add: img)
  also have "\<dots> = g a" by (simp add: g_def)
  finally show ?thesis .
qed

lemma deflation_d: "deflation d"
proof (rule deflation.intro)
  fix x show "d\<cdot>(d\<cdot>x) = d\<cdot>x"
  proof (induct x rule: compact_basis.principal_induct)
    show "adm (\<lambda>x. d\<cdot>(d\<cdot>x) = d\<cdot>x)" by simp
  next
    fix a show "d\<cdot>(d\<cdot>(Rep_compact_basis a)) = d\<cdot>(Rep_compact_basis a)"
      by (simp add: d_app d_g_fixed)
  qed
next
  fix x show "d\<cdot>x \<sqsubseteq> x"
  proof (induct x rule: compact_basis.principal_induct)
    show "adm (\<lambda>x. d\<cdot>x \<sqsubseteq> x)" by simp
  next
    fix a show "d\<cdot>(Rep_compact_basis a) \<sqsubseteq> Rep_compact_basis a"
      by (simp add: d_app g_below)
  qed
qed

lemma d_fixes: "d\<cdot>(Rep_compact_basis a) = Rep_compact_basis a \<longleftrightarrow> a \<in> S"
proof
  assume "a \<in> S"
  thus "d\<cdot>(Rep_compact_basis a) = Rep_compact_basis a" by (simp add: d_app g_fixed)
next
  assume fx: "d\<cdot>(Rep_compact_basis a) = Rep_compact_basis a"
  hence ga: "lub (below_set a) = Rep_compact_basis a" using d_app g_def by simp
  have "\<exists>y \<in> below_set a. Rep_compact_basis a \<sqsubseteq> y"
  proof (rule ccontr)
    assume "\<not> (\<exists>y\<in>below_set a. Rep_compact_basis a \<sqsubseteq> y)"
    hence alln: "\<forall>y\<in>below_set a. \<not> Rep_compact_basis a \<sqsubseteq> y" by blast
    have "adm (\<lambda>y. \<not> Rep_compact_basis a \<sqsubseteq> y)" by (metis Rep_compact_basis' compact_def)
    from directed_admD[OF this below_set_directed below_set_nonempty alln]
    have "\<not> Rep_compact_basis a \<sqsubseteq> lub (below_set a)" .
    with ga show False by simp
  qed
  then obtain y where y: "y \<in> below_set a" and le: "Rep_compact_basis a \<sqsubseteq> y" by blast
  from y obtain b where b: "b \<in> S" "b \<sqsubseteq> a" "y = Rep_compact_basis b"
    unfolding below_set_def by blast
  from le b(3) have "Rep_compact_basis a \<sqsubseteq> Rep_compact_basis b" by simp
  moreover from b(2) have "Rep_compact_basis b \<sqsubseteq> Rep_compact_basis a"
    by (metis compact_le_def)
  ultimately have "Rep_compact_basis a = Rep_compact_basis b" by (rule below_antisym)
  hence "a = b" by (metis compact_basis.Rep_compact_basis_inject)
  with b(1) show "a \<in> S" by simp
qed

end

end
