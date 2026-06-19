theory Deflations
  imports Bounded_Complete "HOLCF-Library.Defl_Bifinite"
begin

(* ===================================================================== *)
(*  Deflations via MUB-closures                                          *)
(*                                                                       *)
(*  For 'a::bifinite, 'cast :: 'a defl \<rightarrow> ('a \<rightarrow> 'a)' is injective         *)
(*  (Algebraic.cast_eq_imp_eq).  It is NOT surjective onto all of        *)
(*  {d. deflation d}: a deflation is a lub of finite deflations iff its   *)
(*  image is bifinite, and bifinite domains are not closed under          *)
(*  retracts.  What we develop instead, via MUB-closed sets of compacts:  *)
(*  the lattice of finite deflations (fin_defl), and the fact that an     *)
(*  algebraic deflation 'cast A' is determined by the COMPACT elements    *)
(*  it fixes -- 'dfixes (cast A)' (defl_eq_iff_dfixes / defl_below_iff_-  *)
(*  dfixes, an order embedding of 'a defl into sets of compacts).         *)
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
(*  Section 6.  Algebraic deflations are determined by their compact     *)
(*              fixes  (cast is NOT surjective onto all deflations)      *)
(* --------------------------------------------------------------------- *)
(*  cast is injective but NOT onto {d. deflation d}: 'd \<sqsubseteq> \<Squnion> finite       *)
(*  deflations below it' is equivalent to 'image of d is bifinite', and  *)
(*  bifinite domains are not closed under retracts (RB ⊋ B; cf. Jung).   *)
(*  So a deflation whose image is a non-bifinite retract has no preimage *)
(*  under cast.                                                          *)
(*                                                                       *)
(*  The positive result, mirroring Section 5: the COMPACT fixes pin down *)
(*  an algebraic deflation.  Write S_d = dfixes d (mub-closed, Sec 2).   *)
(*  - Rep_fin_defl_below_cast: a \<in> Rep_defl A \<Longrightarrow> Rep_fin_defl a \<sqsubseteq> cast A  *)
(*    (each finite deflation in the ideal of A lies below cast A).       *)
(*  - dfixes_cast_mono: A \<sqsubseteq> B \<Longrightarrow> dfixes (cast A) \<subseteq> dfixes (cast B)        *)
(*    (just monotonicity of cast on the fixed-point sets).               *)
(*  - defl_below_of_dfixes: dfixes (cast A) \<subseteq> dfixes (cast B) \<Longrightarrow> A \<sqsubseteq> B.   *)
(*    Test each Rep_fin_defl a (a in the ideal of A) against cast B with *)
(*    Rep_fin_defl.compact_belowI, which only inspects COMPACT fixed     *)
(*    points: cast A fixes them (a \<sqsubseteq> A), so they lie in dfixes (cast A)  *)
(*    \<subseteq> dfixes (cast B); hence Rep_fin_defl a \<sqsubseteq> cast B, so A \<sqsubseteq> B.        *)
(*  Combining the two directions:                                        *)
(*  - defl_below_iff_dfixes: A \<sqsubseteq> B \<longleftrightarrow> dfixes (cast A) \<subseteq> dfixes (cast B)   *)
(*      (order embedding of 'a defl into sets of compact basis elts).    *)
(*  - defl_eq_iff_dfixes:   A = B \<longleftrightarrow> dfixes (cast A) = dfixes (cast B).   *)
(* --------------------------------------------------------------------- *)

section \<open>MUB-closure (in an arbitrary partial order)\<close>

text \<open>\<open>min_ub\<close> (from @{theory \<open>HOLCF-extra.Bounded_Complete\<close>}) is generic over
  sort @{class po}, so the following closure operators apply both to \<open>'a\<close> itself
  and to \<open>'a compact_basis\<close>.\<close>

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

text \<open>Lifting to \<open>'a compact_basis\<close>, bridging via @{thm min_ub_Cb_def} the way
  @{theory \<open>HOLCF-extra.Bounded_Complete\<close>} relates \<open>min_ub\<close> on compacts to \<open>min_ub\<close>
  on the basis.\<close>

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
    by (rule below_order.finite_has_minimal)
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
    with mleb have "d\<cdot>c \<sqsubseteq> b" by order
    moreover from d.deflation_axioms sub \<open>A <| c\<close> have "A <| d\<cdot>c"
      by (rule deflation_ub)
    ultimately have "d\<cdot>c \<in> bounds" unfolding bounds_def using d.idem
      by auto
    with dclem 2 have "m = d\<cdot>c" by fast
    with d.below[of c] \<open>c \<sqsubseteq> m\<close> show "c = m" by order
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
  moreover from * cleb have "Rep_compact_basis ?c \<sqsubseteq> b" by order
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
  with cleb blea show "b = Rep_compact_basis a" by simp
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

lemma approximants_directed: "directed (approximants (x :: 'a::bifinite))"
proof (rule directedI)
  fix a b assume "a \<in> approximants x" "b \<in> approximants x"
  thus "\<exists>z\<in>approximants x. a \<sqsubseteq> z \<and> b \<sqsubseteq> z"
    using below.idealD2[OF compact_basis.ideal_rep] by blast
qed

text \<open>Proposition 2.2.16 form Abramsky & Jung's Domain Theory - compactness for directed sets\<close>

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
    unfolding compact_le_def by order
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
  from le le2 have "a = y" by order
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

section \<open>The lattice of finite deflations\<close>

text \<open>A deflation is below another exactly when its fixed-point set is contained
  in the other's.  This is the order-theoretic content behind @{const cast} being
  an order-embedding, phrased for raw deflations.\<close>

lemma deflation_belowI_fixes:
  assumes d: "deflation d" and e: "deflation e"
    and fx: "\<And>x. e\<cdot>x = x \<Longrightarrow> d\<cdot>x = x"
  shows "e \<sqsubseteq> d"
proof (rule cfun_belowI)
  fix x
  from e have "e\<cdot>(e\<cdot>x) = e\<cdot>x" by (rule deflation.idem)
  hence "d\<cdot>(e\<cdot>x) = e\<cdot>x" by (rule fx)
  moreover from e have "e\<cdot>x \<sqsubseteq> x" by (rule deflation.below)
  ultimately show "e\<cdot>x \<sqsubseteq> d\<cdot>x" by (metis monofun_cfun_arg)
qed

text \<open>The compact fixed points of a deflation, as a set of basis elements.  By \<section>2
  this is MUB-closed, and it contains @{term \<open>\<bottom>\<close>}, so it satisfies the assumptions
  of the @{locale mub_closed_basis} locale.\<close>

definition dfixes :: "('a::bifinite \<rightarrow> 'a) \<Rightarrow> 'a compact_basis set"
  where "dfixes d = {a. d\<cdot>(Rep_compact_basis a) = Rep_compact_basis a}"

lemma mub_closed_dfixes:
  assumes "deflation d"
  shows "mub_closed (dfixes d)"
proof (intro mub_closedI)
  let ?R = Rep_compact_basis
  fix S s assume fin: "finite S" and "S \<subseteq> dfixes d" "is_mub S s"
  from \<open>finite S\<close> \<open>is_mub S s\<close> have "is_mub (?R ` S) (?R s)"
    by (rule mub_compact_basis_fwd)
  moreover from \<open>S \<subseteq> dfixes d\<close> have "?R ` S \<subseteq> {x. d\<cdot>x = x}"
    unfolding dfixes_def by auto
  ultimately have "?R s \<in> {x. d\<cdot>x = x}"
    using deflation_fixes_mub_closed[OF assms, THEN mub_closedD]
      fin[THEN finite_imageI] by fast
  then show "s \<in> dfixes d" by (simp add: dfixes_def)
qed


lemma mub_closed_basis_dfixes:
  assumes "deflation d"
  shows "mub_closed_basis (dfixes d)"
  unfolding mub_closed_basis_def
  using mub_closed_dfixes[OF assms] by blast

lemma finite_dfixes:
  assumes "finite_deflation d"
  shows "finite (dfixes d)"
proof -
  have "inj_on Rep_compact_basis (dfixes d)"
    by (meson compact_basis.Rep_compact_basis_inject inj_onI)
  moreover have "Rep_compact_basis ` dfixes d \<subseteq> {x. d\<cdot>x = x}"
    unfolding dfixes_def by auto
  moreover have "finite {x. d\<cdot>x = x}" using assms by (rule finite_deflation.finite_fixes)
  ultimately show ?thesis by (meson finite_imageD finite_subset)
qed


text \<open>Reconstruction: a finite deflation is recovered from its own compact fixed
  points by the @{locale mub_closed_basis} construction.  Thus \<open>dfixes\<close> and
  \<open>defl_of_set\<close> are mutually inverse between finite deflations and finite MUB-closed
  sets containing @{term \<open>\<bottom>\<close>}.\<close>

lemma defl_of_dfixes:
  assumes "finite_deflation d"
  shows "mub_closed_basis.d (dfixes d) = d"
proof -
  from assms have defld: "deflation d" by (rule finite_deflation_imp_deflation)
  interpret L: mub_closed_basis "dfixes d"
    by (rule mub_closed_basis_dfixes[OF defld])
  have fin: "finite (dfixes d)" using assms by (rule finite_dfixes)
  have defle: "deflation L.d" by (rule L.deflation_d)
  have fde: "finite_deflation L.d" by (rule L.finite_deflation_d[OF fin])
  have eq_fixes: "L.d\<cdot>x = x \<longleftrightarrow> d\<cdot>x = x" for x
  proof
    assume "d\<cdot>x = x"
    moreover have "compact (d\<cdot>x)" by (rule finite_deflation.compact[OF assms])
    ultimately have "compact x" by simp
    then obtain a where xa: "x = Rep_compact_basis a"
      using compact_basis.compact_imp_principal by blast
    from \<open>d\<cdot>x = x\<close> xa have "a \<in> dfixes d" unfolding dfixes_def by simp
    thus "L.d\<cdot>x = x" using xa L.d_fixes by simp
  next
    assume "L.d\<cdot>x = x"
    moreover have "compact (L.d\<cdot>x)" by (rule finite_deflation.compact[OF fde])
    ultimately have "compact x" by simp
    then obtain a where xa: "x = Rep_compact_basis a"
      using compact_basis.compact_imp_principal by blast
    from \<open>L.d\<cdot>x = x\<close> xa have "a \<in> dfixes d" using L.d_fixes by simp
    thus "d\<cdot>x = x" using xa unfolding dfixes_def by simp
  qed
  show "L.d = d"
  proof (rule below_antisym)
    show "L.d \<sqsubseteq> d"
    proof (rule deflation_belowI_fixes[OF defld defle])
      fix x assume "L.d\<cdot>x = x" thus "d\<cdot>x = x" using eq_fixes by simp
    qed
    show "d \<sqsubseteq> L.d"
    proof (rule deflation_belowI_fixes[OF defle defld])
      fix x assume "d\<cdot>x = x" thus "L.d\<cdot>x = x" using eq_fixes by simp
    qed
  qed
qed

text \<open>The MUB-closure of any set containing @{term \<open>\<bottom>\<close>} satisfies the locale
  assumptions, so it determines a deflation.\<close>

lemma mub_closed_basis_mub_closure:
  shows "mub_closed_basis (mub_closure T)"
  unfolding mub_closed_basis_def
  using mub_closed_mub_closure by blast

text \<open>Pairwise join of finite deflations: the deflation determined by the MUB-closure
  of the union of their fixed-point sets.  By the lattice-embedding (fixed points
  ordered by inclusion) this is the least upper bound.\<close>

definition join_fin_defl :: "'a::bifinite fin_defl \<Rightarrow> 'a fin_defl \<Rightarrow> 'a fin_defl"
  where "join_fin_defl A B =
    Abs_fin_defl (mub_closed_basis.d
      (mub_closure (dfixes (Rep_fin_defl A) \<union> dfixes (Rep_fin_defl B))))"

lemma join_fin_defl_aux:
  fixes A B :: "'a::bifinite fin_defl"
  defines "U \<equiv> mub_closure (dfixes (Rep_fin_defl A) \<union> dfixes (Rep_fin_defl B))"
  shows "mub_closed_basis U" (is ?P1)
    and "finite U" (is ?P2)
    and "finite_deflation (mub_closed_basis.d U)" (is ?P3)
    and "Rep_fin_defl (join_fin_defl A B) = mub_closed_basis.d U" (is ?P4)
proof -
  have finA: "finite (dfixes (Rep_fin_defl A))"
    by (rule finite_dfixes[OF finite_deflation_Rep_fin_defl])
  have finB: "finite (dfixes (Rep_fin_defl B))"
    by (rule finite_dfixes[OF finite_deflation_Rep_fin_defl])
  show P1: ?P1 unfolding U_def by (rule mub_closed_basis_mub_closure)
  show P2: ?P2 unfolding U_def
    using finite_mub_closure_cb[of "dfixes (Rep_fin_defl A) \<union> dfixes (Rep_fin_defl B)"]
      finA finB by simp
  show P3: ?P3 by (rule mub_closed_basis.finite_deflation_d[OF P1 P2])
  show ?P4 unfolding join_fin_defl_def U_def[symmetric]
    by (metis P3 Abs_fin_defl_inverse mem_Collect_eq)
qed

lemma dfixes_mub_closed_basis_d:
  assumes "mub_closed_basis S"
  shows "dfixes (mub_closed_basis.d S) = S"
  unfolding dfixes_def using mub_closed_basis.d_fixes[OF assms] by auto

text \<open>The order on finite deflations is inclusion of their fixed-point sets — the
  promised lattice embedding into the MUB-closed sets.\<close>

lemma fin_defl_below_dfixes:
  fixes A B :: "'a::bifinite fin_defl"
  shows "A \<sqsubseteq> B \<longleftrightarrow> dfixes (Rep_fin_defl A) \<subseteq> dfixes (Rep_fin_defl B)"
proof
  assume "A \<sqsubseteq> B"
  thus "dfixes (Rep_fin_defl A) \<subseteq> dfixes (Rep_fin_defl B)"
    unfolding dfixes_def using fin_defl_belowD by auto
next
  assume sub: "dfixes (Rep_fin_defl A) \<subseteq> dfixes (Rep_fin_defl B)"
  show "A \<sqsubseteq> B"
  proof (rule fin_defl_belowI)
    fix x assume "Rep_fin_defl A\<cdot>x = x"
    moreover have "compact (Rep_fin_defl A\<cdot>x)"
      by (rule finite_deflation.compact[OF finite_deflation_Rep_fin_defl])
    ultimately have "compact x" by simp
    then obtain a where xa: "x = Rep_compact_basis a"
      using compact_basis.compact_imp_principal by blast
    from \<open>Rep_fin_defl A\<cdot>x = x\<close> xa have "a \<in> dfixes (Rep_fin_defl A)"
      unfolding dfixes_def by simp
    with sub have "a \<in> dfixes (Rep_fin_defl B)" by blast
    thus "Rep_fin_defl B\<cdot>x = x" using xa unfolding dfixes_def by simp
  qed
qed

lemma dfixes_join_fin_defl:
  fixes A B :: "'a::bifinite fin_defl"
  shows "dfixes (Rep_fin_defl (join_fin_defl A B)) =
         mub_closure (dfixes (Rep_fin_defl A) \<union> dfixes (Rep_fin_defl B))"
  using join_fin_defl_aux(4)[of A B]
    dfixes_mub_closed_basis_d[OF join_fin_defl_aux(1)[of A B]] by simp

lemma join_fin_defl_above1: "A \<sqsubseteq> join_fin_defl A B"
  unfolding fin_defl_below_dfixes dfixes_join_fin_defl
  using mub_closure_extensive by blast

lemma join_fin_defl_above2: "B \<sqsubseteq> join_fin_defl A B"
  unfolding fin_defl_below_dfixes dfixes_join_fin_defl
  using mub_closure_extensive by blast

lemma join_fin_defl_least:
  assumes "A \<sqsubseteq> C" and "B \<sqsubseteq> C"
  shows "join_fin_defl A B \<sqsubseteq> C"
proof -
  have "dfixes (Rep_fin_defl A) \<union> dfixes (Rep_fin_defl B) \<subseteq> dfixes (Rep_fin_defl C)"
    using assms unfolding fin_defl_below_dfixes by blast
  hence "mub_closure (dfixes (Rep_fin_defl A) \<union> dfixes (Rep_fin_defl B))
           \<subseteq> dfixes (Rep_fin_defl C)"
    by (rule mub_closure_least[OF _ mub_closed_dfixes[OF deflation_Rep_fin_defl]])
  thus ?thesis unfolding fin_defl_below_dfixes dfixes_join_fin_defl .
qed

section \<open>Reconstructing an arbitrary deflation from its compact fixed points\<close>

text \<open>The @{locale mub_closed_basis} locale assumes only \<open>mub_closed S\<close> and
  @{term \<open>Abs_compact_basis \<bottom> \<in> S\<close>}; it does \emph{not} require @{term S} finite.
  Hence for \emph{any} deflation @{term d} the set @{term \<open>dfixes d\<close>} of compact
  fixed points determines a deflation @{term \<open>mub_closed_basis.d (dfixes d)\<close>}.  The
  \<open>\<sqsubseteq>\<close>-direction holds without any bifinite approximation machinery.\<close>

lemma defl_of_dfixes_below:
  assumes "deflation d"
  shows "mub_closed_basis.d (dfixes d) \<sqsubseteq> d"
proof -
  interpret L: mub_closed_basis "dfixes d"
    by (rule mub_closed_basis_dfixes[OF assms])
  have "L.d\<cdot>x \<sqsubseteq> d\<cdot>x" for x
  proof -
    have "Rep_compact_basis ` L.below_set x <| d\<cdot>x"
    proof (rule is_ubI)
      fix y assume "y \<in> Rep_compact_basis ` L.below_set x"
      then obtain b where b: "b \<in> L.below_set x" "y = Rep_compact_basis b" by blast
      from b(1) have "b \<in> dfixes d" and "Rep_compact_basis b \<sqsubseteq> x"
        unfolding L.below_set_def by auto
      from \<open>b \<in> dfixes d\<close> have "d\<cdot>(Rep_compact_basis b) = Rep_compact_basis b"
        unfolding dfixes_def by simp
      moreover from \<open>Rep_compact_basis b \<sqsubseteq> x\<close>
      have "d\<cdot>(Rep_compact_basis b) \<sqsubseteq> d\<cdot>x" by (rule monofun_cfun_arg)
      ultimately show "y \<sqsubseteq> d\<cdot>x" using b(2) by simp
    qed
    with L.d_lub show "L.d\<cdot>x \<sqsubseteq> d\<cdot>x" using is_lub_below_iff by blast
  qed
  thus ?thesis by (rule cfun_belowI)
qed

(* ===================================================================== *)
(*  Algebraic deflations are determined by their compact fixes           *)
(*                                                                       *)
(*  'cast' is injective (Algebraic.cast_eq_imp_eq), but more is true:    *)
(*  an algebraic deflation 'cast A' is the directed lub of the finite    *)
(*  deflations 'Rep_fin_defl a' in its defining ideal, so it is pinned   *)
(*  down already by which COMPACT elements it fixes, i.e. by 'dfixes'.   *)
(* ===================================================================== *)

text \<open>Each finite deflation in the defining ideal of @{term A} lies below
  @{term \<open>cast\<cdot>A\<close>}.\<close>

lemma Rep_fin_defl_below_cast:
  assumes "a \<in> Rep_defl A"
  shows "Rep_fin_defl a \<sqsubseteq> cast\<cdot>A"
proof -
  from assms have "defl_principal a \<sqsubseteq> A"
    by (simp add: defl.principal_below_iff_mem_rep)
  hence "cast\<cdot>(defl_principal a) \<sqsubseteq> cast\<cdot>A" by (rule monofun_cfun_arg)
  thus ?thesis by (simp add: cast_defl_principal)
qed

text \<open>Larger algebraic deflations fix more compacts (this direction is just
  monotonicity of @{term cast}).\<close>

lemma dfixes_cast_mono:
  assumes "A \<sqsubseteq> B"
  shows "dfixes (cast\<cdot>A) \<subseteq> dfixes (cast\<cdot>B)"
proof
  fix b assume "b \<in> dfixes (cast\<cdot>A)"
  hence fx: "cast\<cdot>A\<cdot>(Rep_compact_basis b) = Rep_compact_basis b"
    by (simp add: dfixes_def)
  from assms have "cast\<cdot>A \<sqsubseteq> cast\<cdot>B" by (rule monofun_cfun_arg)
  hence "cast\<cdot>A\<cdot>(Rep_compact_basis b) \<sqsubseteq> cast\<cdot>B\<cdot>(Rep_compact_basis b)"
    by (rule monofun_cfun_fun)
  with fx have le: "Rep_compact_basis b \<sqsubseteq> cast\<cdot>B\<cdot>(Rep_compact_basis b)" by simp
  have "cast\<cdot>B\<cdot>(Rep_compact_basis b) = Rep_compact_basis b"
  proof (rule below_antisym)
    show "cast\<cdot>B\<cdot>(Rep_compact_basis b) \<sqsubseteq> Rep_compact_basis b" by (rule cast.below)
    show "Rep_compact_basis b \<sqsubseteq> cast\<cdot>B\<cdot>(Rep_compact_basis b)" by (rule le)
  qed
  thus "b \<in> dfixes (cast\<cdot>B)" by (simp add: dfixes_def)
qed

text \<open>The converse is the substantive direction: an inclusion of compact fixes
  forces the deflation order.  We test each finite deflation @{term \<open>Rep_fin_defl a\<close>}
  in the ideal of @{term A} against @{term \<open>cast\<cdot>B\<close>} using
  @{thm [source] finite_deflation.compact_belowI}, which only inspects compact
  fixed points.\<close>

lemma defl_below_of_dfixes:
  assumes sub: "dfixes (cast\<cdot>A) \<subseteq> dfixes (cast\<cdot>B)"
  shows "A \<sqsubseteq> B"
proof (unfold below_defl_def, rule subsetI)
  fix a assume aA: "a \<in> Rep_defl A"
  have ra: "Rep_fin_defl a \<sqsubseteq> cast\<cdot>A" using aA by (rule Rep_fin_defl_below_cast)
  have "Rep_fin_defl a \<sqsubseteq> cast\<cdot>B"
  proof (rule Rep_fin_defl.compact_belowI)
    fix x assume cx: "compact x" and fx: "Rep_fin_defl a\<cdot>x = x"
    have caAx: "cast\<cdot>A\<cdot>x = x"
    proof (rule below_antisym)
      show "cast\<cdot>A\<cdot>x \<sqsubseteq> x" by (rule cast.below)
      have "Rep_fin_defl a\<cdot>x \<sqsubseteq> cast\<cdot>A\<cdot>x" by (rule monofun_cfun_fun[OF ra])
      with fx show "x \<sqsubseteq> cast\<cdot>A\<cdot>x" by simp
    qed
    let ?b = "Abs_compact_basis x"
    from cx have rb: "Rep_compact_basis ?b = x" by simp
    with caAx have "cast\<cdot>A\<cdot>(Rep_compact_basis ?b) = Rep_compact_basis ?b" by simp
    hence "?b \<in> dfixes (cast\<cdot>A)" by (simp add: dfixes_def)
    with sub have "?b \<in> dfixes (cast\<cdot>B)" ..
    hence "cast\<cdot>B\<cdot>(Rep_compact_basis ?b) = Rep_compact_basis ?b"
      by (simp add: dfixes_def)
    with rb show "cast\<cdot>B\<cdot>x = x" by simp
  qed
  hence "cast\<cdot>(defl_principal a) \<sqsubseteq> cast\<cdot>B" by (simp add: cast_defl_principal)
  hence "defl_principal a \<sqsubseteq> B" by (rule cast_below_imp_below)
  thus "a \<in> Rep_defl B" by (simp add: defl.principal_below_iff_mem_rep)
qed

text \<open>Hence the compact-fixes map is an order embedding of @{typ \<open>'a defl\<close>} into
  sets of compact basis elements, and in particular injective: an algebraic
  deflation is completely determined by the compacts it fixes.\<close>

theorem defl_below_iff_dfixes:
  "A \<sqsubseteq> B \<longleftrightarrow> dfixes (cast\<cdot>A) \<subseteq> dfixes (cast\<cdot>B)"
  using dfixes_cast_mono defl_below_of_dfixes by blast

theorem defl_eq_iff_dfixes:
  "A = B \<longleftrightarrow> dfixes (cast\<cdot>A) = dfixes (cast\<cdot>B)"
  by (metis below_antisym defl_below_iff_dfixes set_eq_subset)
end
