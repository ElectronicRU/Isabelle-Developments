theory Deflations
  imports MUB_Closure
begin

(* ===================================================================== *)
(*  The lattice of finite deflations, and 'a defl by compact fixes       *)
(*                                                                       *)
(*  Built on MUB_Closure (the mub-closure machinery + the 'defl_of_set'  *)
(*  locale that turns a mub-closed set of compacts into a deflation).    *)
(*                                                                       *)
(*  - fin_defl order is fixed-point inclusion; pairwise joins exist      *)
(*    ('join_fin_defl' = defl_of_set of the mub-closure of the union of  *)
(*    fixed points), so finite deflations form a lattice.                *)
(*  - cast :: 'a defl \<rightarrow> ('a \<rightarrow> 'a) is injective (Algebraic.cast_eq_imp_eq)*)
(*    but NOT surjective onto {d. deflation d}: a deflation is the lub    *)
(*    of the finite deflations below it iff its image is bifinite, and    *)
(*    bifinite domains are not closed under retracts (RB ⊋ B, cf. Jung). *)
(*  - what IS true: an algebraic deflation 'cast A' is pinned down by     *)
(*    which COMPACT elements it fixes.  Writing 'dfixes d':              *)
(*      defl_below_iff_dfixes : A \<sqsubseteq> B \<longleftrightarrow> dfixes (cast A) \<subseteq> dfixes (cast B)*)
(*      defl_eq_iff_dfixes    : A = B \<longleftrightarrow> dfixes (cast A) = dfixes (cast B)*)
(*    i.e. 'dfixes o cast' is an order embedding of 'a defl into sets of  *)
(*    compact basis elements.                                            *)
(* ===================================================================== *)


section \<open>The lattice of finite deflations\<close>

text \<open>A deflation is below another exactly when its fixed-point set is contained
  in the other's.  This is the order-theoretic content behind @{const cast} being
  an order-embedding, phrased for raw deflations.\<close>

lemma deflation_belowI_fixes:
  assumes d: "deflation d" and e: "deflation e"
    and fx: "\<And>x. e\<cdot>x = x \<Longrightarrow> d\<cdot>x = x"
  shows "e \<sqsubseteq> d"
  using e fx by (rule deflation.belowI)

text \<open>The compact fixed points of a deflation, as a set of basis elements.  This set
  is MUB-closed (@{thm [source] deflation_fixes_mub_closed}) and contains @{term \<open>\<bottom>\<close>},
  so it satisfies the assumptions of the @{locale mub_closed_basis} locale.\<close>

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
    by (rule below_antisym; rule deflation_belowI_fixes) (simp_all add: eq_fixes defld defle)
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

section \<open>Algebraic deflations are determined by their compact fixes\<close>

text \<open>@{const cast} is injective but not surjective onto all deflations: only a
  deflation whose image is bifinite is the lub of the finite deflations below it.
  Still, an algebraic deflation @{term \<open>cast\<cdot>A\<close>} is the directed lub of the finite
  deflations in its defining ideal, so it is pinned down by which COMPACT elements
  it fixes, i.e. by @{term \<open>dfixes (cast\<cdot>A)\<close>}.\<close>

text \<open>Each finite deflation in the defining ideal of @{term A} lies below
  @{term \<open>cast\<cdot>A\<close>}.\<close>

lemma Rep_fin_defl_below_cast:
  assumes "a \<in> Rep_defl A"
  shows "Rep_fin_defl a \<sqsubseteq> cast\<cdot>A"
  using assms by (metis cast_defl_principal cast_below_cast defl.principal_below_iff_mem_rep)

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
      using fx ra cast.belowD by fastforce
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
