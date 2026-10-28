theory Algebraic_Semi_Factor
  imports Subdomain "HOLCF-extra.DI" "HOLCF-extra.Algebraic_Lattice" "HOL-Library.Countable_Set"
begin

section \<open>Semi-factors over dI-domains\<close>

text \<open>Over a dI-domain the meet of any non-empty family of semi-factor deflations is again a
  semi-factor deflation.  Its image is the intersection of the images and it is stable
  (@{thm [source] stable_defl_glb}), so only the slide rule needs proof.  At a compact argument
  the family takes only finitely many values, and a finite subfamily, whose meet is a semi-factor
  by @{thm [source] semi_factor_defl_oo}, gives the slide rule there; algebraicity extends it to
  all arguments.\<close>

text \<open>Joinability with a fixed element is admissible: a chain bounded with \<open>y\<close> stays below the
  chain of joins with \<open>y\<close>.\<close>

lemma adm_joinable: "adm (\<lambda>x. x \<Up> (y :: 'a::bounded_complete))"
proof (rule admI)
  fix Y :: "nat \<Rightarrow> 'a" assume Y: "chain Y" and J: "\<forall>i. Y i \<Up> y"
  have ch: "chain (\<lambda>i. Y i \<squnion> y)"
    by (rule chainI, rule join_mono1) (simp_all add: J chainE[OF Y])
  show "(\<Squnion>i. Y i) \<Up> y"
  proof (rule joinableI)
    show "(\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. Y i \<squnion> y)" by (rule lub_mono[OF Y ch]) (simp add: J joinableD(1))
    show "y \<sqsubseteq> (\<Squnion>i. Y i \<squnion> y)"
      by (rule below_trans[OF joinableD(2)[OF J[rule_format]] is_ub_thelub[OF ch]])
  qed
qed

lemma semi_factor_defl_finite_meet:
  fixes F :: "('a::{bifinite, distributive_cpo} \<rightarrow> 'a) set"
  assumes "finite F" and "\<And>d. d \<in> F \<Longrightarrow> semi_factor_defl d"
  shows "\<exists>e. semi_factor_defl e \<and> (\<forall>z. e\<cdot>z = z \<longleftrightarrow> (\<forall>d\<in>F. d\<cdot>z = z))"
  using assms
proof (induct F rule: finite_induct)
  case empty
  show ?case by (intro exI[of _ ID] conjI) (simp_all add: semi_factor_defl_ID)
next
  case (insert d F)
  then obtain e where e: "semi_factor_defl e" and efx: "\<forall>z. e\<cdot>z = z \<longleftrightarrow> (\<forall>d\<in>F. d\<cdot>z = z)"
    by blast
  have d: "semi_factor_defl d" using insert.prems by simp
  note fx = stable_defl_oo_fixed[OF semi_factor_defl.axioms(1)[OF d] semi_factor_defl.axioms(1)[OF e]]
  show ?case
  proof (intro exI[of _ "d oo e"] conjI allI)
    show "semi_factor_defl (d oo e)" by (rule semi_factor_defl_oo[OF d e])
    show "(d oo e)\<cdot>z = z \<longleftrightarrow> (\<forall>d'\<in>insert d F. d'\<cdot>z = z)" for z using fx efx by simp
  qed
qed

lemma semi_factor_defl_glb_compact:
  fixes \<D> :: "('a::dI \<rightarrow> 'a) set"
  assumes ne: "\<D> \<noteq> {}" and sf: "\<And>d. d \<in> \<D> \<Longrightarrow> semi_factor_defl d"
    and k: "compact x" and y: "glb \<D>\<cdot>y = y" and xy: "glb \<D>\<cdot>x \<sqsubseteq> y"
  shows "x \<Up> y"
proof -
  have st: "\<And>d. d \<in> \<D> \<Longrightarrow> stable_defl d" by (rule semi_factor_defl.axioms(1)[OF sf])
  note fx = stable_defl_glb_fixes[OF ne st]
  have "(\<lambda>d. d\<cdot>x) ` \<D> \<subseteq> {z. z \<sqsubseteq> x}"
    using st by (auto intro: deflation.below stable_defl.deflation)
  then have "finite ((\<lambda>d. d\<cdot>x) ` \<D>)" by (rule finite_subset) (rule finite_below_compact[OF k])
  then have "\<exists>F\<subseteq>\<D>. finite F \<and> (\<lambda>d. d\<cdot>x) ` \<D> = (\<lambda>d. d\<cdot>x) ` F"
    by (rule finite_subset_image[OF _ subset_refl])
  then obtain F where F: "F \<subseteq> \<D>" "finite F" and FD: "(\<lambda>d. d\<cdot>x) ` \<D> = (\<lambda>d. d\<cdot>x) ` F"
    by (elim exE conjE) (rule that)
  obtain e where e: "semi_factor_defl e" and efx: "\<And>z. e\<cdot>z = z \<longleftrightarrow> (\<forall>d\<in>F. d\<cdot>z = z)"
    using semi_factor_defl_finite_meet[OF F(2)] sf F(1) by blast
  interpret e: semi_factor_defl e by (rule e)
  have exF: "d\<cdot>(e\<cdot>x) = e\<cdot>x" if "d \<in> F" for d using efx[of "e\<cdot>x"] e.idem that by blast
  have "d\<cdot>(e\<cdot>x) = e\<cdot>x" if d: "d \<in> \<D>" for d
  proof -
    have "d\<cdot>x \<in> (\<lambda>d. d\<cdot>x) ` F" using FD d by blast
    then obtain d' where d': "d' \<in> F" "d\<cdot>x = d'\<cdot>x" by blast
    have "e\<cdot>x = d'\<cdot>(e\<cdot>x)" using exF[OF d'(1)] by simp
    also have "\<dots> \<sqsubseteq> d'\<cdot>x" by (rule monofun_cfun_arg[OF e.below])
    finally have "e\<cdot>x \<sqsubseteq> d\<cdot>x" using d'(2) by simp
    then show ?thesis by (rule stable_defl.lower_fixed[OF st[OF d]])
  qed
  then have "glb \<D>\<cdot>(e\<cdot>x) = e\<cdot>x" using fx by blast
  then have "e\<cdot>x \<sqsubseteq> glb \<D>\<cdot>x" by (metis monofun_cfun_arg e.below)
  then have "e\<cdot>x \<sqsubseteq> y" using xy by (rule below_trans)
  moreover have "e\<cdot>y = y" using efx y fx F(1) by blast
  ultimately show "x \<Up> y" using e.slide by blast
qed

lemma semi_factor_defl_glb:
  fixes \<D> :: "('a::dI \<rightarrow> 'a) set"
  assumes ne: "\<D> \<noteq> {}" and sf: "\<And>d. d \<in> \<D> \<Longrightarrow> semi_factor_defl d"
  shows "semi_factor_defl (glb \<D>)"
proof (rule semi_factor_deflI)
  have st: "\<And>d. d \<in> \<D> \<Longrightarrow> stable_defl d" by (rule semi_factor_defl.axioms(1)[OF sf])
  show "stable_defl (glb \<D>)" by (rule stable_defl_glb[OF ne st])
  fix x y assume y: "glb \<D>\<cdot>y = y" and xy: "glb \<D>\<cdot>x \<sqsubseteq> y"
  obtain a :: "nat \<Rightarrow> 'a \<rightarrow> 'a" where a: "approx_chain a" using bifinite by blast
  interpret approx_chain a by (fact a)
  have ch: "chain (\<lambda>i. a i\<cdot>x)" by (rule ch2ch_Rep_cfunL[OF chain_approx])
  have "a i\<cdot>x \<Up> y" for i
    by (rule semi_factor_defl_glb_compact[OF ne sf compact_approx y])
      (blast, rule below_trans[OF monofun_cfun_arg[OF approx_below] xy])
  then have "(\<Squnion>i. a i\<cdot>x) \<Up> y" by (rule admD[OF adm_joinable ch])
  then show "x \<Up> y" by (simp add: contlub_cfun_fun[OF chain_approx, symmetric])
qed


subsection \<open>Meets of semi-factors\<close>

text \<open>Over a dI key the meet of a non-empty set of semi-factors is computed pointwise: its
  projection is the glb of the projections, so its image is the intersection of the images.\<close>

lemma semi_factor_p_glb:
  fixes \<A> :: "'a::dI semi_factor set"
  assumes ne: "\<A> \<noteq> {}"
  shows "semi_factor_p (glb \<A>) = (\<Sqinter>A\<in>\<A>. semi_factor_p A)"
proof -
  let ?P = "semi_factor_p ` \<A>"
  have neP: "?P \<noteq> {}" using ne by blast
  have sfd: "semi_factor_defl (glb ?P)"
    by (rule semi_factor_defl_glb[OF neP]) (auto intro: semi_factor_defl_semi_factor_p)
  have "glb \<A> = semi_factor_of_defl (glb ?P)"
  proof (rule glb_eqI, rule is_glbI)
    show "semi_factor_of_defl (glb ?P) \<sqsubseteq> A" if "A \<in> \<A>" for A
      unfolding semi_factor_below_iff_p semi_factor_p_of_defl[OF sfd]
      by (rule glb_below) (use that in blast)
    show "B \<sqsubseteq> semi_factor_of_defl (glb ?P)" if "\<forall>A\<in>\<A>. B \<sqsubseteq> A" for B
      unfolding semi_factor_below_iff_p semi_factor_p_of_defl[OF sfd]
      by (rule glb_greatest[OF neP]) (use that in \<open>auto simp: semi_factor_below_iff_p\<close>)
  qed
  then show ?thesis by (simp add: semi_factor_p_of_defl[OF sfd])
qed

subsection \<open>Algebraicity\<close>

lemma countable_compacts: "countable {x :: 'a::bifinite. compact x}"
proof -
  obtain f :: "'a compact_basis \<Rightarrow> nat" where "inj f" using compact_basis.countable ..
  then have "countable (range (Rep_compact_basis :: 'a compact_basis \<Rightarrow> 'a))"
    by (rule countable_image[OF countableI])
  moreover have "range (Rep_compact_basis :: 'a compact_basis \<Rightarrow> 'a) = {x. compact x}"
    using type_definition_compact_basis by (rule type_definition.Rep_range)
  ultimately show ?thesis by simp
qed

lemma stable_defl_semi_factor_p: "stable_defl (semi_factor_p F)"
  by (rule semi_factor_defl.axioms(1)[OF semi_factor_defl_semi_factor_p])

lemma deflation_semi_factor_p: "deflation (semi_factor_p F)"
  by (rule stable_defl.deflation[OF stable_defl_semi_factor_p])

lemma semi_factor_p_mono: "F \<sqsubseteq> G \<Longrightarrow> semi_factor_p F\<cdot>x \<sqsubseteq> semi_factor_p G\<cdot>x"
  by (rule monofun_cfun_fun) (simp add: semi_factor_below_iff_p[symmetric])

text \<open>Projections onto a lub of semi-factors are pointwise lubs (@{thm [source] proj_Sup}).\<close>

lemma semi_factor_p_lub_is_lub: "(\<lambda>F. semi_factor_p F\<cdot>x) ` \<X> <<| semi_factor_p (lub \<X>)\<cdot>x"
proof -
  have "lub \<X> = Sup \<X>" by (rule lub_eqI[OF semi_factor_is_lub])
  then have "semi_factor_p (lub \<X>) = stable_subdom_p (Sup (subdom_of_semi_factor ` \<X>))"
    by (simp add: semi_factor_p.rep_eq Sup_semi_factor.rep_eq)
  moreover have "(\<lambda>F. semi_factor_p F\<cdot>x) ` \<X> = (\<lambda>A. stable_subdom_p A\<cdot>x) ` (subdom_of_semi_factor ` \<X>)"
    by (simp add: image_image semi_factor_p.rep_eq)
  ultimately show ?thesis using proj_Sup[where \<A> = "subdom_of_semi_factor ` \<X>" and x = x] by simp
qed

lemma semi_factor_p_chain_lub: "semi_factor_p (\<Squnion>i. Y i)\<cdot>x = (\<Squnion>i. semi_factor_p (Y i)\<cdot>x)"
proof -
  have "range (\<lambda>i. semi_factor_p (Y i)\<cdot>x) <<| semi_factor_p (\<Squnion>i. Y i)\<cdot>x"
    using semi_factor_p_lub_is_lub[where \<X> = "range Y" and x = x] by (simp add: image_image)
  then show ?thesis by (rule lub_eqI[symmetric])
qed

text \<open>The principal semi-factor of \<open>x\<close>: the least one containing \<open>x\<close>.  Over a dI key its image is
  the intersection of the images containing \<open>x\<close> (@{thm [source] semi_factor_p_glb}).\<close>

definition semi_factor_principal :: "'a::dI \<Rightarrow> 'a semi_factor" where
  "semi_factor_principal x = glb {F. semi_factor_p F\<cdot>x = x}"

lemma semi_factor_principal_fixes:
  "semi_factor_p (semi_factor_principal x)\<cdot>y = y \<longleftrightarrow>
    (\<forall>F. semi_factor_p F\<cdot>x = x \<longrightarrow> semi_factor_p F\<cdot>y = y)"
proof -
  let ?A = "{F :: 'a semi_factor. semi_factor_p F\<cdot>x = x}"
  have "semi_factor_of_defl ID \<in> ?A" by (simp add: semi_factor_p_of_defl semi_factor_defl_ID)
  then have ne: "?A \<noteq> {}" by blast
  have "semi_factor_p (semi_factor_principal x) = glb (semi_factor_p ` ?A)"
    unfolding semi_factor_principal_def by (rule semi_factor_p_glb[OF ne])
  moreover have "glb (semi_factor_p ` ?A)\<cdot>y = y \<longleftrightarrow> (\<forall>d\<in>semi_factor_p ` ?A. d\<cdot>y = y)"
    by (rule stable_defl_glb_fixes) (use ne in \<open>auto intro: stable_defl_semi_factor_p\<close>)
  ultimately show ?thesis by auto
qed

lemma semi_factor_principal_self: "semi_factor_p (semi_factor_principal x)\<cdot>x = x"
  by (simp add: semi_factor_principal_fixes)

lemma semi_factor_principal_below_iff: "semi_factor_principal x \<sqsubseteq> F \<longleftrightarrow> semi_factor_p F\<cdot>x = x"
proof
  assume "semi_factor_principal x \<sqsubseteq> F"
  then have "semi_factor_p (semi_factor_principal x)\<cdot>x \<sqsubseteq> semi_factor_p F\<cdot>x"
    by (rule semi_factor_p_mono)
  then have "x \<sqsubseteq> semi_factor_p F\<cdot>x" by (simp add: semi_factor_principal_self)
  then show "semi_factor_p F\<cdot>x = x" by (rule below_antisym[OF deflation.below[OF deflation_semi_factor_p]])
next
  assume "semi_factor_p F\<cdot>x = x"
  then show "semi_factor_principal x \<sqsubseteq> F" unfolding semi_factor_principal_def by (intro glb_below) simp
qed

lemma compact_semi_factor_principal:
  assumes k: "compact k"
  shows "compact (semi_factor_principal k)"
proof (rule compactI2)
  fix Y :: "nat \<Rightarrow> 'a semi_factor" assume Y: "chain Y" and le: "semi_factor_principal k \<sqsubseteq> (\<Squnion>i. Y i)"
  have ch: "chain (\<lambda>i. semi_factor_p (Y i)\<cdot>k)" by (rule chainI, rule semi_factor_p_mono, rule chainE[OF Y])
  have "k = semi_factor_p (\<Squnion>i. Y i)\<cdot>k" using le by (simp add: semi_factor_principal_below_iff)
  also have "\<dots> = (\<Squnion>i. semi_factor_p (Y i)\<cdot>k)" by (rule semi_factor_p_chain_lub)
  finally have "k \<sqsubseteq> (\<Squnion>i. semi_factor_p (Y i)\<cdot>k)" by simp
  then obtain i where "k \<sqsubseteq> semi_factor_p (Y i)\<cdot>k" using compactD2[OF k ch] by blast
  then have "semi_factor_p (Y i)\<cdot>k = k" by (rule below_antisym[OF deflation.below[OF deflation_semi_factor_p]])
  then have "semi_factor_principal k \<sqsubseteq> Y i" by (simp add: semi_factor_principal_below_iff)
  then show "\<exists>i. semi_factor_principal k \<sqsubseteq> Y i" by blast
qed

text \<open>Every semi-factor is the lub of the principals of its compact elements: its image is
  downward closed and the projection onto the lub fixes every compact of it, hence every element.\<close>

lemma semi_factor_lub_principals:
  "F = lub {semi_factor_principal k | k. compact k \<and> semi_factor_p F\<cdot>k = k}" (is "F = lub ?P")
proof (rule below_antisym)
  show "lub ?P \<sqsubseteq> F" by (rule lattice_lub_least) (auto simp: is_ub_def semi_factor_principal_below_iff)
  show "F \<sqsubseteq> lub ?P"
  proof (simp only: semi_factor_below_iff_p, rule cfun_belowI)
    fix x
    let ?Z = "lub ?P" and ?y = "semi_factor_p F\<cdot>x"
    have fix_Z: "semi_factor_p ?Z\<cdot>k = k" if "compact k" "semi_factor_p F\<cdot>k = k" for k
    proof -
      have "semi_factor_principal k \<sqsubseteq> ?Z" by (rule lattice_lub_upper) (use that in blast)
      then show ?thesis by (simp add: semi_factor_principal_below_iff)
    qed
    obtain C where C: "chain C" "\<forall>i. compact (C i)" "?y = (\<Squnion>i. C i)" by (rule obtain_compact_chain)
    have fixF: "semi_factor_p F\<cdot>(C i) = C i" for i
    proof -
      have "C i \<sqsubseteq> semi_factor_p F\<cdot>x" using is_ub_thelub[OF C(1)] C(3) by simp
      then show ?thesis by (rule stable_defl.lower_fixed[OF stable_defl_semi_factor_p])
    qed
    have "semi_factor_p ?Z\<cdot>?y = (\<Squnion>i. semi_factor_p ?Z\<cdot>(C i))"
      unfolding C(3) by (rule contlub_cfun_arg[OF C(1)])
    also have "\<dots> = (\<Squnion>i. C i)" using C(2) fixF by (simp add: fix_Z)
    also have "\<dots> = ?y" by (simp add: C(3))
    finally have yZ: "semi_factor_p ?Z\<cdot>?y = ?y" .
    have "?y \<sqsubseteq> x" by (rule deflation.below[OF deflation_semi_factor_p])
    then have "semi_factor_p ?Z\<cdot>?y \<sqsubseteq> semi_factor_p ?Z\<cdot>x" by (rule monofun_cfun_arg)
    with yZ show "semi_factor_p F\<cdot>x \<sqsubseteq> semi_factor_p ?Z\<cdot>x" by simp
  qed
qed

lemma semi_factor_algebraic: "F = lub {K. compact K \<and> K \<sqsubseteq> F}" for F :: "'a::dI semi_factor"
proof (rule below_antisym)
  have "lub {semi_factor_principal k | k. compact k \<and> semi_factor_p F\<cdot>k = k} \<sqsubseteq> lub {K. compact K \<and> K \<sqsubseteq> F}"
    by (rule lattice_lub_mono)
      (auto intro: compact_semi_factor_principal simp: semi_factor_principal_below_iff)
  then show "F \<sqsubseteq> lub {K. compact K \<and> K \<sqsubseteq> F}"
    by (rule below_trans[OF eq_imp_below[OF semi_factor_lub_principals]])
  show "lub {K. compact K \<and> K \<sqsubseteq> F} \<sqsubseteq> F" by (rule lattice_lub_least) (auto simp: is_ub_def)
qed

text \<open>A compact semi-factor is the join of finitely many compact principals: enumerate the
  compacts of its image, and the joins of initial segments form a chain with lub the semi-factor.\<close>

lemma compact_semi_factor_finite_join:
  assumes K: "compact K"
  shows "\<exists>A. finite A \<and> A \<subseteq> {k. compact k} \<and> K = lub (semi_factor_principal ` A)"
proof -
  let ?P = "{k. compact k \<and> semi_factor_p K\<cdot>k = k}"
  have "semi_factor_p K\<cdot>\<bottom> = \<bottom>" by (rule bottomI, rule deflation.below[OF deflation_semi_factor_p])
  then have neP: "?P \<noteq> {}" by (intro exI[of _ \<bottom>] notI) simp
  have cP: "countable ?P" by (rule countable_subset[OF _ countable_compacts]) auto
  define e where "e = from_nat_into ?P"
  have e: "range e = ?P" unfolding e_def by (rule range_from_nat_into[OF neP cP])
  have eP: "compact (e i) \<and> semi_factor_p K\<cdot>(e i) = e i" for i using rangeI[of e i] e by blast
  define G where "G n = lub (semi_factor_principal ` e ` {..n})" for n
  have chG: "chain G" unfolding G_def by (rule chainI, rule lattice_lub_mono) auto
  have GK: "G n \<sqsubseteq> K" for n
    unfolding G_def by (rule lattice_lub_least) (auto simp: is_ub_def semi_factor_principal_below_iff eP)
  have "K \<sqsubseteq> (\<Squnion>n. G n)"
  proof -
    have "K = lub {semi_factor_principal k | k. compact k \<and> semi_factor_p K\<cdot>k = k}"
      by (rule semi_factor_lub_principals)
    also have "\<dots> \<sqsubseteq> (\<Squnion>n. G n)"
    proof (rule lattice_lub_least, rule is_ubI)
      fix X assume "X \<in> {semi_factor_principal k | k. compact k \<and> semi_factor_p K\<cdot>k = k}"
      then obtain k where X: "X = semi_factor_principal k" and k: "k \<in> ?P" by blast
      then have "k \<in> range e" using e by simp
      then obtain n where n: "k = e n" by blast
      have "X \<sqsubseteq> G n" unfolding X n G_def by (rule lattice_lub_upper) simp
      also have "G n \<sqsubseteq> (\<Squnion>n. G n)" by (rule is_ub_thelub[OF chG])
      finally show "X \<sqsubseteq> (\<Squnion>n. G n)" .
    qed
    finally show ?thesis .
  qed
  then obtain n where "K \<sqsubseteq> G n" using compactD2[OF K chG] by blast
  then have "K = G n" using GK[of n] by (rule below_antisym)
  then show ?thesis unfolding G_def by (intro exI[of _ "e ` {..n}"] conjI) (auto simp: eP)
qed

lemma countable_compact_semi_factors: "countable {K :: 'a::dI semi_factor. compact K}"
proof (rule countable_subset)
  show "{K. compact K} \<subseteq> (\<lambda>A. lub (semi_factor_principal ` A)) ` {A. finite A \<and> A \<subseteq> {k :: 'a. compact k}}"
    using compact_semi_factor_finite_join by blast
  show "countable ((\<lambda>A. lub (semi_factor_principal ` A)) ` {A. finite A \<and> A \<subseteq> {k :: 'a. compact k}})"
    by (rule countable_image, rule countable_Collect_finite_subset, rule countable_compacts)
qed

lemma semi_factor_compacts_enum: "\<exists>c :: nat \<Rightarrow> 'a::dI semi_factor. range c = {K. compact K}"
  using range_from_nat_into[OF _ countable_compact_semi_factors] compact_bottom by blast

instance semi_factor :: (dI) bifinite
  by (rule bifinite_algebraic_lattice[OF semi_factor_compacts_enum semi_factor_algebraic])

end
