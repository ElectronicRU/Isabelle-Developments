theory Semi_Factor_DI
  imports Subdomain "HOLCF-extra.DI"
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
  then obtain F where F: "F \<subseteq> \<D>" "finite F" and FD: "(\<lambda>d. d\<cdot>x) ` \<D> = (\<lambda>d. d\<cdot>x) ` F"
    using finite_subset_image[OF _ subset_refl] by blast
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

end
