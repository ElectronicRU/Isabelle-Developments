theory Separated_Principal
  imports LOD
begin

section \<open>Principal semi-factors from levels of finite height\<close>

text \<open>Separation and local finite detail do \<^emph>\<open>not\<close> suffice for principal semi-factors.  Let
  \<open>E\<close> consist of \<open>\<bottom>\<close>, an element \<open>y\<close> and a strictly descending chain
  \<open>z\<^sub>0 \<sqsupset> z\<^sub>1 \<sqsupset> z\<^sub>2 \<sqsupset> \<dots> \<sqsupset> \<bottom>\<close>, with \<open>y\<close> incomparable to (and not joinable with) every
  \<open>z\<^sub>n\<close>.  \<open>E\<close> is a bifinite (approximations: keep \<open>y\<close> and \<open>z\<^sub>0, \<dots>, z\<^sub>n\<close>, send the rest to
  \<open>\<bottom>\<close>) distributive tree without infinite ascending chains, so every element is compact and
  \<open>ID\<close> is a finitary semi-factor: \<open>E\<close> is locally finitely detailed, and so is the separated sum
  \<open>E\<^sub>\<bottom>\<close> (its nonbottom semi-factors are the lifted semi-factors of \<open>E\<close>).
  The sets \<open>S\<^sub>n = {\<bottom>, y} \<union> {z\<^sub>m | m \<ge> n}\<close> are semi-factors containing \<open>y\<close> (the only image
  element above the projection \<open>z\<^sub>n\<close> of \<open>z\<^sub>j\<close>, \<open>j < n\<close>, is \<open>z\<^sub>n\<close> itself).  Conversely a
  semi-factor containing \<open>y\<close> must project \<open>z\<^sub>0\<close> to some \<open>z\<^sub>n\<close> (projecting it to \<open>\<bottom>\<close> breaks
  the slide rule at \<open>y\<close>), so it contains \<open>S\<^sub>n\<close>.  A least one would contain some \<open>z\<^sub>n\<close> and lie
  in \<open>S\<^sub>n\<^sub>+\<^sub>1\<close>: there is no principal semi-factor of \<open>y\<close> (nor of \<open>up\<cdot>y\<close> in \<open>E\<^sub>\<bottom>\<close>).

  Separation is in fact irrelevant to the question: the nonbottom semi-factors of a separated
  sum are the products of semi-factors of its summands, and any domain becomes a separated sum by
  lifting.  The culprit is the infinite \<^emph>\<open>descending\<close> chain inside a finitary level: finitary
  (all images compact) only excludes infinite ascending chains.  Excluding descending ones too,
  i.e. asking for levels without infinite chains, gives principals, by the argument of the dI
  case: the meet of the semi-factors containing \<open>k\<close>, cut down below such a level, is computed
  pointwise, since at every argument the values of the projections have a least one.\<close>

subsection \<open>Well-founded semi-factors\<close>

text \<open>A semi-factor is \<^emph>\<open>well-founded\<close> when its image has no infinite strictly descending
  chains.\<close>

definition well_founded_semi_factor :: "'a::{bifinite, distributive_cpo} semi_factor \<Rightarrow> bool" where
  "well_founded_semi_factor F \<longleftrightarrow> wf {(a, b). a \<sqsubseteq> b \<and> a \<noteq> b \<and> b \<downharpoonright> F = b}"

text \<open>Projections onto smaller semi-factors land in the image of the larger one.\<close>

lemma semi_factor_proj_fixed_above:
  assumes "G \<sqsubseteq> F" shows "x \<downharpoonright> G \<downharpoonright> F = x \<downharpoonright> G"
  using assms by (rule semi_factor_comp_simp(1))

text \<open>The key step.  Let \<open>\<A>\<close> be a non-empty family of semi-factors below a well-founded \<open>F\<close>,
  closed under binary meets.  At any argument \<open>x\<close> the values \<open>x \<downharpoonright> G\<close>, \<open>G \<in> \<A>\<close>, lie in the
  image of \<open>F\<close>, so one of them, \<open>x \<downharpoonright> G\<^sub>0\<close>, is minimal; meet-closure makes it least.\<close>

lemma well_founded_least_value:
  assumes wf: "well_founded_semi_factor F" and ne: "\<A> \<noteq> {}"
    and below: "\<And>G. G \<in> \<A> \<Longrightarrow> G \<sqsubseteq> F"
    and meet: "\<And>G H. G \<in> \<A> \<Longrightarrow> H \<in> \<A> \<Longrightarrow> G \<sqinter> H \<in> \<A>"
  obtains G0 where "G0 \<in> \<A>" and "\<And>G. G \<in> \<A> \<Longrightarrow> x \<downharpoonright> G0 \<sqsubseteq> x \<downharpoonright> G"
proof -
  let ?R = "{(a, b). a \<sqsubseteq> b \<and> a \<noteq> b \<and> b \<downharpoonright> F = b}"
  let ?V = "(\<lambda>G. x \<downharpoonright> G) ` \<A>"
  from ne obtain G1 where "G1 \<in> \<A>" by blast
  then have "x \<downharpoonright> G1 \<in> ?V" by blast
  from wf[unfolded well_founded_semi_factor_def] this obtain m where
    mV: "m \<in> ?V" and min: "\<And>a. (a, m) \<in> ?R \<Longrightarrow> a \<notin> ?V"
    by (rule wfE_min) blast
  from mV obtain G0 where G0: "G0 \<in> \<A>" and m: "m = x \<downharpoonright> G0" by blast
  have mF: "m \<downharpoonright> F = m" unfolding m by (rule semi_factor_proj_fixed_above[OF below[OF G0]])
  have "x \<downharpoonright> G0 \<sqsubseteq> x \<downharpoonright> G" if G: "G \<in> \<A>" for G
  proof -
    let ?a = "x \<downharpoonright> (G0 \<sqinter> G)"
    have aV: "?a \<in> ?V" using meet[OF G0 G] by blast
    have "?a = x \<downharpoonright> G \<downharpoonright> G0" by (simp only: semi_factor_proj_comp lattice_meet_commute)
    also have "\<dots> \<sqsubseteq> x \<downharpoonright> G0"
      by (rule monofun_cfun_arg[OF deflation.below[OF deflation_semi_factor_p]])
    finally have am: "?a \<sqsubseteq> m" by (simp only: m)
    have "?a = m" using min[of ?a] aV am mF by blast
    moreover have "?a \<sqsubseteq> x \<downharpoonright> G"
      unfolding semi_factor_proj_comp[symmetric]
      by (rule monofun_cfun_arg[OF deflation.below[OF deflation_semi_factor_p]])
    ultimately show ?thesis by (simp only: m)
  qed
  with G0 show ?thesis by (rule that)
qed

text \<open>Hence the glb of the projections is a semi-factor deflation: it fixes the least value
  \<open>x \<downharpoonright> G\<^sub>0\<close>, which therefore is its value at \<open>x\<close>, and the slide rule is that of \<open>G\<^sub>0\<close>.\<close>

lemma semi_factor_defl_glb_well_founded:
  assumes wf: "well_founded_semi_factor F" and ne: "\<A> \<noteq> {}"
    and below: "\<And>G. G \<in> \<A> \<Longrightarrow> G \<sqsubseteq> F"
    and meet: "\<And>G H. G \<in> \<A> \<Longrightarrow> H \<in> \<A> \<Longrightarrow> G \<sqinter> H \<in> \<A>"
  shows "semi_factor_defl (glb (semi_factor_p ` \<A>))"
proof (rule semi_factor_deflI)
  let ?P = "semi_factor_p ` \<A>"
  have neP: "?P \<noteq> {}" using ne by blast
  have st: "\<And>d. d \<in> ?P \<Longrightarrow> stable_defl d" by (auto intro: stable_defl_semi_factor_p)
  note fx = stable_defl_glb_fixes[OF neP st]
  show "stable_defl (glb ?P)" by (rule stable_defl_glb[OF neP st])
  fix x y assume y: "glb ?P\<cdot>y = y" and xy: "glb ?P\<cdot>x \<sqsubseteq> y"
  obtain G0 where G0: "G0 \<in> \<A>" and least: "\<And>G. G \<in> \<A> \<Longrightarrow> x \<downharpoonright> G0 \<sqsubseteq> x \<downharpoonright> G"
    by (rule well_founded_least_value[OF wf ne below meet, where x = x]) blast+
  have "d\<cdot>(x \<downharpoonright> G0) = x \<downharpoonright> G0" if "d \<in> ?P" for d
    using that least by (auto intro: stable_defl.lower_fixed[OF stable_defl_semi_factor_p])
  then have "glb ?P\<cdot>(x \<downharpoonright> G0) = x \<downharpoonright> G0" using fx by blast
  moreover have "glb ?P\<cdot>(x \<downharpoonright> G0) \<sqsubseteq> glb ?P\<cdot>x"
    by (rule monofun_cfun_arg[OF deflation.below[OF deflation_semi_factor_p]])
  ultimately have "x \<downharpoonright> G0 \<sqsubseteq> y" using xy by (metis below_trans)
  moreover have "y \<downharpoonright> G0 = y" using y fx G0 by blast
  ultimately show "x \<Up> y" by (intro proj_slide)
qed

text \<open>A key living at a well-founded level has a principal semi-factor: the glb of the
  projections onto the semi-factors containing it and lying below the level.\<close>

theorem principal_semi_factor_well_founded_level:
  assumes wf: "well_founded_semi_factor F" and k: "k \<downharpoonright> F = k"
  shows "\<exists>P. is_principal_semi_factor P k"
proof -
  let ?A = "{G. G \<sqsubseteq> F \<and> k \<downharpoonright> G = k}"
  let ?P = "semi_factor_p ` ?A"
  have ne: "?A \<noteq> {}" using k by blast
  have meet: "G \<sqinter> H \<in> ?A" if "G \<in> ?A" "H \<in> ?A" for G H
    using that by (auto simp: semi_factor_proj_comp[symmetric] intro: below_trans[OF lattice_meet_le1])
  have sfd: "semi_factor_defl (glb ?P)"
    by (rule semi_factor_defl_glb_well_founded[OF wf ne _ meet]) auto
  have neP: "?P \<noteq> {}" using ne by blast
  have st: "\<And>d. d \<in> ?P \<Longrightarrow> stable_defl d" by (auto intro: stable_defl_semi_factor_p)
  let ?Q = "semi_factor_of_defl (glb ?P)"
  have pQ: "semi_factor_p ?Q = glb ?P" by (rule semi_factor_p_of_defl[OF sfd])
  have kQ: "k \<downharpoonright> ?Q = k" unfolding pQ using stable_defl_glb_fixes[OF neP st] by auto
  have "?Q \<sqsubseteq> G \<longleftrightarrow> k \<downharpoonright> G = k" for G
  proof
    assume "?Q \<sqsubseteq> G"
    then have "k \<downharpoonright> ?Q \<sqsubseteq> k \<downharpoonright> G" by (rule semi_factor_p_mono)
    then have "k \<sqsubseteq> k \<downharpoonright> G" by (simp only: kQ)
    then show "k \<downharpoonright> G = k" by (rule below_antisym[OF deflation.below[OF deflation_semi_factor_p]])
  next
    assume kG: "k \<downharpoonright> G = k"
    have "G \<sqinter> F \<in> ?A"
      using kG k by (auto simp: semi_factor_proj_comp[symmetric] intro: lattice_meet_le2)
    then have "glb ?P \<sqsubseteq> semi_factor_p (G \<sqinter> F)" by (intro glb_below) blast
    then have "?Q \<sqsubseteq> G \<sqinter> F" by (simp only: semi_factor_below_iff_p[of ?Q, unfolded pQ])
    then show "?Q \<sqsubseteq> G" by (rule below_trans[OF _ lattice_meet_le1])
  qed
  then show ?thesis unfolding is_principal_semi_factor_def by blast
qed

subsection \<open>Locally finite height\<close>

text \<open>A domain has \<^emph>\<open>locally finite height\<close> when every compact lives at a level without infinite
  chains: finitary (no infinite ascending ones) and well-founded (no infinite descending ones).
  Such a domain is locally finitely detailed and has principals, so it is a @{class lod_domain}.\<close>

class locally_finite_height = bifinite + distributive_cpo +
  assumes compact_finite_height_level:
    "compact k \<Longrightarrow> \<exists>F. finitary_semi_factor F \<and> well_founded_semi_factor F \<and> k \<downharpoonright> F = k"

instance locally_finite_height \<subseteq> locally_finitely_detailed
  by standard (use compact_finite_height_level in blast)

instance locally_finite_height \<subseteq> principal_semifactor
proof
  fix x :: 'a assume "compact x"
  then obtain F where "well_founded_semi_factor F" "x \<downharpoonright> F = x"
    using compact_finite_height_level by blast
  then show "\<exists>P. is_principal_semi_factor P x" by (rule principal_semi_factor_well_founded_level)
qed

instance locally_finite_height \<subseteq> lod_domain ..

end
