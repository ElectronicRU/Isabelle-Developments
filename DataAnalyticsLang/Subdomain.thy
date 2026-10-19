theory Subdomain 
  imports HOLCF "HOLCF-extra.Directed" "HOLCF-extra.Lattice_Complete"
  abbrevs ",," = "\<downharpoonright>"
begin

default_sort "{bifinite, bounded_complete}"

text \<open>\<^cite>\<open>buneman91\<close>\<close>


section \<open>Stable deflations\<close>

text \<open>A deflation is \<^emph>\<open>stable\<close> when its image is downward closed.  The pointwise facts about
  stable subdomains are stated here for deflations; the subdomains below only add the
  construction of the projection.\<close>

locale stable_defl = deflation d for d :: "'a::{bifinite, bounded_complete} \<rightarrow> 'a" +
  assumes downclosed: "d\<cdot>y = y \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> d\<cdot>x = x"
begin

lemma deflation: "deflation d" by (fact deflation_axioms)

text \<open>Every image element below @{term x} is below @{term \<open>d\<cdot>x\<close>}; every lower bound of an image
  element lies in the image.\<close>

lemma below_image: "d\<cdot>a = a \<Longrightarrow> a \<sqsubseteq> x \<Longrightarrow> a \<sqsubseteq> d\<cdot>x"
  by (metis monofun_cfun_arg)

lemma lower_fixed: "l \<sqsubseteq> d\<cdot>x \<Longrightarrow> d\<cdot>l = l"
  by (rule downclosed[OF idem])

text \<open>Hence the deflation commutes with existing binary meets.\<close>

lemma glb_fixed:
  assumes m: "is_glb {x, y} m"
  shows "is_glb {d\<cdot>x, d\<cdot>y} (d\<cdot>m)"
proof (rule is_glbI)
  fix z assume "z \<in> {d\<cdot>x, d\<cdot>y}"
  moreover have "m \<sqsubseteq> x" "m \<sqsubseteq> y" using m by (auto intro: is_glb_below)
  ultimately show "d\<cdot>m \<sqsubseteq> z" by (auto intro: monofun_cfun_arg)
next
  fix l assume "\<forall>z\<in>{d\<cdot>x, d\<cdot>y}. l \<sqsubseteq> z"
  then have lx: "l \<sqsubseteq> d\<cdot>x" and ly: "l \<sqsubseteq> d\<cdot>y" by simp_all
  have fix_l: "d\<cdot>l = l" using lx by (rule lower_fixed)
  have "l \<sqsubseteq> x" using lx below by (rule below_trans)
  moreover have "l \<sqsubseteq> y" using ly below by (rule below_trans)
  ultimately have "l \<sqsubseteq> m" using m by (auto intro: is_glb_greatest)
  then have "d\<cdot>l \<sqsubseteq> d\<cdot>m" by (rule monofun_cfun_arg)
  with fix_l show "l \<sqsubseteq> d\<cdot>m" by simp
qed

text \<open>Below an image element, meeting with @{term z} or with its image is the same.\<close>

lemma glb_relative:
  assumes m: "is_glb {d\<cdot>c, d\<cdot>z} m"
  shows "is_glb {d\<cdot>c, z} m"
proof (rule is_glbI)
  fix w assume "w \<in> {d\<cdot>c, z}"
  moreover have "m \<sqsubseteq> d\<cdot>c" "m \<sqsubseteq> d\<cdot>z" using m by (auto intro: is_glb_below)
  ultimately show "m \<sqsubseteq> w" using below[of z] by (auto intro: below_trans)
next
  fix l assume "\<forall>w\<in>{d\<cdot>c, z}. l \<sqsubseteq> w"
  then have lc: "l \<sqsubseteq> d\<cdot>c" and lz: "l \<sqsubseteq> z" by simp_all
  have "d\<cdot>l = l" using lc by (rule lower_fixed)
  moreover from lz have "d\<cdot>l \<sqsubseteq> d\<cdot>z" by (rule monofun_cfun_arg)
  ultimately have "l \<sqsubseteq> d\<cdot>z" by simp
  with lc show "l \<sqsubseteq> m" using m by (auto intro: is_glb_greatest)
qed

end

lemma stable_deflI:
  "deflation d \<Longrightarrow> (\<And>x y. d\<cdot>y = y \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> d\<cdot>x = x) \<Longrightarrow> stable_defl d"
  by (simp add: stable_defl_def stable_defl_axioms_def)

text \<open>Jung, Lemma 4.1.6(i): the image of \<open>x\<close> below some image element \<open>y\<close> is the meet \<open>x \<sqinter> y\<close>.
  Binary meets need bounded completeness.\<close>

lemma stable_defl_image_meet:
  assumes d: "stable_defl d" and y: "d\<cdot>y = y" and le: "d\<cdot>x \<sqsubseteq> y"
  shows "d\<cdot>x = x \<sqinter> y"
proof (rule below_antisym)
  interpret stable_defl d by (rule d)
  show "d\<cdot>x \<sqsubseteq> x \<sqinter> y" using below le by (rule meet_greatest)
  have "d\<cdot>(x \<sqinter> y) = x \<sqinter> y" using y meet_below2 by (rule downclosed)
  then show "x \<sqinter> y \<sqsubseteq> d\<cdot>x" using meet_below1 by (rule below_image)
qed


section \<open>Stable subdomains\<close>

locale stable_subdomain =
  fixes S :: "'a set" (structure)
  assumes lub_closed:  "T \<subseteq> S \<Longrightarrow> T <<| t \<Longrightarrow> t \<in> S"
  assumes downward: "y \<in> S \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> x \<in> S"
begin
definition "proj a = lub {x \<in> S. x \<sqsubseteq> a}"

lemma proj_set_directed: "directed {x \<in> S. x \<sqsubseteq> a}"
proof (rule directedI, safe)
  fix x y assume S: "x \<in> S" "y \<in> S"
  assume a: "x \<sqsubseteq> a" "y \<sqsubseteq> a"
  then have lub: "{x, y} <<| (x \<squnion> y)" by (rule join_is_lub)
  from lub_closed[OF _ this] S have lubS: "x \<squnion> y \<in> S"
    by blast
  from lub have le: "x \<sqsubseteq> x \<squnion> y" "y \<sqsubseteq> x \<squnion> y" by (auto dest: is_lubD1 is_ubD)
  moreover from a have "x \<squnion> y \<sqsubseteq> a"
    using is_lubD2[OF lub, of a] by auto
  ultimately show "\<exists>z \<in> {x \<in> S. x \<sqsubseteq> a}. x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
    using lubS by blast
qed

lemma bot_in_S: "\<bottom> \<in> S"
  using lub_closed[of "{}" "\<bottom>"] by simp

lemma proj_set_ne: "{x \<in> S. x \<sqsubseteq> a} \<noteq> {}"
proof -
  have "\<bottom> \<in> {x \<in> S. x \<sqsubseteq> a}" using bot_in_S by simp
  then show ?thesis by auto
qed

corollary proj_is_lub: "{x \<in> S. x \<sqsubseteq> a} <<| proj a"
  unfolding proj_def using proj_set_directed by (rule directed_lub)

corollary proj_in_S: "proj a \<in> S"
  using lub_closed[OF _ proj_is_lub] by blast

lemma proj_below: "proj a \<sqsubseteq> a"
  by (blast intro: proj_is_lub[THEN is_lubD2, of a a] is_ubI)

corollary proj_fixed: "a \<in> S \<Longrightarrow> proj a = a"
proof (rule below_antisym)
  show "proj a \<sqsubseteq> a" by (fact proj_below)
  assume "a \<in> S"
  then have "a \<in> {x \<in> S. x \<sqsubseteq> a}" by simp
  with proj_is_lub[THEN is_lubD1, THEN is_ubD] show "a \<sqsubseteq> proj a" .
qed

corollary proj_fixed_iff: "proj a = a \<longleftrightarrow> a \<in> S"
  using proj_in_S proj_fixed by metis

corollary below_set_is_down_set:
  "{x \<in> S. x \<sqsubseteq> a} = {x. x \<sqsubseteq> proj a}"
proof (intro subset_antisym subsetI; safe)
  fix x assume "x \<in> S" "x \<sqsubseteq> a"
  with proj_is_lub[THEN is_lubD1, THEN is_ubD]
  show "x \<sqsubseteq> proj a" by blast
next
  fix x assume *: "x \<sqsubseteq> proj a"
  from below_trans[OF * proj_below]
  show "x \<sqsubseteq> a" .
  from downward[OF proj_in_S *]
  show "x \<in> S" .
qed

lemma approximants_proj:
  "approximants (proj a) = {x \<in> approximants a. Rep_compact_basis x \<in> S}"
  unfolding approximants_def
  using below_set_is_down_set by blast

lemma proj_mono: "monofun proj"
proof (rule monofunI)
  fix x y :: 'a assume "x \<sqsubseteq> y"
  then have "{z \<in> S. z \<sqsubseteq> x} \<subseteq> {z \<in> S. z \<sqsubseteq> y}"
    using below_trans by blast
  with proj_is_lub proj_is_lub show "proj x \<sqsubseteq> proj y"
    by (rule lub_subset_mono)
qed

corollary below_proj_of: "a \<in> S \<Longrightarrow> a \<sqsubseteq> x \<Longrightarrow> a \<sqsubseteq> proj x"
  using proj_is_lub[THEN is_lubD1, THEN is_ubD] by blast

lemma proj_monoD: "x \<sqsubseteq> y \<Longrightarrow> proj x \<sqsubseteq> proj y"
  by (rule monofunE[OF proj_mono])


lemma proj_cont: "cont proj"
proof (rule contI2)
  show "monofun proj" by (fact proj_mono)
  fix Y :: "nat \<Rightarrow> 'a" assume Y: "chain Y"
  assume pY: "chain (\<lambda>i. proj (Y i))"
  from Y have 1: "approximants (\<Squnion>i. Y i) = (\<Union>i. approximants (Y i))"
    by (rule compact_basis.rep_lub)
  from pY have 2: "approximants (\<Squnion>i. proj(Y i)) = (\<Union>i. approximants (proj (Y i)))"
    by (rule compact_basis.rep_lub)
  from 1 2 approximants_proj
  have "approximants (proj (\<Squnion>i. Y i)) \<subseteq> approximants (\<Squnion>i. proj(Y i))"
    by auto
  then show "proj (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. proj(Y i))"
    by (rule compact_basis.belowI)
qed

definition p where "p \<equiv> \<Lambda> a. proj a"

lemma p_beta: "p\<cdot>x = proj x"
  unfolding p_def
  by (simp add: proj_cont)

lemma deflation_p: "deflation p"
proof
  show "p\<cdot>(p\<cdot>x) = p\<cdot>x" for x
    using proj_in_S proj_fixed
    by (simp add: p_beta)
  show "p\<cdot>x \<sqsubseteq> x" for x
    using proj_below by (simp add: p_beta)
qed

text \<open>\<open>p\<close>-form duplicates of the projection lemmas.  Since \<open>p_beta\<close> (\<open>p\<cdot>x = proj x\<close>) is
  deliberately not a simp rule — it rewrites \<open>p\<cdot>x\<close> against \<open>deflation.below\<close> etc. — we
  restate the projection facts directly for \<open>p\<cdot>x\<close> via \<open>proj = Rep_cfun p\<close> and use those.\<close>
lemma proj_Rep_p: "proj = Rep_cfun p"
  by (rule ext) (simp add: p_beta)

lemmas p_in_S[simp] = proj_in_S[unfolded proj_Rep_p]
lemmas p_below = proj_below[unfolded proj_Rep_p]
lemmas p_fixed = proj_fixed[unfolded proj_Rep_p]
lemmas p_fixed_iff = proj_fixed_iff[unfolded proj_Rep_p]

text \<open>The projection is a stable deflation; the deflation lemmas are inherited, and restated
  with membership in @{term S} for the fixed points.\<close>

sublocale stable_defl p
  by (rule stable_deflI[OF deflation_p]) (use downward p_fixed_iff in simp)

lemmas below_p_of = below_image[unfolded p_fixed_iff]
lemmas p_meet = stable_defl_image_meet[OF stable_defl_axioms, unfolded p_fixed_iff]

lemma p_fixes: "{x. p\<cdot>x = x} = S"
  by (simp add: proj_fixed_iff p_beta)

lemma p_range: "range (\<lambda>x. p\<cdot>x) = S"
  by (simp only: p_fixes range_eq_fixes)

end


locale semi_factor_subdomain = stable_subdomain +
  assumes slide_rule: "y \<in> S \<Longrightarrow> p\<cdot>x \<sqsubseteq> y \<Longrightarrow> x \<Up> y"

lemma stable_subdomain_deflation:
  fixes p assumes p: "deflation p" and ss: "stable_subdomain {x. p\<cdot>x = x}"
  shows "p = stable_subdomain.p {x. p\<cdot>x = x}"
proof -
  interpret p: deflation p by (rule p)
  interpret S: stable_subdomain "{x. p\<cdot>x = x}" by (rule ss)
  show ?thesis
  proof (intro below_antisym)
    show "p \<sqsubseteq> S.p"
    proof (rule p.belowI)
      fix x assume "p\<cdot>x = x"
      then show "S.p\<cdot>x = x"
        by (metis (mono_tags, lifting) S.p_fixes mem_Collect_eq)
    qed
    show "S.p \<sqsubseteq> p"
    proof (rule S.belowI)
      fix x assume "S.p\<cdot>x = x"
      then show "p\<cdot>x = x"
        by (metis (mono_tags, lifting) S.p_fixes mem_Collect_eq)
    qed
  qed
qed
text \<open>The range of any deflation is automatically closed under lubs of bounded
  subsets: only downward closure distinguishes a stable-subdomain projection from a
  general deflation.\<close>

lemma deflation_lub_closed:
  assumes d: "deflation d" and T: "T \<subseteq> {x. d\<cdot>x = x}" and lub: "T <<| t"
  shows "d\<cdot>t = t"
proof -
  interpret deflation d by (rule d)
  have "T <| d\<cdot>t"
  proof (rule is_ubI)
    fix x assume x: "x \<in> T"
    with T have "d\<cdot>x = x" by auto
    moreover from is_lubD1[OF lub] x have "x \<sqsubseteq> t" by (rule is_ubD)
    ultimately show "x \<sqsubseteq> d\<cdot>t" by (metis monofun_cfun_arg)
  qed
  from is_lubD2[OF lub this] have "t \<sqsubseteq> d\<cdot>t" .
  with below show "d\<cdot>t = t" by (rule below_antisym)
qed

lemma deflation_stable_subdomainI:
  assumes d: "deflation d"
    and dc: "\<And>x y. d\<cdot>y = y \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> d\<cdot>x = x"
  shows "stable_subdomain {x. d\<cdot>x = x}"
proof
  fix y x assume "y \<in> {x. d\<cdot>x = x}" "x \<sqsubseteq> y"
  with dc show "x \<in> {x. d\<cdot>x = x}" by simp
next
  fix T t assume "T \<subseteq> {x. d\<cdot>x = x}" "T <<| t"
  with deflation_lub_closed[OF d] show "t \<in> {x. d\<cdot>x = x}" by simp
qed

subsection \<open>Stable deflations and stable subdomains\<close>

text \<open>The image of a stable deflation is a stable subdomain
  (@{thm [source] deflation_stable_subdomainI}).  Unlike the order predicates on deflations,
  stability is not antitone, but it is admissible on algebraic types.  It is closed under the
  domain constructions, so e.g.\ the \<open>take\<close> functions of a domain are stable.\<close>

lemma stable_defl_stable_subdomain:
  assumes "stable_defl d"
  shows "stable_subdomain {x. d\<cdot>x = x}"
  by (rule deflation_stable_subdomainI[OF stable_defl.deflation[OF assms]
        stable_defl.downclosed[OF assms]])

lemma stable_defl_bottom: "stable_defl (\<bottom> :: 'a \<rightarrow> 'a)"
  by (rule stable_deflI[OF deflation_bottom]) simp

lemma stable_defl_ID: "stable_defl (ID :: 'a \<rightarrow> 'a)"
  by (rule stable_deflI[OF deflation_ID]) simp

lemma adm_stable_defl: "adm (stable_defl :: ('a \<rightarrow> 'a) \<Rightarrow> bool)"
proof (rule admI)
  fix D :: "nat \<Rightarrow> 'a \<rightarrow> 'a"
  assume chain: "chain D" and H: "\<forall>i. stable_defl (D i)"
  have Hd: "deflation (D i)" for i by (rule stable_defl.axioms(1)[OF H[rule_format]])
  have defl: "deflation (\<Squnion>i. D i)" by (rule admD[OF adm_deflation chain Hd])
  show "stable_defl (\<Squnion>i. D i)"
  proof (rule stable_deflI[OF defl])
    fix x y assume fy: "(\<Squnion>i. D i)\<cdot>y = y" and xy: "x \<sqsubseteq> y"
    obtain C where C: "chain C" "\<forall>i. compact (C i)" "x = (\<Squnion>i. C i)"
      by (rule obtain_compact_chain)
    have fixed: "(\<Squnion>i. D i)\<cdot>(C i) = C i" for i
    proof -
      have "C i \<sqsubseteq> x" using is_ub_thelub[OF C(1)] C(3) by simp
      then have "C i \<sqsubseteq> y" using xy by (rule below_trans)
      then have "C i \<sqsubseteq> (\<Squnion>i. D i)\<cdot>y" using fy by simp
      also have "\<dots> = (\<Squnion>j. D j\<cdot>y)" by (rule contlub_cfun_fun[OF chain])
      finally have Cilub: "C i \<sqsubseteq> (\<Squnion>j. D j\<cdot>y)" .
      have chy: "chain (\<lambda>j. D j\<cdot>y)" by (rule ch2ch_Rep_cfunL[OF chain])
      from compactD2[OF C(2)[rule_format] chy Cilub] obtain j where j: "C i \<sqsubseteq> D j\<cdot>y" by blast
      have idem: "D j\<cdot>(D j\<cdot>y) = D j\<cdot>y" by (rule deflation.idem[OF Hd])
      have CiFix: "D j\<cdot>(C i) = C i"
        by (rule stable_defl.downclosed[OF H[rule_format] idem j])
      have "D j \<sqsubseteq> (\<Squnion>i. D i)" by (rule is_ub_thelub[OF chain])
      then have "D j\<cdot>(C i) \<sqsubseteq> (\<Squnion>i. D i)\<cdot>(C i)" by (rule monofun_cfun_fun)
      with CiFix have "C i \<sqsubseteq> (\<Squnion>i. D i)\<cdot>(C i)" by simp
      then show ?thesis by (rule below_antisym[OF deflation.below[OF defl]])
    qed
    have rcx: "range C <<| x" using cpo_lubI[OF C(1)] C(3) by simp
    have "range C \<subseteq> {z. (\<Squnion>i. D i)\<cdot>z = z}" using fixed by auto
    from deflation_lub_closed[OF defl this rcx] show "(\<Squnion>i. D i)\<cdot>x = x" .
  qed
qed

lemma stable_defl_u_map:
  assumes f: "stable_defl (f :: 'a \<rightarrow> 'a)"
  shows "stable_defl (u_map\<cdot>f)"
proof (rule stable_deflI)
  have fd: "deflation f" by (rule stable_defl.axioms(1)[OF f])
  then show "deflation (u_map\<cdot>f)" by (rule deflation_u_map)
  fix x y assume fy: "u_map\<cdot>f\<cdot>y = y" and xy: "x \<sqsubseteq> y"
  show "u_map\<cdot>f\<cdot>x = x"
  proof (cases x)
    case bottom then show ?thesis by simp
  next
    case (up x')
    with xy obtain y' where y: "y = up\<cdot>y'" "x' \<sqsubseteq> y'" by (cases y) auto
    with fy have "f\<cdot>y' = y'" by simp
    from stable_defl.downclosed[OF f this \<open>x' \<sqsubseteq> y'\<close>] up show ?thesis by simp
  qed
qed

lemma stable_defl_ssum_map:
  assumes f: "stable_defl f" and g: "stable_defl g"
  shows "stable_defl (ssum_map\<cdot>f\<cdot>g)"
proof (rule stable_deflI)
  show "deflation (ssum_map\<cdot>f\<cdot>g)"
    by (rule deflation_ssum_map[OF stable_defl.axioms(1)[OF f] stable_defl.axioms(1)[OF g]])
  fix x y assume fy: "ssum_map\<cdot>f\<cdot>g\<cdot>y = y" and xy: "x \<sqsubseteq> y"
  show "ssum_map\<cdot>f\<cdot>g\<cdot>x = x"
  proof (cases x)
    case bottom then show ?thesis by simp
  next
    case (sinl x')
    with xy obtain y' where y: "y = sinl\<cdot>y'" "y' \<noteq> \<bottom>" "x' \<sqsubseteq> y'" by (cases y) auto
    with fy have "f\<cdot>y' = y'" by simp
    from stable_defl.downclosed[OF f this \<open>x' \<sqsubseteq> y'\<close>] sinl show ?thesis by simp
  next
    case (sinr x')
    with xy obtain y' where y: "y = sinr\<cdot>y'" "y' \<noteq> \<bottom>" "x' \<sqsubseteq> y'" by (cases y) auto
    with fy have "g\<cdot>y' = y'" by simp
    from stable_defl.downclosed[OF g this \<open>x' \<sqsubseteq> y'\<close>] sinr show ?thesis by simp
  qed
qed

lemma stable_defl_sprod_map:
  assumes f: "stable_defl f" and g: "stable_defl g"
  shows "stable_defl (sprod_map\<cdot>f\<cdot>g)"
proof (rule stable_deflI)
  show "deflation (sprod_map\<cdot>f\<cdot>g)"
    by (rule deflation_sprod_map[OF stable_defl.axioms(1)[OF f] stable_defl.axioms(1)[OF g]])
  fix x y assume fy: "sprod_map\<cdot>f\<cdot>g\<cdot>y = y" and xy: "x \<sqsubseteq> y"
  show "sprod_map\<cdot>f\<cdot>g\<cdot>x = x"
  proof (cases x)
    case bottom then show ?thesis by simp
  next
    case (spair a b)
    with xy obtain c e where y: "y = (:c, e:)" "c \<noteq> \<bottom>" "e \<noteq> \<bottom>" "a \<sqsubseteq> c" "b \<sqsubseteq> e"
      by (cases y) (auto simp: spair_below_iff)
    with fy have "f\<cdot>c = c" "g\<cdot>e = e" by (auto simp: spair_eq_iff)
    with stable_defl.downclosed[OF f] stable_defl.downclosed[OF g] y spair
    have "f\<cdot>a = a" "g\<cdot>b = b" by blast+
    with spair show ?thesis by simp
  qed
qed

lemma stable_defl_iso:
  fixes abs :: "'r \<rightarrow> 't" and rep
  assumes iso_abs: "\<And>x. rep\<cdot>(abs\<cdot>x) = x" and iso_rep: "\<And>y. abs\<cdot>(rep\<cdot>y) = y"
    and f: "stable_defl f"
  shows "stable_defl (abs oo f oo rep)"
proof (rule stable_deflI)
  interpret iso abs rep by (rule iso.intro[OF iso_abs iso_rep])
  show "deflation (abs oo f oo rep)"
    by (rule deflation_abs_rep[OF abs_iso rep_iso stable_defl.axioms(1)[OF f]])
  fix x y assume fy: "(abs oo f oo rep)\<cdot>y = y" and xy: "x \<sqsubseteq> y"
  from fy have "rep\<cdot>(abs\<cdot>(f\<cdot>(rep\<cdot>y))) = rep\<cdot>y" by simp
  then have "f\<cdot>(rep\<cdot>y) = rep\<cdot>y" by simp
  moreover from xy have "rep\<cdot>x \<sqsubseteq> rep\<cdot>y" by (rule monofun_cfun_arg)
  ultimately have "f\<cdot>(rep\<cdot>x) = rep\<cdot>x" by (rule stable_defl.downclosed[OF f])
  then show "(abs oo f oo rep)\<cdot>x = x" by simp
qed


subsection \<open>Semi-factor deflations\<close>

text \<open>The deflation form of a semi-factor: a stable deflation satisfying the slide rule.  Closure
  of the image under existing lubs need not be assumed: the image of any deflation has it
  (@{thm [source] deflation_lub_closed}).  The deflation is then the projection onto its image,
  and conversely the projection of a semi-factor is one.\<close>

locale semi_factor_defl = stable_defl d for d :: "'a::{bifinite, distributive_cpo} \<rightarrow> 'a" +
  assumes slide: "d\<cdot>y = y \<Longrightarrow> d\<cdot>x \<sqsubseteq> y \<Longrightarrow> x \<Up> y"

lemma semi_factor_deflI:
  assumes "stable_defl d" and "\<And>x y. d\<cdot>y = y \<Longrightarrow> d\<cdot>x \<sqsubseteq> y \<Longrightarrow> x \<Up> y"
  shows "semi_factor_defl d"
  using assms by (simp add: semi_factor_defl_def semi_factor_defl_axioms_def)

lemma semi_factor_defl_iff:
  "semi_factor_defl d \<longleftrightarrow> deflation d \<and> semi_factor_subdomain {x. d\<cdot>x = x}"
proof
  assume sd: "semi_factor_defl d"
  then have st: "stable_defl d" by (rule semi_factor_defl.axioms(1))
  have d: "deflation d" by (rule stable_defl.deflation[OF st])
  have ss: "stable_subdomain {x. d\<cdot>x = x}" by (rule stable_defl_stable_subdomain[OF st])
  have p: "stable_subdomain.p {x. d\<cdot>x = x} = d"
    by (rule stable_subdomain_deflation[OF d ss, symmetric])
  have "semi_factor_subdomain {x. d\<cdot>x = x}"
    by (rule semi_factor_subdomain.intro[OF ss], unfold_locales, unfold p)
      (auto intro: semi_factor_defl.slide[OF sd])
  with d show "deflation d \<and> semi_factor_subdomain {x. d\<cdot>x = x}" by blast
next
  assume "deflation d \<and> semi_factor_subdomain {x. d\<cdot>x = x}"
  then have d: "deflation d" and S: "semi_factor_subdomain {x. d\<cdot>x = x}" by blast+
  have ss: "stable_subdomain {x. d\<cdot>x = x}" by (rule semi_factor_subdomain.axioms(1)[OF S])
  have p: "stable_subdomain.p {x. d\<cdot>x = x} = d"
    by (rule stable_subdomain_deflation[OF d ss, symmetric])
  show "semi_factor_defl d"
  proof (rule semi_factor_deflI)
    show "stable_defl d"
      by (rule stable_deflI[OF d]) (use stable_subdomain.downward[OF ss] in blast)
    fix x y assume "d\<cdot>y = y" "d\<cdot>x \<sqsubseteq> y"
    then show "x \<Up> y" using semi_factor_subdomain.slide_rule[OF S] p by auto
  qed
qed


lemma semi_factor_defl_bottom: "semi_factor_defl (\<bottom> :: 'a::{bifinite, distributive_cpo} \<rightarrow> 'a)"
proof (rule semi_factor_deflI[OF stable_defl_bottom])
  fix x y :: 'a assume "\<bottom>\<cdot>y = y"
  then have "y = \<bottom>" by simp
  then show "x \<Up> y" by (simp add: joinable_sym bottom_joinable)
qed

text \<open>A semi-factor is the image of its projection.\<close>

lemma semi_factor_defl_p:
  assumes "semi_factor_subdomain S"
  shows "semi_factor_defl (stable_subdomain.p S)"
proof -
  note ss = semi_factor_subdomain.axioms(1)[OF assms]
  have "{x. stable_subdomain.p S\<cdot>x = x} = S" by (rule stable_subdomain.p_fixes[OF ss])
  with assms stable_subdomain.deflation_p[OF ss] show ?thesis
    by (simp add: semi_factor_defl_iff)
qed

text \<open>A pcpo carved from a bounded-complete type by a typedef whose set is closed
  under lubs of bounded subsets is again bounded complete. The order on the subtype
  must be the one induced by @{term Rep}, as supplied by @{command pcpodef}.\<close>

lemma bounded_complete_subtypeI:
  fixes Rep :: "'b::pcpo \<Rightarrow> 'a::bounded_complete"
  assumes type: "type_definition Rep Abs Q"
    and below: "\<And>x y. (x \<sqsubseteq> y) = (Rep x \<sqsubseteq> Rep y)"
    and Q_lub_closed: "\<And>A a. A \<subseteq> Q \<Longrightarrow> A <<| a \<Longrightarrow> a \<in> Q"
  shows "OFCLASS('b, bounded_complete_class)"
proof
  interpret type_definition Rep Abs Q by (rule type)
  fix A :: "'b set" and b :: 'b
  assume "A \<noteq> {}" and Ab: "A <| b"
  have RepAb: "Rep ` A <| Rep b"
  proof (rule is_ubI)
    fix y assume "y \<in> Rep ` A"
    then obtain x where x: "x \<in> A" "y = Rep x" by auto
    from is_ubD[OF Ab x(1)] have "Rep x \<sqsubseteq> Rep b" using below by simp
    with x(2) show "y \<sqsubseteq> Rep b" by simp
  qed
  then obtain l where l: "Rep ` A <<| l" using ex_bound_ex_lub by blast
  have "Rep ` A \<subseteq> Q" using Rep by auto
  from Q_lub_closed[OF this l] have lQ: "l \<in> Q" .
  have "A <<| Abs l"
  proof (rule is_lubI)
    show "A <| Abs l"
    proof (rule is_ubI)
      fix x assume "x \<in> A"
      from is_ubD[OF is_lubD1[OF l]] this have "Rep x \<sqsubseteq> l" by auto
      then show "x \<sqsubseteq> Abs l" using below Abs_inverse[OF lQ] by simp
    qed
  next
    fix u assume "A <| u"
    have "Rep ` A <| Rep u"
    proof (rule is_ubI)
      fix y assume "y \<in> Rep ` A"
      then obtain x where x: "x \<in> A" "y = Rep x" by auto
      from is_ubD[OF \<open>A <| u\<close> x(1)] have "Rep x \<sqsubseteq> Rep u" using below by simp
      with x(2) show "y \<sqsubseteq> Rep u" by simp
    qed
    with l have "l \<sqsubseteq> Rep u" by (rule is_lubD2)
    then show "Abs l \<sqsubseteq> u" using below Abs_inverse[OF lQ] by simp
  qed
  then show "\<exists>z. A <<| z" ..
qed


text \<open>Continuity of binary meet (@{thm [source] cont_meet_arg}) is in \<open>Distributive\<close>.\<close>


section \<open>Stable subdomains as a lattice of sets\<close>

text \<open>Stable subdomains form a closure system: they contain @{term UNIV} and are
  closed under arbitrary intersection. Hence they form a complete lattice under
  inclusion, with meet given by intersection.\<close>

lemma stable_subdomain_UNIV: "stable_subdomain UNIV"
  by unfold_locales auto

lemma p_UNIV: "stable_subdomain.p UNIV\<cdot>x = x"
  by (simp add: stable_subdomain.p_fixed[OF stable_subdomain_UNIV])

lemma stable_subdomain_bot: "stable_subdomain {\<bottom>::'a}"
proof
  fix t :: 'a and T :: "'a set" assume "T \<subseteq> {\<bottom>}"
  then have "T = {} \<or> T = {\<bottom>}" by fast
  then have "T <<| \<bottom>" by auto
  moreover assume "T <<| t"
  ultimately have "t = \<bottom>" by (rule is_lub_unique[symmetric])
  then show "t \<in> {\<bottom>}" ..
qed auto

lemma p_bot: "stable_subdomain.p {\<bottom>}\<cdot>x = \<bottom>"
  using stable_subdomain.p_in_S[OF stable_subdomain_bot] by fast

lemma stable_subdomain_Inter:
  assumes "\<And>S. S \<in> \<S> \<Longrightarrow> stable_subdomain S"
  shows "stable_subdomain (\<Inter> \<S>)"
proof (unfold_locales)
  fix x y assume "y \<in> \<Inter> \<S>" and "x \<sqsubseteq> y"
  with assms show "x \<in> \<Inter> \<S>"
    by (auto intro: stable_subdomain.downward)
next
  fix T t assume T: "T \<subseteq> \<Inter> \<S>" and lub: "T <<| t"
  show "t \<in> \<Inter> \<S>"
  proof (rule InterI)
    fix X assume "X \<in> \<S>"
    with assms have "stable_subdomain X" by simp
    moreover from T \<open>X \<in> \<S>\<close> have "T \<subseteq> X" by auto
    ultimately show "t \<in> X" using lub by (rule stable_subdomain.lub_closed)
  qed
qed

text \<open>Jung, Lemma 4.1.5(ii) (one direction): a finer stable subdomain has a smaller projection.\<close>
(* NOTE: this can be shown without going to definitions by lemma deflation.belowI *)
lemma proj_mono_subdomain:
  assumes A: "stable_subdomain A" and S: "stable_subdomain S" and sub: "A \<subseteq> S"
  shows "stable_subdomain.proj A x \<sqsubseteq> stable_subdomain.proj S x"
proof -
  interpret A: stable_subdomain A by (rule A)
  interpret S: stable_subdomain S by (rule S)
  have "{a \<in> A. a \<sqsubseteq> x} \<subseteq> {s \<in> S. s \<sqsubseteq> x}" using sub by blast
  with A.proj_is_lub S.proj_is_lub show "A.proj x \<sqsubseteq> S.proj x"
    by (rule lub_subset_mono)
qed

text \<open>The projection-cfun version of @{thm proj_mono_subdomain}.\<close>
lemma p_mono_subdomain:
  assumes A: "stable_subdomain A" and S: "stable_subdomain S" and sub: "A \<subseteq> S"
  shows "stable_subdomain.p A \<sqsubseteq> stable_subdomain.p S"
proof (rule cfun_belowI)
  fix x
  interpret A: stable_subdomain A by (rule A)
  interpret S: stable_subdomain S by (rule S)
  show "stable_subdomain.p A\<cdot>x \<sqsubseteq> stable_subdomain.p S\<cdot>x"
    using proj_mono_subdomain[OF A S sub] by (simp add: A.p_beta S.p_beta)
qed

lemma stable_defl_subdomain_p:
  assumes "stable_subdomain S" shows "stable_defl (stable_subdomain.p S)"
proof -
  interpret stable_subdomain S by (rule assms)
  show ?thesis by (rule stable_defl_axioms)
qed

subsection \<open>Meets of stable deflations\<close>

text \<open>The composition of stable deflations has the intersection of the images as its image, and
  is again stable.  It is the pointwise meet, and the meet in the function space.\<close>

lemma stable_defl_oo_fixed:
  assumes p: "stable_defl p" and q: "stable_defl q"
  shows "(p oo q)\<cdot>y = y \<longleftrightarrow> p\<cdot>y = y \<and> q\<cdot>y = y"
proof
  interpret p: stable_defl p by (rule p)
  interpret q: stable_defl q by (rule q)
  assume y: "(p oo q)\<cdot>y = y"
  have "y \<sqsubseteq> q\<cdot>y" using p.below[of "q\<cdot>y"] y by simp
  then have qy: "q\<cdot>y = y" using q.below by (rule below_antisym[rotated])
  with y show "p\<cdot>y = y \<and> q\<cdot>y = y" by simp
qed simp

lemma stable_defl_oo:
  assumes p: "stable_defl p" and q: "stable_defl q"
  shows "stable_defl (p oo q)"
proof -
  interpret p: stable_defl p by (rule p)
  interpret q: stable_defl q by (rule q)
  show ?thesis
  proof standard
    fix x
    have "q\<cdot>(p\<cdot>(q\<cdot>x)) = p\<cdot>(q\<cdot>x)" using p.below by (rule q.lower_fixed)
    then show "(p oo q)\<cdot>((p oo q)\<cdot>x) = (p oo q)\<cdot>x" by (simp add: p.idem)
  next
    fix x
    show "(p oo q)\<cdot>x \<sqsubseteq> x" by (simp add: below_trans[OF p.below q.below])
  next
    fix x y assume "(p oo q)\<cdot>y = y" and xy: "x \<sqsubseteq> y"
    then have "p\<cdot>y = y" "q\<cdot>y = y" unfolding stable_defl_oo_fixed[OF p q] by simp_all
    with xy have "p\<cdot>x = x" "q\<cdot>x = x" by (simp_all add: p.downclosed q.downclosed)
    then show "(p oo q)\<cdot>x = x" by simp
  qed
qed

lemma stable_defl_oo_glb:
  assumes p: "stable_defl p" and q: "stable_defl q"
  shows "is_glb {p\<cdot>x, q\<cdot>x} (p\<cdot>(q\<cdot>x))"
proof (rule is_glbI)
  interpret p: stable_defl p by (rule p)
  interpret q: stable_defl q by (rule q)
  fix z assume "z \<in> {p\<cdot>x, q\<cdot>x}"
  moreover have "p\<cdot>(q\<cdot>x) \<sqsubseteq> p\<cdot>x" using q.below by (rule monofun_cfun_arg)
  ultimately show "p\<cdot>(q\<cdot>x) \<sqsubseteq> z" using p.below by auto
next
  interpret p: stable_defl p by (rule p)
  interpret q: stable_defl q by (rule q)
  fix l assume "\<forall>z\<in>{p\<cdot>x, q\<cdot>x}. l \<sqsubseteq> z"
  then have lp: "l \<sqsubseteq> p\<cdot>x" and lq: "l \<sqsubseteq> q\<cdot>x" by simp_all
  have "p\<cdot>l = l" using lp by (rule p.lower_fixed)
  moreover from lq have "p\<cdot>l \<sqsubseteq> p\<cdot>(q\<cdot>x)" by (rule monofun_cfun_arg)
  ultimately show "l \<sqsubseteq> p\<cdot>(q\<cdot>x)" by simp
qed

lemma stable_defl_meet_oo:
  assumes p: "stable_defl p" and q: "stable_defl q"
  shows "p \<sqinter> q = p oo q"
proof -
  note glb = stable_defl_oo_glb[OF p q]
  have "is_glb {p, q} (p oo q)"
  proof (rule is_glbI)
    fix f assume "f \<in> {p, q}"
    then show "p oo q \<sqsubseteq> f"
      by (auto intro!: cfun_belowI intro: is_glb_below[OF glb])
  next
    fix f assume "\<forall>g\<in>{p, q}. f \<sqsubseteq> g"
    then have "f\<cdot>x \<sqsubseteq> p\<cdot>x" "f\<cdot>x \<sqsubseteq> q\<cdot>x" for x by (auto intro: monofun_cfun_fun)
    then show "f \<sqsubseteq> p oo q"
      by (auto intro!: cfun_belowI is_glb_greatest[OF glb])
  qed
  then show ?thesis unfolding meet_def by (rule glb_eqI)
qed

subsection \<open>Arbitrary meets and directed joins\<close>

text \<open>The glb in the function space of a nonempty family of stable deflations is again a stable
  deflation, with the intersection of the images as its image.  Each value \<open>g\<cdot>x\<close> lies below the
  image elements \<open>d\<cdot>x\<close>, hence in every image; conversely a compact \<open>k\<close> in every image yields the
  step function \<open>stepfn k k\<close>, a lower bound of the family, so \<open>k \<sqsubseteq> g\<cdot>k\<close>.  Algebraicity extends this
  to all common fixed points.\<close>

lemma stable_defl_glb_fixes:
  assumes ne: "\<D> \<noteq> {}" and st: "\<And>d. d \<in> \<D> \<Longrightarrow> stable_defl d"
  shows "glb \<D>\<cdot>y = y \<longleftrightarrow> (\<forall>d\<in>\<D>. d\<cdot>y = y)"
proof -
  obtain g0 where "is_glb \<D> g0" using ne by (rule bounded_complete_class.is_glb)
  then have g: "is_glb \<D> (glb \<D>)" by (rule is_glb_glb)
  from ne obtain d0 where d0: "d0 \<in> \<D>" by blast
  have "glb \<D>\<cdot>x \<sqsubseteq> d0\<cdot>x" for x using is_glb_below[OF g d0] by (rule monofun_cfun_fun)
  then have below: "glb \<D>\<cdot>x \<sqsubseteq> x" for x
    using stable_defl.deflation[OF st[OF d0]] by (blast intro: below_trans deflation.below)
  show ?thesis
  proof
    assume fy: "glb \<D>\<cdot>y = y"
    show "\<forall>d\<in>\<D>. d\<cdot>y = y"
    proof
      fix d assume d: "d \<in> \<D>"
      have "glb \<D>\<cdot>y \<sqsubseteq> d\<cdot>y" using is_glb_below[OF g d] by (rule monofun_cfun_fun)
      with fy show "d\<cdot>y = y" by (simp add: stable_defl.lower_fixed[OF st[OF d]])
    qed
  next
    assume fix_all: "\<forall>d\<in>\<D>. d\<cdot>y = y"
    obtain C where C: "chain C" "\<forall>i. compact (C i)" "y = (\<Squnion>i. C i)"
      by (rule obtain_compact_chain)
    have "C i \<sqsubseteq> glb \<D>\<cdot>y" for i
    proof -
      have Ci: "C i \<sqsubseteq> y" using is_ub_thelub[OF C(1)] C(3) by simp
      have "stepfn (C i) (C i) \<sqsubseteq> d" if d: "d \<in> \<D>" for d
      proof -
        have "d\<cdot>(C i) = C i"
          using fix_all d Ci by (blast intro: stable_defl.downclosed[OF st[OF d]])
        then show ?thesis by (simp add: stepfn_below_iff[OF C(2)[rule_format]])
      qed
      then have "stepfn (C i) (C i) \<sqsubseteq> glb \<D>" by (blast intro: is_glb_greatest[OF g])
      then have "stepfn (C i) (C i)\<cdot>y \<sqsubseteq> glb \<D>\<cdot>y" by (rule monofun_cfun_fun)
      with Ci show ?thesis by (simp add: stepfn_beta[OF C(2)[rule_format]])
    qed
    then have "y \<sqsubseteq> glb \<D>\<cdot>y" unfolding C(3) by (rule lub_below[OF C(1)])
    then show "glb \<D>\<cdot>y = y" by (rule below_antisym[OF below])
  qed
qed

lemma stable_defl_glb:
  assumes ne: "\<D> \<noteq> {}" and st: "\<And>d. d \<in> \<D> \<Longrightarrow> stable_defl d"
  shows "stable_defl (glb \<D>)"
proof -
  note fx = stable_defl_glb_fixes[OF ne st]
  obtain g0 where "is_glb \<D> g0" using ne by (rule bounded_complete_class.is_glb)
  then have g: "is_glb \<D> (glb \<D>)" by (rule is_glb_glb)
  have fixed: "d\<cdot>(glb \<D>\<cdot>x) = glb \<D>\<cdot>x" if d: "d \<in> \<D>" for d x
  proof -
    have "glb \<D>\<cdot>x \<sqsubseteq> d\<cdot>x" using is_glb_below[OF g d] by (rule monofun_cfun_fun)
    then show ?thesis by (rule stable_defl.lower_fixed[OF st[OF d]])
  qed
  from ne obtain d0 where d0: "d0 \<in> \<D>" by blast
  have below: "glb \<D>\<cdot>x \<sqsubseteq> x" for x
    using monofun_cfun_fun[OF is_glb_below[OF g d0]] stable_defl.deflation[OF st[OF d0]]
    by (blast intro: below_trans deflation.below)
  show ?thesis
  proof standard
    fix x show "glb \<D>\<cdot>(glb \<D>\<cdot>x) = glb \<D>\<cdot>x" using fixed by (simp add: fx)
  next
    fix x show "glb \<D>\<cdot>x \<sqsubseteq> x" by (rule below)
  next
    fix x y assume "glb \<D>\<cdot>y = y" and xy: "x \<sqsubseteq> y"
    then have "\<forall>d\<in>\<D>. d\<cdot>y = y" by (simp add: fx)
    with xy have "\<forall>d\<in>\<D>. d\<cdot>x = x" by (blast intro: stable_defl.downclosed[OF st])
    then show "glb \<D>\<cdot>x = x" by (simp add: fx)
  qed
qed

text \<open>The lub of a directed family of stable deflations is a stable deflation: stable deflations
  are admissible (@{thm [source] adm_stable_defl}), and admissible predicates are closed under
  directed lubs.\<close>

lemma stable_defl_directed_lub:
  assumes dir: "directed \<D>" and ne: "\<D> \<noteq> {}" and st: "\<And>d. d \<in> \<D> \<Longrightarrow> stable_defl d"
  shows "stable_defl (lub \<D>)"
  by (rule directed_admD[OF adm_stable_defl dir ne]) (simp add: st)

section \<open>The domain of stable subdomains\<close>

text \<open>Stable subdomains are represented by their projections, the stable deflations.  These are
  closed under \<open>\<bottom>\<close> and admissible, so they form a pcpo under the pointwise order; the lattice order
  is the same order.  Binary meets are compositions and arbitrary meets are glbs in the function
  space; binary and arbitrary joins are the meets of the upper bounds.\<close>

pcpodef 'a stable_subdom = "{d :: 'a \<rightarrow> 'a. stable_defl d}"
  morphisms stable_subdom_p subdom_of_defl
  by (simp_all add: stable_defl_bottom adm_stable_defl)

notation stable_subdom_p (\<open>\<p>\<index>\<close>)

setup_lifting type_definition_stable_subdom

lemma stable_defl_stable_subdom_p [simp]: "stable_defl \<p>\<^bsub>A\<^esub>"
  using stable_subdom_p by simp

lemma stable_subdom_below_iff: "A \<sqsubseteq> B \<longleftrightarrow> \<p>\<^bsub>A\<^esub> \<sqsubseteq> \<p>\<^bsub>B\<^esub>"
  by (simp add: below_stable_subdom_def)

lemma stable_subdom_proj_eqI: "\<p>\<^bsub>A\<^esub> = \<p>\<^bsub>B\<^esub> \<Longrightarrow> A = B"
  by (simp add: stable_subdom_p_inject)

lemma stable_subdom_p_subdom_of_defl: "stable_defl d \<Longrightarrow> \<p>\<^bsub>subdom_of_defl d\<^esub> = d"
  by (simp add: subdom_of_defl_inverse)

instantiation stable_subdom :: ("{bifinite, bounded_complete}") complete_lattice
begin

lift_definition less_eq_stable_subdom :: "'a stable_subdom \<Rightarrow> 'a stable_subdom \<Rightarrow> bool"
  is "(\<sqsubseteq>)" .

lift_definition less_stable_subdom :: "'a stable_subdom \<Rightarrow> 'a stable_subdom \<Rightarrow> bool"
  is "\<lambda>p q. p \<sqsubseteq> q \<and> \<not> q \<sqsubseteq> p" .

lift_definition inf_stable_subdom :: "'a stable_subdom \<Rightarrow> 'a stable_subdom \<Rightarrow> 'a stable_subdom"
  is "\<lambda>p q. p \<sqinter> q" by (simp add: stable_defl_meet_oo stable_defl_oo)

lift_definition top_stable_subdom :: "'a stable_subdom"
  is ID by (rule stable_defl_ID)

lift_definition bot_stable_subdom :: "'a stable_subdom"
  is \<bottom> by (rule stable_defl_bottom)

lift_definition Inf_stable_subdom :: "'a stable_subdom set \<Rightarrow> 'a stable_subdom"
  is "\<lambda>\<D>. if \<D> = {} then ID else glb \<D>"
  by (auto intro: stable_defl_ID stable_defl_glb)

definition sup_stable_subdom :: "'a stable_subdom \<Rightarrow> 'a stable_subdom \<Rightarrow> 'a stable_subdom"
  where "sup_stable_subdom A B = Inf {C. A \<le> C \<and> B \<le> C}"

definition Sup_stable_subdom :: "'a stable_subdom set \<Rightarrow> 'a stable_subdom"
  where "Sup_stable_subdom \<A> = Inf {C. \<forall>A\<in>\<A>. A \<le> C}"

lemma Inf_lower_stable_subdom: "A \<in> \<D> \<Longrightarrow> Inf \<D> \<le> A" for A :: "'a stable_subdom"
proof transfer
  fix \<D> :: "('a \<rightarrow> 'a) set" and a
  assume "a \<in> \<D>"
  then have "\<D> \<noteq> {}" by blast
  then obtain g where "is_glb \<D> g" by (rule bounded_complete_class.is_glb)
  with \<open>a \<in> \<D>\<close> show "(if \<D> = {} then ID else glb \<D>) \<sqsubseteq> a"
    by (auto intro: is_glb_below[OF is_glb_glb])
qed

lemma Inf_greatest_stable_subdom: "(\<And>C. C \<in> \<D> \<Longrightarrow> A \<le> C) \<Longrightarrow> A \<le> Inf \<D>" for A :: "'a stable_subdom"
proof transfer
  fix \<D> :: "('a \<rightarrow> 'a) set" and a
  assume D: "Ball \<D> stable_defl" and st: "stable_defl a"
    and lb: "\<And>c. stable_defl c \<Longrightarrow> c \<in> \<D> \<Longrightarrow> a \<sqsubseteq> c"
  show "a \<sqsubseteq> (if \<D> = {} then ID else glb \<D>)"
  proof (cases "\<D> = {}")
    case True
    then show ?thesis using deflation.below_ID[OF stable_defl.deflation[OF st]] by simp
  next
    case False
    then obtain g where "is_glb \<D> g" by (rule bounded_complete_class.is_glb)
    with False D lb show ?thesis by (auto intro: is_glb_greatest[OF is_glb_glb])
  qed
qed

lemma bot_le_stable_subdom: "bot \<le> A" for A :: "'a stable_subdom"
  by transfer simp

lemma le_antisym_stable_subdom: "A \<le> B \<Longrightarrow> B \<le> A \<Longrightarrow> A = B" for A :: "'a stable_subdom"
  by transfer (rule below_antisym)

instance
proof
  fix A B C :: "'a stable_subdom" and \<D> :: "'a stable_subdom set"
  show "(A < B) = (A \<le> B \<and> \<not> B \<le> A)" by transfer simp
  show "A \<le> A" by transfer simp
  show "A \<le> B \<Longrightarrow> B \<le> C \<Longrightarrow> A \<le> C" by transfer (rule below_trans)
  show "A \<le> B \<Longrightarrow> B \<le> A \<Longrightarrow> A = B" by transfer (rule below_antisym)
  show "inf A B \<le> A" by transfer (rule meet_below1)
  show "inf A B \<le> B" by transfer (rule meet_below2)
  show "A \<le> B \<Longrightarrow> A \<le> C \<Longrightarrow> A \<le> inf B C" by transfer (rule meet_greatest)
  show "A \<le> sup A B" "B \<le> sup A B"
    unfolding sup_stable_subdom_def by (auto intro: Inf_greatest_stable_subdom)
  show "A \<le> C \<Longrightarrow> B \<le> C \<Longrightarrow> sup A B \<le> C"
    unfolding sup_stable_subdom_def by (auto intro: Inf_lower_stable_subdom)
  show "A \<in> \<D> \<Longrightarrow> Inf \<D> \<le> A" by (rule Inf_lower_stable_subdom)
  show "(\<And>B. B \<in> \<D> \<Longrightarrow> A \<le> B) \<Longrightarrow> A \<le> Inf \<D>" by (rule Inf_greatest_stable_subdom)
  show "A \<in> \<D> \<Longrightarrow> A \<le> Sup \<D>"
    unfolding Sup_stable_subdom_def by (auto intro: Inf_greatest_stable_subdom)
  show "(\<And>B. B \<in> \<D> \<Longrightarrow> B \<le> A) \<Longrightarrow> Sup \<D> \<le> A"
    unfolding Sup_stable_subdom_def by (auto intro: Inf_lower_stable_subdom)
  show "Inf {} = (top :: 'a stable_subdom)" by transfer simp
  show "Sup {} = (bot :: 'a stable_subdom)"
    unfolding Sup_stable_subdom_def
    by (rule le_antisym_stable_subdom[OF Inf_lower_stable_subdom bot_le_stable_subdom]) simp
qed

end

text \<open>The domain order is the lattice order; hence the domain is bounded complete, indeed every
  set has a lub.\<close>

lemma below_stable_subdom_iff_le: "A \<sqsubseteq> B \<longleftrightarrow> A \<le> B" for A B :: "'a stable_subdom"
  by (simp add: stable_subdom_below_iff less_eq_stable_subdom.rep_eq)

lemma stable_subdom_is_lub: "\<A> <<| Sup \<A>" for \<A> :: "'a stable_subdom set"
  by (auto intro!: is_lubI is_ubI Sup_upper Sup_least
      simp: below_stable_subdom_iff_le is_ub_def)

instance stable_subdom :: ("{bifinite, bounded_complete}") bounded_complete
  by standard (blast intro: stable_subdom_is_lub)

instance stable_subdom :: ("{bifinite, bounded_complete}") lattice_complete
  by intro_classes (rule exI[of _ top], simp add: below_stable_subdom_iff_le)

lemma p_below_iff_le: "\<p>\<^bsub>A\<^esub> \<sqsubseteq> \<p>\<^bsub>B\<^esub> \<longleftrightarrow> A \<le> B"
  by (simp add: less_eq_stable_subdom.rep_eq)

lemma le_of_p_below: "\<p>\<^bsub>A\<^esub> \<sqsubseteq> \<p>\<^bsub>B\<^esub> \<Longrightarrow> A \<le> B" and p_below_of_le: "A \<le> B \<Longrightarrow> \<p>\<^bsub>A\<^esub> \<sqsubseteq> \<p>\<^bsub>B\<^esub>"
  by (simp_all add: p_below_iff_le)

lemma p_inf_meet_rep: "\<p>\<^bsub>inf A B\<^esub> = \<p>\<^bsub>A\<^esub> \<sqinter> \<p>\<^bsub>B\<^esub>"
  by (rule inf_stable_subdom.rep_eq)

text \<open>The meet is composition (@{thm [source] stable_defl_meet_oo}).\<close>

lemma p_inf: "\<p>\<^bsub>inf A B\<^esub> = \<p>\<^bsub>A\<^esub> oo \<p>\<^bsub>B\<^esub>"
  by (simp add: p_inf_meet_rep stable_defl_meet_oo)

lemma p_bot_stable_subdom: "\<p>\<^bsub>bot\<^esub> = \<bottom>" and p_top_stable_subdom: "\<p>\<^bsub>top\<^esub> = ID"
  by (simp_all add: bot_stable_subdom.rep_eq top_stable_subdom.rep_eq)

subsection \<open>Images as sets\<close>

text \<open>The image of the projection is the stable subdomain; conversely a stable subdomain gives
  the element represented by its projection.\<close>

definition set_of_subdom :: "'a stable_subdom \<Rightarrow> 'a set"
  where "set_of_subdom A = {x. \<p>\<^bsub>A\<^esub>\<cdot>x = x}"

definition subdom_of_set :: "'a set \<Rightarrow> 'a stable_subdom"
  where "subdom_of_set S = subdom_of_defl (stable_subdomain.p S)"

lemma p_fixes: "\<p>\<^bsub>A\<^esub>\<cdot>x = x \<longleftrightarrow> x \<in> set_of_subdom A"
  by (simp add: set_of_subdom_def)

lemma stable_subdomain_of_set_of_subdom: "stable_subdomain (set_of_subdom A)"
  unfolding set_of_subdom_def by (rule stable_defl_stable_subdomain) simp

interpretation subdom: stable_subdomain "set_of_subdom A"
  rewrites "stable_subdomain.p (set_of_subdom A) \<equiv> \<p>\<^bsub>A\<^esub>"
proof -
  show "stable_subdomain (set_of_subdom A)" by (rule stable_subdomain_of_set_of_subdom)
  show "stable_subdomain.p (set_of_subdom A) \<equiv> \<p>\<^bsub>A\<^esub>"
    unfolding set_of_subdom_def
    by (rule eq_reflection, rule stable_subdomain_deflation[symmetric])
      (simp_all add: stable_defl.deflation stable_defl_stable_subdomain)
qed

lemma stable_subdom_p_subdom_of_set:
  "stable_subdomain S \<Longrightarrow> \<p>\<^bsub>subdom_of_set S\<^esub> = stable_subdomain.p S"
  unfolding subdom_of_set_def by (rule stable_subdom_p_subdom_of_defl, rule stable_defl_subdomain_p)

lemma set_of_subdom_of_set: "stable_subdomain S \<Longrightarrow> set_of_subdom (subdom_of_set S) = S"
  by (simp add: set_of_subdom_def stable_subdom_p_subdom_of_set stable_subdomain.p_fixes)

lemma set_of_subdom_inf: "set_of_subdom (inf A B) = set_of_subdom A \<inter> set_of_subdom B"
  unfolding set_of_subdom_def p_inf
    stable_defl_oo_fixed[OF stable_defl_stable_subdom_p stable_defl_stable_subdom_p]
  by blast

lemma stable_subdomain_Int:
  "stable_subdomain S \<Longrightarrow> stable_subdomain T \<Longrightarrow> stable_subdomain (S \<inter> T)"
  using stable_subdomain_Inter[of "{S, T}"] by auto


section \<open>Distributive domains: joins of stable subdomains\<close>

default_sort "{bifinite, distributive_cpo}"

text \<open>Jung, Lemma 4.1.6(ii) (binary form): a stable deflation preserves existing joins.  This is
  where distributivity of the domain is used.\<close>

lemma stable_defl_image_join:
  fixes d :: "'a \<rightarrow> 'a"
  assumes d: "stable_defl d" and j: "x \<Up> y"
  shows "d\<cdot>(x \<squnion> y) = d\<cdot>x \<squnion> d\<cdot>y"
proof -
  interpret stable_defl d by (rule d)
  have px: "d\<cdot>x = x \<sqinter> d\<cdot>(x \<squnion> y)"
    by (rule stable_defl_image_meet[OF d idem monofun_cfun_arg[OF joinableD(1)[OF j]]])
  have py: "d\<cdot>y = y \<sqinter> d\<cdot>(x \<squnion> y)"
    by (rule stable_defl_image_meet[OF d idem monofun_cfun_arg[OF joinableD(2)[OF j]]])
  have "d\<cdot>x \<squnion> d\<cdot>y = (x \<sqinter> d\<cdot>(x \<squnion> y)) \<squnion> (y \<sqinter> d\<cdot>(x \<squnion> y))"
    using px py by simp
  also have "\<dots> = (x \<squnion> y) \<sqinter> d\<cdot>(x \<squnion> y)"
    by (rule meet_join_distrib2[OF j, symmetric])
  also have "\<dots> = d\<cdot>(x \<squnion> y)"
    by (metis meet_sym meet_absorbI below)
  finally show ?thesis by (rule sym)
qed

subsection \<open>Joins of stable deflations\<close>

text \<open>Jung, Lemma 4.1.9 in deflation form.  Deflations lie below @{term ID}, so they are joinable,
  and their join is pointwise.  It is idempotent because each deflation preserves the joins of the
  other's images, and its image is downward closed because, below an image element
  \<open>y = p\<cdot>y \<squnion> q\<cdot>y\<close>, distributivity splits \<open>x = (x \<sqinter> p\<cdot>y) \<squnion> (x \<sqinter> q\<cdot>y) = p\<cdot>x \<squnion> q\<cdot>x\<close>.\<close>


lemma stable_defl_join_app:
  fixes p :: "'a \<rightarrow> 'a"
  assumes p: "stable_defl p" and q: "stable_defl q"
  shows "(p \<squnion> q)\<cdot>x = p\<cdot>x \<squnion> q\<cdot>x"
  by (rule cfun_join[OF deflation_joinable[OF stable_defl.deflation[OF p]
        stable_defl.deflation[OF q]]])

lemma stable_defl_join:
  fixes p :: "'a \<rightarrow> 'a"
  assumes p: "stable_defl p" and q: "stable_defl q"
  shows "stable_defl (p \<squnion> q)"
proof -
  interpret p: stable_defl p by (rule p)
  interpret q: stable_defl q by (rule q)
  have pq: "p\<cdot>x \<Up> q\<cdot>x" for x by (rule joinableI[OF p.below q.below])
  note app = stable_defl_join_app[OF p q]
  show ?thesis
  proof standard
    fix x
    have "p\<cdot>(p\<cdot>x \<squnion> q\<cdot>x) = p\<cdot>x \<squnion> p\<cdot>(q\<cdot>x)"
      by (simp add: stable_defl_image_join[OF p pq] p.idem)
    also have "\<dots> = p\<cdot>x" by (rule join_absorb2, rule monofun_cfun_arg, rule q.below)
    finally have pj: "p\<cdot>(p\<cdot>x \<squnion> q\<cdot>x) = p\<cdot>x" .
    have "q\<cdot>(p\<cdot>x \<squnion> q\<cdot>x) = q\<cdot>(p\<cdot>x) \<squnion> q\<cdot>x"
      by (simp add: stable_defl_image_join[OF q pq] q.idem)
    also have "\<dots> = q\<cdot>x" by (rule join_absorb, rule monofun_cfun_arg, rule p.below)
    finally have qj: "q\<cdot>(p\<cdot>x \<squnion> q\<cdot>x) = q\<cdot>x" .
    show "(p \<squnion> q)\<cdot>((p \<squnion> q)\<cdot>x) = (p \<squnion> q)\<cdot>x" by (simp add: app pj qj)
  next
    fix x
    show "(p \<squnion> q)\<cdot>x \<sqsubseteq> x" unfolding app by (rule join_belowI[OF p.below q.below])
  next
    fix x y assume y: "(p \<squnion> q)\<cdot>y = y" and xy: "x \<sqsubseteq> y"
    have px: "p\<cdot>x = x \<sqinter> p\<cdot>y"
      by (rule stable_defl_image_meet[OF p p.idem monofun_cfun_arg[OF xy]])
    have qx: "q\<cdot>x = x \<sqinter> q\<cdot>y"
      by (rule stable_defl_image_meet[OF q q.idem monofun_cfun_arg[OF xy]])
    have "x = x \<sqinter> y" using xy by (simp add: meet_absorbI)
    also have "\<dots> = x \<sqinter> (p\<cdot>y \<squnion> q\<cdot>y)" using y by (simp add: app)
    also have "\<dots> = (x \<sqinter> p\<cdot>y) \<squnion> (x \<sqinter> q\<cdot>y)" by (rule meet_join_distrib[OF pq])
    also have "\<dots> = (p \<squnion> q)\<cdot>x" by (simp add: app px qx)
    finally show "(p \<squnion> q)\<cdot>x = x" by (rule sym)
  qed
qed

text \<open>The slide rule: below \<open>y = p\<cdot>y \<squnion> q\<cdot>y\<close>, slide \<open>x\<close> first through @{term p} onto \<open>p\<cdot>y\<close>, then
  \<open>p\<cdot>y \<squnion> x\<close> through @{term q} onto \<open>q\<cdot>y\<close>.\<close>

lemma semi_factor_defl_join:
  assumes p: "semi_factor_defl p" and q: "semi_factor_defl q"
  shows "semi_factor_defl (p \<squnion> q)"
proof -
  interpret p: semi_factor_defl p by (rule p)
  interpret q: semi_factor_defl q by (rule q)
  note app = stable_defl_join_app[OF p.stable_defl_axioms q.stable_defl_axioms]
  show ?thesis
  proof (rule semi_factor_deflI)
    show "stable_defl (p \<squnion> q)"
      by (rule stable_defl_join[OF p.stable_defl_axioms q.stable_defl_axioms])
    fix x y assume y: "(p \<squnion> q)\<cdot>y = y" and le: "(p \<squnion> q)\<cdot>x \<sqsubseteq> y"
    have pq: "p\<cdot>z \<Up> q\<cdot>z" for z by (rule joinableI[OF p.below q.below])
    have yab: "y = p\<cdot>y \<squnion> q\<cdot>y" using y by (simp add: app)
    from le have pxy: "p\<cdot>x \<sqsubseteq> y" and qxy: "q\<cdot>x \<sqsubseteq> y"
      unfolding app by (auto intro: below_trans joinableD[OF pq])
    have "p\<cdot>x \<sqsubseteq> p\<cdot>y" using p.idem pxy by (rule p.below_image)
    with p.idem have x_pa: "x \<Up> p\<cdot>y" by (rule p.slide)
    then have pa_x: "p\<cdot>y \<Up> x" by (simp add: joinable_sym)
    have "q\<cdot>(p\<cdot>y \<squnion> x) = q\<cdot>(p\<cdot>y) \<squnion> q\<cdot>x"
      by (rule stable_defl_image_join[OF q.stable_defl_axioms pa_x])
    also have "\<dots> \<sqsubseteq> q\<cdot>y"
      by (rule join_belowI[OF monofun_cfun_arg[OF p.below] q.below_image[OF q.idem qxy]])
    finally have "q\<cdot>(p\<cdot>y \<squnion> x) \<sqsubseteq> q\<cdot>y" .
    with q.idem have pax_pb: "p\<cdot>y \<squnion> x \<Up> q\<cdot>y" by (rule q.slide)
    let ?w = "(p\<cdot>y \<squnion> x) \<squnion> q\<cdot>y"
    note w = joinableD[OF pax_pb]
    have "x \<sqsubseteq> ?w" using joinableD(2)[OF pa_x] w(1) by (rule below_trans)
    moreover have "p\<cdot>y \<squnion> q\<cdot>y \<sqsubseteq> ?w"
      by (rule join_belowI[OF below_trans[OF joinableD(1)[OF pa_x] w(1)] w(2)])
    then have "y \<sqsubseteq> ?w" by (simp only: yab[symmetric])
    ultimately show "x \<Up> y" by (rule joinableI)
  qed
qed

text \<open>The image of the join is the set of joins of image elements (Jung, Lemma 4.1.9): every image
  element is \<open>p\<cdot>x \<squnion> q\<cdot>x\<close>, and a joinable \<open>a \<squnion> b\<close> of image elements lies below \<open>p\<cdot>(a \<squnion> b) \<squnion> q\<cdot>(a \<squnion> b)\<close>.\<close>

lemma stable_defl_join_fixes:
  fixes p :: "'a \<rightarrow> 'a"
  assumes p: "stable_defl p" and q: "stable_defl q"
  shows "{x. (p \<squnion> q)\<cdot>x = x} = {a \<squnion> b |a b. p\<cdot>a = a \<and> q\<cdot>b = b \<and> a \<Up> b}"
proof
  interpret p: stable_defl p by (rule p)
  interpret q: stable_defl q by (rule q)
  note app = stable_defl_join_app[OF p q]
  have pq: "p\<cdot>x \<Up> q\<cdot>x" for x by (rule joinableI[OF p.below q.below])
  show "{x. (p \<squnion> q)\<cdot>x = x} \<subseteq> {a \<squnion> b |a b. p\<cdot>a = a \<and> q\<cdot>b = b \<and> a \<Up> b}"
  proof
    fix x assume "x \<in> {x. (p \<squnion> q)\<cdot>x = x}"
    then have "x = p\<cdot>x \<squnion> q\<cdot>x" by (simp add: app)
    with pq[of x] p.idem q.idem show "x \<in> {a \<squnion> b |a b. p\<cdot>a = a \<and> q\<cdot>b = b \<and> a \<Up> b}" by blast
  qed
  show "{a \<squnion> b |a b. p\<cdot>a = a \<and> q\<cdot>b = b \<and> a \<Up> b} \<subseteq> {x. (p \<squnion> q)\<cdot>x = x}"
  proof
    fix x assume "x \<in> {a \<squnion> b |a b. p\<cdot>a = a \<and> q\<cdot>b = b \<and> a \<Up> b}"
    then obtain a b where a: "p\<cdot>a = a" and b: "q\<cdot>b = b" and ab: "a \<Up> b" and x: "x = a \<squnion> b"
      by blast
    have "a \<sqsubseteq> p\<cdot>(a \<squnion> b)" using a joinableD(1)[OF ab] by (rule p.below_image)
    moreover have "b \<sqsubseteq> q\<cdot>(a \<squnion> b)" using b joinableD(2)[OF ab] by (rule q.below_image)
    ultimately have "a \<squnion> b \<sqsubseteq> p\<cdot>(a \<squnion> b) \<squnion> q\<cdot>(a \<squnion> b)"
      by (blast intro: join_belowI below_trans joinableD[OF pq])
    moreover have "p\<cdot>(a \<squnion> b) \<squnion> q\<cdot>(a \<squnion> b) \<sqsubseteq> a \<squnion> b" by (rule join_belowI[OF p.below q.below])
    ultimately show "x \<in> {x. (p \<squnion> q)\<cdot>x = x}" unfolding x by (simp add: app below_antisym)
  qed
qed

text \<open>The set form, for stable subdomains given as sets.\<close>

lemma semi_factor_subdomain_join:
  fixes A B :: "'a set"
  assumes A: "semi_factor_subdomain A" and B: "semi_factor_subdomain B"
  shows "semi_factor_subdomain {a \<squnion> b |a b. a \<in> A \<and> b \<in> B \<and> a \<Up> b}"
proof -
  note sA = semi_factor_subdomain.axioms(1)[OF A] and sB = semi_factor_subdomain.axioms(1)[OF B]
  have p: "semi_factor_defl (stable_subdomain.p A)" by (rule semi_factor_defl_p[OF A])
  have q: "semi_factor_defl (stable_subdomain.p B)" by (rule semi_factor_defl_p[OF B])
  have "{x. (stable_subdomain.p A \<squnion> stable_subdomain.p B)\<cdot>x = x}
      = {a \<squnion> b |a b. a \<in> A \<and> b \<in> B \<and> a \<Up> b}"
    unfolding stable_defl_join_fixes[OF p[THEN semi_factor_defl.axioms(1)]
        q[THEN semi_factor_defl.axioms(1)]]
    by (simp add: stable_subdomain.p_fixed_iff[OF sA] stable_subdomain.p_fixed_iff[OF sB])
  with semi_factor_defl_join[OF p q] show ?thesis by (simp add: semi_factor_defl_iff)
qed

text \<open>The slide rule passes through composition as for the meet of semi-factors (Jung, Lemma
  4.1.9(ii)): first through the outer, then through the inner deflation.\<close>

lemma semi_factor_defl_oo:
  assumes p: "semi_factor_defl p" and q: "semi_factor_defl q"
  shows "semi_factor_defl (p oo q)"
proof -
  interpret p: semi_factor_defl p by (rule p)
  interpret q: semi_factor_defl q by (rule q)
  show ?thesis
  proof (rule semi_factor_deflI)
    show "stable_defl (p oo q)" by (rule stable_defl_oo[OF p.stable_defl_axioms q.stable_defl_axioms])
    fix x y assume y: "(p oo q)\<cdot>y = y" and px: "(p oo q)\<cdot>x \<sqsubseteq> y"
    from y have py: "p\<cdot>y = y" and qy: "q\<cdot>y = y"
      unfolding stable_defl_oo_fixed[OF p.stable_defl_axioms q.stable_defl_axioms] by simp_all
    from px have "p\<cdot>(q\<cdot>x) \<sqsubseteq> y" by simp
    with py have step1: "q\<cdot>x \<Up> y" by (rule p.slide)
    have "{q\<cdot>x, y} \<subseteq> {z. q\<cdot>z = z}" by (simp add: qy q.idem)
    then have memB: "q\<cdot>(q\<cdot>x \<squnion> y) = q\<cdot>x \<squnion> y"
      by (rule deflation_lub_closed[OF q.deflation _ joinable_lub[OF step1]])
    from step1 have "q\<cdot>x \<sqsubseteq> q\<cdot>x \<squnion> y" by (rule joinableD(1))
    with memB have step2: "x \<Up> q\<cdot>x \<squnion> y" by (rule q.slide)
    then have "x \<sqsubseteq> x \<squnion> (q\<cdot>x \<squnion> y)" by (rule joinableD(1))
    moreover from step1 step2 have "y \<sqsubseteq> x \<squnion> (q\<cdot>x \<squnion> y)"
      by (blast dest: joinableD(2) below_trans)
    ultimately show "x \<Up> y" by (rule joinableI)
  qed
qed

lemma semi_factor_defl_ID: "semi_factor_defl ID"
  by (rule semi_factor_deflI[OF stable_defl_ID]) (auto intro: joinableI)

subsection \<open>Joins in the domain of stable subdomains\<close>

text \<open>Over a distributive domain the binary join is pointwise.\<close>

lemma p_sup: "\<p>\<^bsub>sup A B\<^esub> = \<p>\<^bsub>A\<^esub> \<squnion> \<p>\<^bsub>B\<^esub>" for A B :: "'a stable_subdom"
proof -
  let ?j = "\<p>\<^bsub>A\<^esub> \<squnion> \<p>\<^bsub>B\<^esub>"
  have st: "stable_defl ?j" by (rule stable_defl_join) simp_all
  have jl: "{\<p>\<^bsub>A\<^esub>, \<p>\<^bsub>B\<^esub>} <<| ?j"
    by (rule joinable_lub, rule deflation_joinable) (simp_all add: stable_defl.deflation)
  have "sup A B \<le> subdom_of_defl ?j"
    using is_lubD1[OF jl]
    by (intro sup_least; simp add: p_below_iff_le[symmetric] stable_subdom_p_subdom_of_defl[OF st])
  then have "\<p>\<^bsub>sup A B\<^esub> \<sqsubseteq> ?j" by (simp add: p_below_iff_le[symmetric] stable_subdom_p_subdom_of_defl[OF st])
  moreover have "?j \<sqsubseteq> \<p>\<^bsub>sup A B\<^esub>"
    by (rule is_lubD2[OF jl]) (simp add: p_below_iff_le)
  ultimately show ?thesis by (rule below_antisym)
qed

lemma p_sup_join: "\<p>\<^bsub>sup a b\<^esub>\<cdot>x = \<p>\<^bsub>a\<^esub>\<cdot>x \<squnion> \<p>\<^bsub>b\<^esub>\<cdot>x" for a b :: "'a stable_subdom"
  by (simp add: p_sup stable_defl_join_app)

lemma set_of_subdom_sup:
  fixes A B :: "'a stable_subdom"
  shows "set_of_subdom (sup A B) =
    {a \<squnion> b |a b. a \<in> set_of_subdom A \<and> b \<in> set_of_subdom B \<and> a \<Up> b}"
  unfolding set_of_subdom_def p_sup stable_defl_join_fixes[OF stable_defl_stable_subdom_p
      stable_defl_stable_subdom_p]
  by simp

text \<open>Directed joins are pointwise lubs, already over bounded-complete domains
  (@{thm [source] stable_defl_directed_lub}).\<close>

lemma p_Sup_directed:
  fixes \<A> :: "'b::{bifinite, bounded_complete} stable_subdom set"
  assumes directed: "\<And>X Y. X \<in> \<A> \<Longrightarrow> Y \<in> \<A> \<Longrightarrow> \<exists>Z \<in> \<A>. X \<le> Z \<and> Y \<le> Z"
    and nonempty: "\<A> \<noteq> {}"
  shows "\<p>\<^bsub>Sup \<A>\<^esub> = lub ((\<lambda>A. \<p>\<^bsub>A\<^esub>) ` \<A>)" (is "_ = lub ?P")
proof -
  have dir: "directed ?P"
  proof (rule directedI)

    fix u v assume "u \<in> ?P" "v \<in> ?P"
    then obtain X Y where "X \<in> \<A>" "Y \<in> \<A>" "u = \<p>\<^bsub>X\<^esub>" "v = \<p>\<^bsub>Y\<^esub>" by blast
    with directed show "\<exists>z\<in>?P. u \<sqsubseteq> z \<and> v \<sqsubseteq> z" by (fastforce simp: p_below_iff_le)
  qed
  have ne: "?P \<noteq> {}" using nonempty by blast
  have st: "stable_defl (lub ?P)" by (rule stable_defl_directed_lub[OF dir ne]) auto
  note lubP = directed_lub[OF dir]
  have "Sup \<A> \<le> subdom_of_defl (lub ?P)"
  proof (rule Sup_least)
    fix A assume "A \<in> \<A>"
    then have "\<p>\<^bsub>A\<^esub> \<sqsubseteq> lub ?P" by (blast intro: is_ubD[OF is_lubD1[OF lubP]])
    then show "A \<le> subdom_of_defl (lub ?P)"
      by (simp add: p_below_iff_le[symmetric] stable_subdom_p_subdom_of_defl[OF st])
  qed
  then have "\<p>\<^bsub>Sup \<A>\<^esub> \<sqsubseteq> lub ?P"
    by (simp add: p_below_iff_le[symmetric] stable_subdom_p_subdom_of_defl[OF st])
  moreover have "lub ?P \<sqsubseteq> \<p>\<^bsub>Sup \<A>\<^esub>"
    by (rule is_lubD2[OF lubP], rule ub_imageI) (simp add: p_below_iff_le Sup_upper)
  ultimately show ?thesis by (rule below_antisym)
qed

lemma directed_stable_proj_sup:
  fixes \<A> :: "'b::{bifinite, bounded_complete} stable_subdom set"
  assumes directed: "\<And>X Y. X \<in> \<A> \<Longrightarrow> Y \<in> \<A> \<Longrightarrow> \<exists>Z \<in> \<A>. X \<le> Z \<and> Y \<le> Z"
    and nonempty: "\<A> \<noteq> {}"
  shows "(\<lambda>A. \<p>\<^bsub>A\<^esub>\<cdot>x) ` \<A> <<| \<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x"
proof -
  have dir: "directed ((\<lambda>A. \<p>\<^bsub>A\<^esub>) ` \<A>)"
  proof (rule directedI)

    fix u v assume "u \<in> (\<lambda>A. \<p>\<^bsub>A\<^esub>) ` \<A>" "v \<in> (\<lambda>A. \<p>\<^bsub>A\<^esub>) ` \<A>"
    then obtain X Y where "X \<in> \<A>" "Y \<in> \<A>" "u = \<p>\<^bsub>X\<^esub>" "v = \<p>\<^bsub>Y\<^esub>" by blast
    with directed show "\<exists>z\<in>(\<lambda>A. \<p>\<^bsub>A\<^esub>) ` \<A>. u \<sqsubseteq> z \<and> v \<sqsubseteq> z" by (fastforce simp: p_below_iff_le)
  qed
  have "(\<lambda>f. f\<cdot>x) ` ((\<lambda>A. \<p>\<^bsub>A\<^esub>) ` \<A>) <<| lub ((\<lambda>A. \<p>\<^bsub>A\<^esub>) ` \<A>)\<cdot>x"
    using nonempty by (intro cont_directed_is_lub[OF cont_Rep_cfun1 dir]) blast
  then show ?thesis by (simp add: p_Sup_directed[OF directed nonempty] image_image)
qed

subsection \<open>Semi-factors\<close>

text \<open>The bottom subdomain @{term \<open>{\<bottom>}\<close>} satisfies the slide condition trivially.\<close>
lemma semi_factor_subdomain_bot: "semi_factor_subdomain {\<bottom>}"
proof (intro semi_factor_subdomain.intro[OF stable_subdomain_bot] semi_factor_subdomain_axioms.intro)
  fix x y assume "y \<in> {\<bottom>}" and "stable_subdomain.p {\<bottom>}\<cdot>x \<sqsubseteq> y"
  then have "y = \<bottom>" by simp
  then show "x \<Up> y" by simp
qed

definition is_semi_factor :: "'a stable_subdom \<Rightarrow> bool"
  where "is_semi_factor A \<longleftrightarrow> semi_factor_defl \<p>\<^bsub>A\<^esub>"

lemma p_set_of_subdom: "stable_subdomain.p (set_of_subdom A) = \<p>\<^bsub>A\<^esub>"
  unfolding set_of_subdom_def
  by (rule stable_subdomain_deflation[symmetric])
    (simp_all add: stable_defl.deflation stable_defl_stable_subdomain)

lemma is_semi_factor_iff_subdomain: "is_semi_factor A \<longleftrightarrow> semi_factor_subdomain (set_of_subdom A)"
  unfolding is_semi_factor_def semi_factor_defl_iff
  by (simp add: set_of_subdom_def stable_defl.deflation)

lemma is_semi_factorI:
  assumes slide: "\<And>x y. y \<in> set_of_subdom A \<Longrightarrow> \<p>\<^bsub>A\<^esub>\<cdot>x \<sqsubseteq> y \<Longrightarrow> x \<Up> y"
  shows "is_semi_factor A"
  unfolding is_semi_factor_def
  by (rule semi_factor_deflI[OF stable_defl_stable_subdom_p]) (simp add: slide p_fixes)

lemma is_semi_factor_bot: "is_semi_factor bot"
  by (simp add: is_semi_factor_def p_bot_stable_subdom semi_factor_defl_bottom)

lemma is_semi_factor_top: "is_semi_factor top"
  by (simp add: is_semi_factor_def p_top_stable_subdom semi_factor_defl_ID)

text \<open>Semi-factors are closed under binary joins (Jung 4.1.9(i)) and meets (4.1.9(ii)).\<close>

lemma is_semi_factor_sup:
  "is_semi_factor a \<Longrightarrow> is_semi_factor b \<Longrightarrow> is_semi_factor (sup a b)"
  by (simp add: is_semi_factor_def p_sup semi_factor_defl_join)

lemma is_semi_factor_inf:
  "is_semi_factor a \<Longrightarrow> is_semi_factor b \<Longrightarrow> is_semi_factor (inf a b)"
  by (simp add: is_semi_factor_def p_inf semi_factor_defl_oo)

text \<open>\dots\ and hence, by induction, through finite suprema.\<close>
lemma finite_semi_factor_Sup:
  fixes \<A> :: "'a stable_subdom set"
  assumes "finite \<A>" and "\<And>A. A \<in> \<A> \<Longrightarrow> is_semi_factor A"
  shows "is_semi_factor (Sup \<A>)"
  using assms
proof (induction \<A> rule: finite_induct)
  case empty
  show ?case by (simp add: is_semi_factor_bot)
next
  case (insert A \<A>)
  from insert.prems have "is_semi_factor A" by blast
  moreover have "is_semi_factor (Sup \<A>)"
    by (rule insert.IH) (use insert.prems in blast)
  ultimately show ?case using is_semi_factor_sup
    by simp
qed

lemma directed_semi_factor_Sup:
  fixes \<A> :: "'a stable_subdom set"
  assumes directed: "\<And>X Y. X \<in> \<A> \<Longrightarrow> Y \<in> \<A> \<Longrightarrow> \<exists>Z \<in> \<A>. X \<le> Z \<and> Y \<le> Z"
    and nonempty: "\<A> \<noteq> {}"
    and sf: "\<And>A. A \<in> \<A> \<Longrightarrow> is_semi_factor A"
  shows "is_semi_factor (Sup \<A>)"
proof (rule is_semi_factorI)
  fix x y assume y: "y \<in> set_of_subdom (Sup \<A>)"
  assume px_below: "\<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x \<sqsubseteq> y"
  from directed_stable_proj_sup[OF directed nonempty]
  have p_lub: "(\<lambda>A. \<p>\<^bsub>A\<^esub>\<cdot>x) ` \<A> <<| \<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x" for x .
  let ?p = "\<p>\<^bsub>Sup \<A>\<^esub>"
  have xpAy: "x \<Up> \<p>\<^bsub>A\<^esub>\<cdot>y" if "A \<in> \<A>" for A
  proof -
    interpret A: semi_factor_defl "\<p>\<^bsub>A\<^esub>" using sf[OF that] by (simp add: is_semi_factor_def)
    from that have "\<p>\<^bsub>A\<^esub> \<sqsubseteq> ?p" by (intro p_below_of_le Sup_upper)
    then have "\<p>\<^bsub>A\<^esub>\<cdot>x = \<p>\<^bsub>A\<^esub>\<cdot>(?p\<cdot>x)"
      by (simp add: deflation_below_comp1[OF subdom.deflation_p subdom.deflation_p])
    also have "\<dots> \<sqsubseteq> \<p>\<^bsub>A\<^esub>\<cdot>y" using px_below by (rule monofun_cfun_arg)
    finally have "\<p>\<^bsub>A\<^esub>\<cdot>x \<sqsubseteq> \<p>\<^bsub>A\<^esub>\<cdot>y" .
    with subdom.idem show "x \<Up> \<p>\<^bsub>A\<^esub>\<cdot>y" by (rule A.slide)
  qed
  let ?W = "(\<lambda>A. x \<squnion> \<p>\<^bsub>A\<^esub>\<cdot>y) ` \<A>"
  have dirW: "directed ?W"
  proof (rule directedI)
    fix u v assume "u \<in> ?W" "v \<in> ?W"
    then obtain A B where A: "A \<in> \<A>" "u = x \<squnion> \<p>\<^bsub>A\<^esub>\<cdot>y"
      and B: "B \<in> \<A>" "v = x \<squnion> \<p>\<^bsub>B\<^esub>\<cdot>y" by blast
    from directed[OF A(1) B(1)] obtain C where C: "C \<in> \<A>" "A \<le> C" "B \<le> C" by blast
    from C(2) have AC: "\<p>\<^bsub>A\<^esub>\<cdot>y \<sqsubseteq> \<p>\<^bsub>C\<^esub>\<cdot>y"
      by (auto intro: p_below_of_le monofun_cfun_fun)
    from C(3) have BC: "\<p>\<^bsub>B\<^esub>\<cdot>y \<sqsubseteq> \<p>\<^bsub>C\<^esub>\<cdot>y"
      by (auto intro: p_below_of_le monofun_cfun_fun)
    have "u \<sqsubseteq> x \<squnion> \<p>\<^bsub>C\<^esub>\<cdot>y" unfolding A(2)
      by (rule join_mono2[OF xpAy[OF C(1)] AC])
    moreover have "v \<sqsubseteq> x \<squnion> \<p>\<^bsub>C\<^esub>\<cdot>y" unfolding B(2)
      by (rule join_mono2[OF xpAy[OF C(1)] BC])
    moreover have "x \<squnion> \<p>\<^bsub>C\<^esub>\<cdot>y \<in> ?W" using C(1) by blast
    ultimately show "\<exists>z\<in>?W. u \<sqsubseteq> z \<and> v \<sqsubseteq> z" by blast
  qed
  define w where "w = lub ?W"
  have Wlub: "?W <<| w" unfolding w_def using dirW by (rule directed_lub)
  from nonempty obtain A0 where A0: "A0 \<in> \<A>" by blast
  have memA0: "x \<squnion> \<p>\<^bsub>A0\<^esub>\<cdot>y \<in> ?W" using A0 by blast
  have "x \<sqsubseteq> x \<squnion> \<p>\<^bsub>A0\<^esub>\<cdot>y" by (rule joinableD(1)[OF xpAy[OF A0]])
  also have "\<dots> \<sqsubseteq> w" using is_ubD[OF is_lubD1[OF Wlub] memA0] .
  finally have xw: "x \<sqsubseteq> w" .
  have Py_y: "(\<lambda>A. \<p>\<^bsub>A\<^esub>\<cdot>y) ` \<A> <<| y"
    using p_lub[of y] y by (simp add: p_fixes[symmetric])
  have Py_w: "(\<lambda>A. \<p>\<^bsub>A\<^esub>\<cdot>y) ` \<A> <| w"
  proof (rule ub_imageI)
    fix A assume A: "A \<in> \<A>"
    have memA: "x \<squnion> \<p>\<^bsub>A\<^esub>\<cdot>y \<in> ?W" using A by blast
    have "\<p>\<^bsub>A\<^esub>\<cdot>y \<sqsubseteq> x \<squnion>  \<p>\<^bsub>A\<^esub>\<cdot>y" by (rule joinableD(2)[OF xpAy[OF A]])
    also have "\<dots> \<sqsubseteq> w" using is_ubD[OF is_lubD1[OF Wlub] memA] .
    finally show "\<p>\<^bsub>A\<^esub>\<cdot>y \<sqsubseteq> w" .
  qed
  have yw: "y \<sqsubseteq> w" using Py_y Py_w by (rule is_lubD2)
  show "x \<Up> y" using xw yw by (rule joinableI)
qed

lemma Fpow_singleton: "x \<in> A \<Longrightarrow> {x} \<in> Fpow A"
  by (simp add: Fpow_def)

lemma (in complete_lattice) Sup_of_Fpow: "Sup (Sup ` Fpow(\<A>)) = Sup \<A>"
proof (rule order_antisym)
  show "Sup \<A> \<le> Sup (Sup ` Fpow \<A>)"
    by (rule Sup_least, rule Sup_upper, drule Fpow_singleton, force)
  show "Sup (Sup ` Fpow \<A>) \<le> Sup \<A>"
    by (rule Sup_least, erule imageE, auto simp add: Sup_subset_mono Fpow_def )
qed

lemma is_semi_factor_Sup:
  fixes \<A> :: "'a stable_subdom set"
  assumes sf: "\<And>A. A \<in> \<A> \<Longrightarrow> is_semi_factor A"
  shows "is_semi_factor (Sup \<A>)"
proof -
  have directed: "X \<in> Sup ` Fpow(\<A>) \<Longrightarrow> Y \<in> Sup ` Fpow(\<A>) \<Longrightarrow> \<exists>Z \<in> Sup ` Fpow(\<A>). X \<le> Z \<and> Y \<le> Z"
    for X Y
  proof (simp, safe, intro bexI)
    fix x y :: "'a stable_subdom set"
    show "Sup x \<le> Sup (x \<union> y) \<and> Sup y \<le> Sup (x \<union> y)"
      by (simp add: Sup_subset_mono)
    assume "x \<in> Fpow(\<A>)" "y \<in> Fpow(\<A>)"
    then show "x \<union> y \<in> Fpow(\<A>)" by (simp add: Fpow_def)
  qed
  moreover have "Sup ` Fpow(\<A>) \<noteq> {}" by (simp add: Fpow_not_empty)
  moreover have "B \<in> Sup ` Fpow(\<A>) \<Longrightarrow> is_semi_factor (B)" for B
    using finite_semi_factor_Sup sf unfolding Fpow_def by auto
  ultimately have "is_semi_factor (Sup (Sup ` Fpow(\<A>)))"
    by (rule directed_semi_factor_Sup)
  then show ?thesis by (simp add: Sup_of_Fpow)
qed

subsection \<open>Meets, distributivity and the frame law\<close>

lemma p_inf_meet: "\<p>\<^bsub>inf A B\<^esub>\<cdot>x = \<p>\<^bsub>A\<^esub>\<cdot>x \<sqinter> \<p>\<^bsub>B\<^esub>\<cdot>x"
  unfolding meet_def p_inf
  by (simp add: glb_eqI[OF stable_defl_oo_glb[OF stable_defl_stable_subdom_p
          stable_defl_stable_subdom_p]])

lemma p_joinable[simp]: "\<p>\<^bsub>A\<^esub>\<cdot>x \<Up> \<p>\<^bsub>B\<^esub>\<cdot>x"
  by (rule joinableI; rule subdom.below)

instance stable_subdom :: ("{bifinite,distributive_cpo}") distrib_lattice
  by (intro_classes, intro stable_subdom_proj_eqI cfun_eqI)
    (simp add: p_inf_meet p_sup_join join_meet_distrib)

text \<open>Composition of projections is the projection onto the meet, and commutative.\<close>

lemma p_comp_inf: "\<p>\<^bsub>b\<^esub>\<cdot>(\<p>\<^bsub>a\<^esub>\<cdot>x) = \<p>\<^bsub>inf a b\<^esub>\<cdot>x"
  using p_inf_meet[of b a x] p_inf_meet[of a b x] by (simp add: p_inf meet_sym)

lemma p_app_commute: "\<p>\<^bsub>a\<^esub>\<cdot>(\<p>\<^bsub>b\<^esub>\<cdot>x) = \<p>\<^bsub>b\<^esub>\<cdot>(\<p>\<^bsub>a\<^esub>\<cdot>x)"
  by (simp add: p_comp_inf inf_commute)

lemma p_comp_inf2:  "\<p>\<^bsub>a\<^esub>\<cdot>(\<p>\<^bsub>b\<^esub>\<cdot>x) = \<p>\<^bsub>inf a b\<^esub>\<cdot>x"
  by (simp add: p_comp_inf inf_commute)

lemma (in stable_subdomain) join_closed:
  "a \<Up> b \<Longrightarrow> a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> a \<squnion> b \<in> S"
  using lub_closed[OF _ joinable_lub]
  by fast


text \<open>The projection of a finite (nonempty) sup is the lub of the pointwise projections.\<close>
lemma finite_proj_sup:
  fixes \<A> :: "'a stable_subdom set"
  assumes "finite \<A>" and "\<A> \<noteq> {}"
  shows "(\<lambda>A. \<p>\<^bsub>A\<^esub>\<cdot>x) ` \<A> <<| \<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x"
  using assms
proof (induction rule: finite_ne_induct)
  case (singleton A)
  have "{\<p>\<^bsub>A\<^esub>\<cdot>x} <<| \<p>\<^bsub>A\<^esub>\<cdot>x" by (rule is_lub_singleton)
  then show ?case by simp
next
  case (insert A \<A>)
  have j: "\<p>\<^bsub>A\<^esub>\<cdot>x \<Up> \<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x" by (rule joinableI[OF subdom.p_below subdom.p_below])
  have "insert (\<p>\<^bsub>A\<^esub>\<cdot>x) ((\<lambda>B. \<p>\<^bsub>B\<^esub>\<cdot>x) ` \<A>) <<| \<p>\<^bsub>A\<^esub>\<cdot>x \<squnion> \<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x"
    by (rule insert_join_is_lub[OF insert.IH j])
  moreover have "(\<lambda>B. \<p>\<^bsub>B\<^esub>\<cdot>x) ` insert A \<A> = insert (\<p>\<^bsub>A\<^esub>\<cdot>x) ((\<lambda>B. \<p>\<^bsub>B\<^esub>\<cdot>x) ` \<A>)" by simp
  moreover have "\<p>\<^bsub>A\<^esub>\<cdot>x \<squnion> \<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x = \<p>\<^bsub>Sup (insert A \<A>)\<^esub>\<cdot>x"
    by (simp add: p_sup_join)
  ultimately show ?case by simp
qed

text \<open>The projection of an \emph{arbitrary} sup is the lub of the pointwise projections
  (Jung's full \<open>p\<^bsub>\<Squnion>\<A>\<^esub>\<cdot>x = \<Squnion>\<^bsub>A\<in>\<A>\<^esub> p\<^bsub>A\<^esub>\<cdot>x\<close>, in @{text "<<|"} form): combine the
  directed result over @{term "Sup ` Fpow \<A>"} (whose sup is @{term "Sup \<A>"}) with the
  finite case.  An upper bound of the pointwise projections bounds every finite sub-join,
  hence the directed lub, hence @{term "\<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x"}.\<close>
lemma proj_Sup:
  fixes \<A> :: "'a stable_subdom set"
  shows "(\<lambda>A. \<p>\<^bsub>A\<^esub>\<cdot>x) ` \<A> <<| \<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x"
proof -
  have dir: "X \<in> Sup ` Fpow \<A> \<Longrightarrow> Y \<in> Sup ` Fpow \<A> \<Longrightarrow> \<exists>Z \<in> Sup ` Fpow \<A>. X \<le> Z \<and> Y \<le> Z"
    for X Y
  proof (simp, safe, intro bexI)
    fix x y :: "'a stable_subdom set"
    show "Sup x \<le> Sup (x \<union> y) \<and> Sup y \<le> Sup (x \<union> y)" by (simp add: Sup_subset_mono)
    assume "x \<in> Fpow \<A>" "y \<in> Fpow \<A>"
    then show "x \<union> y \<in> Fpow \<A>" by (simp add: Fpow_def)
  qed
  have neF: "Sup ` Fpow \<A> \<noteq> {}" by (simp add: Fpow_not_empty)
  have D: "(\<lambda>F. \<p>\<^bsub>F\<^esub>\<cdot>x) ` (Sup ` Fpow \<A>) <<| \<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x"
    using directed_stable_proj_sup[OF dir neF] by (simp add: Sup_of_Fpow)
  show ?thesis
  proof (rule is_lubI)
    show "(\<lambda>A. \<p>\<^bsub>A\<^esub>\<cdot>x) ` \<A> <| \<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x"
    proof (rule ub_imageI)
      fix A assume "A \<in> \<A>"
      then have "\<p>\<^bsub>A\<^esub> \<sqsubseteq> \<p>\<^bsub>Sup \<A>\<^esub>" by (intro p_below_of_le Sup_upper)
      then show "\<p>\<^bsub>A\<^esub>\<cdot>x \<sqsubseteq> \<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x" by (rule monofun_cfun_fun)
    qed
  next
    fix u assume u: "(\<lambda>A. \<p>\<^bsub>A\<^esub>\<cdot>x) ` \<A> <| u"
    have "(\<lambda>F. \<p>\<^bsub>F\<^esub>\<cdot>x) ` (Sup ` Fpow \<A>) <| u"
    proof (rule ub_imageI)
      fix F assume "F \<in> Sup ` Fpow \<A>"
      then obtain G where G: "G \<in> Fpow \<A>" and F: "F = Sup G" by auto
      from G have finG: "finite G" and GA: "G \<subseteq> \<A>" by (auto simp: Fpow_def)
      show "\<p>\<^bsub>F\<^esub>\<cdot>x \<sqsubseteq> u"
      proof (cases "G = {}")
        case True
        with F show ?thesis by (simp add: p_bot_stable_subdom)
      next
        case False
        have lub: "(\<lambda>A. \<p>\<^bsub>A\<^esub>\<cdot>x) ` G <<| \<p>\<^bsub>Sup G\<^esub>\<cdot>x" using finG False by (rule finite_proj_sup)
        have "(\<lambda>A. \<p>\<^bsub>A\<^esub>\<cdot>x) ` G <| u"
        proof (rule ub_imageI)
          fix A assume "A \<in> G"
          with GA have "\<p>\<^bsub>A\<^esub>\<cdot>x \<in> (\<lambda>A. \<p>\<^bsub>A\<^esub>\<cdot>x) ` \<A>" by auto
          with u show "\<p>\<^bsub>A\<^esub>\<cdot>x \<sqsubseteq> u" by (rule is_ubD)
        qed
        with lub have "\<p>\<^bsub>Sup G\<^esub>\<cdot>x \<sqsubseteq> u" by (rule is_lubD2)
        with F show ?thesis by simp
      qed
    qed
    with D show "\<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x \<sqsubseteq> u" by (rule is_lubD2)
  qed
qed

text \<open>The frame law: binary meet distributes over arbitrary joins.  The image \<open>y\<close> of \<open>x\<close> under
  \<open>A \<sqinter> \<Squnion>\<B>\<close> is the lub of its projections through the members of \<open>\<B>\<close>
  (@{thm [source] proj_Sup}), and each of those is fixed by \<open>A \<sqinter> B\<close>, hence by the right-hand side.\<close>

lemma inf_Sup_stable_subdom:
  fixes A :: "'a stable_subdom"
  shows "inf A (Sup \<B>) = (SUP B\<in>\<B>. inf A B)"
proof (rule order.antisym)
  show "(SUP B\<in>\<B>. inf A B) \<le> inf A (Sup \<B>)"
    by (rule SUP_least) (auto intro: inf_mono Sup_upper le_infI2)
  let ?C = "SUP B\<in>\<B>. inf A B"
  show "inf A (Sup \<B>) \<le> ?C"
  proof (rule le_of_p_below, rule cfun_belowI)
    fix x
    let ?y = "\<p>\<^bsub>inf A (Sup \<B>)\<^esub>\<cdot>x"
    have "?y \<in> set_of_subdom (inf A (Sup \<B>))" by (rule subdom.p_in_S)
    then have yA: "?y \<in> set_of_subdom A" and yS: "?y \<in> set_of_subdom (Sup \<B>)"
      by (simp_all add: set_of_subdom_inf)
    have lub: "(\<lambda>B. \<p>\<^bsub>B\<^esub>\<cdot>?y) ` \<B> <<| ?y"
      using proj_Sup[where \<A> = \<B> and x = ?y] yS by (simp add: p_fixes[symmetric])
    have "(\<lambda>B. \<p>\<^bsub>B\<^esub>\<cdot>?y) ` \<B> <| \<p>\<^bsub>?C\<^esub>\<cdot>?y"
    proof (rule ub_imageI)
      fix B assume B: "B \<in> \<B>"
      have zS: "\<p>\<^bsub>B\<^esub>\<cdot>?y \<in> set_of_subdom (inf A B)"
        using subdom.downward[OF yA subdom.p_below] subdom.p_in_S by (simp add: set_of_subdom_inf)
      moreover have le: "inf A B \<le> ?C" using B by (rule SUP_upper)
      ultimately have "\<p>\<^bsub>?C\<^esub>\<cdot>(\<p>\<^bsub>B\<^esub>\<cdot>?y) = \<p>\<^bsub>B\<^esub>\<cdot>?y"
      proof -
        have "\<p>\<^bsub>B\<^esub>\<cdot>?y = \<p>\<^bsub>inf A B\<^esub>\<cdot>(\<p>\<^bsub>B\<^esub>\<cdot>?y)" using zS by (simp add: p_fixes[symmetric])
        also have "\<dots> \<sqsubseteq> \<p>\<^bsub>?C\<^esub>\<cdot>(\<p>\<^bsub>B\<^esub>\<cdot>?y)" using le by (intro monofun_cfun_fun p_below_of_le)
        finally show ?thesis by (rule below_antisym[OF subdom.p_below])
      qed
      moreover have "\<p>\<^bsub>?C\<^esub>\<cdot>(\<p>\<^bsub>B\<^esub>\<cdot>?y) \<sqsubseteq> \<p>\<^bsub>?C\<^esub>\<cdot>?y" by (rule monofun_cfun_arg, rule subdom.p_below)
      ultimately show "\<p>\<^bsub>B\<^esub>\<cdot>?y \<sqsubseteq> \<p>\<^bsub>?C\<^esub>\<cdot>?y" by simp
    qed
    with lub have "?y \<sqsubseteq> \<p>\<^bsub>?C\<^esub>\<cdot>?y" by (rule is_lubD2)
    also have "\<dots> \<sqsubseteq> \<p>\<^bsub>?C\<^esub>\<cdot>x" by (rule monofun_cfun_arg, rule subdom.p_below)
    finally show "?y \<sqsubseteq> \<p>\<^bsub>?C\<^esub>\<cdot>x" .
  qed
qed

lemma Sup_contains_top: "top \<in> (X::'a::complete_lattice set) \<Longrightarrow> Sup X = top"
  by (rule order.antisym) (auto intro: Sup_upper)

section \<open>The type of semi-factors\<close>

text \<open>Following Jung, the semi-factors (stable subdomains satisfying the slide condition) form a
  complete lattice.  Sups, binary meets, top and bottom are inherited from the type
  \<open>'a stable_subdom\<close> (the semi-factors are closed under those operations), but an arbitrary
  intersection of semi-factors need not be one.  The meet of a family is therefore recovered
  as the sup of its semi-factor lower bounds.\<close>

text \<open>Semi-factors are closed under arbitrary sups, in particular under lubs of chains: they form
  a sub-pcpo of the stable subdomains.\<close>

pcpodef 'a semi_factor = "{A :: 'a stable_subdom. is_semi_factor A}"
  morphisms subdom_of_semi_factor semi_factor_of_subdom
proof -
  have b: "bot = (\<bottom> :: 'a stable_subdom)" by (rule bottomI) (simp add: below_stable_subdom_iff_le)
  show "\<bottom> \<in> {A :: 'a stable_subdom. is_semi_factor A}" using is_semi_factor_bot by (simp add: b[symmetric])
next
  show "adm (\<lambda>A. A \<in> {A :: 'a stable_subdom. is_semi_factor A})"
  proof (rule admI, simp)
    fix Y :: "nat \<Rightarrow> 'a stable_subdom" assume Y: "chain Y" "\<forall>i. is_semi_factor (Y i)"
    have "(\<Squnion>i. Y i) = Sup (range Y)" by (rule lub_eqI) (rule stable_subdom_is_lub)
    then show "is_semi_factor (\<Squnion>i. Y i)" using Y(2) by (auto intro: is_semi_factor_Sup)
  qed
qed

setup_lifting type_definition_semi_factor

lemma is_semi_factor_subdom_of_semi_factor: "is_semi_factor (subdom_of_semi_factor F)"
  using subdom_of_semi_factor by blast

instantiation semi_factor :: ("{bifinite,distributive_cpo}") complete_lattice
begin

lift_definition less_eq_semi_factor :: "'a semi_factor \<Rightarrow> 'a semi_factor \<Rightarrow> bool"
  is "(\<le>)" .

lift_definition less_semi_factor :: "'a semi_factor \<Rightarrow> 'a semi_factor \<Rightarrow> bool"
  is "(<)" .

lift_definition inf_semi_factor :: "'a semi_factor \<Rightarrow> 'a semi_factor \<Rightarrow> 'a semi_factor"
  is "inf" by (rule is_semi_factor_inf)

lift_definition sup_semi_factor :: "'a semi_factor \<Rightarrow> 'a semi_factor \<Rightarrow> 'a semi_factor"
  is "sup" by (rule is_semi_factor_sup)

lift_definition top_semi_factor :: "'a semi_factor"
  is "top" by (rule is_semi_factor_top)

lift_definition bot_semi_factor :: "'a semi_factor"
  is "bot" by (rule is_semi_factor_bot)

lift_definition Sup_semi_factor :: "'a semi_factor set \<Rightarrow> 'a semi_factor"
  is "Sup" by (rule is_semi_factor_Sup)

text \<open>Arbitrary meet = sup of the semi-factor lower bounds.\<close>
lift_definition Inf_semi_factor :: "'a semi_factor set \<Rightarrow> 'a semi_factor"
  is "\<lambda>\<S>. Sup {b. (\<forall>a\<in>\<S>. b \<le> a) \<and> is_semi_factor b}"
  by (auto intro: is_semi_factor_Sup)

instance
  by (standard; transfer) (auto intro: Sup_least Sup_upper is_semi_factor_top Sup_contains_top)

end

instance semi_factor ::  ("{bifinite,distributive_cpo}") distrib_lattice
  by (intro_classes, transfer', rule sup_inf_distrib1)

text \<open>As for stable subdomains, the domain order is the lattice order.\<close>

lemma below_semi_factor_iff_le: "F \<sqsubseteq> G \<longleftrightarrow> F \<le> G" for F G :: "'a semi_factor"
  by (simp add: below_semi_factor_def less_eq_semi_factor.rep_eq below_stable_subdom_iff_le)

lemma semi_factor_is_lub: "\<A> <<| Sup \<A>" for \<A> :: "'a semi_factor set"
  by (auto intro!: is_lubI is_ubI Sup_upper Sup_least
      simp: below_semi_factor_iff_le is_ub_def)

instance semi_factor :: ("{bifinite,distributive_cpo}") bounded_complete
  by standard (blast intro: semi_factor_is_lub)

instance semi_factor :: ("{bifinite,distributive_cpo}") lattice_complete
  by intro_classes (rule exI[of _ top], simp add: below_semi_factor_iff_le)

lemma join_semi_factor: "F \<squnion> G = sup F G" for F G :: "'a semi_factor"
  unfolding join_def by (rule lub_eqI) (simp add: semi_factor_is_lub[of "{F, G}", simplified])

lemma meet_semi_factor: "F \<sqinter> G = inf F G" for F G :: "'a semi_factor"
  unfolding meet_def by (rule glb_eqI) (simp add: is_glb_def below_semi_factor_iff_le)

instance semi_factor :: ("{bifinite,distributive_cpo}") distributive_cpo
  by intro_classes (simp add: join_semi_factor meet_semi_factor inf_sup_distrib1)

lift_definition semi_factor_p :: "'a semi_factor \<Rightarrow> 'a \<rightarrow> 'a"
is "stable_subdom_p" .

lift_definition set_of_semi_factor :: "'a semi_factor \<Rightarrow> 'a set"
is "set_of_subdom" .

interpretation semi_factor: semi_factor_subdomain "set_of_semi_factor A"
  rewrites semi_factor_p_eq: "stable_subdomain.p (set_of_semi_factor A) \<equiv> semi_factor_p A"
proof -
  show "semi_factor_subdomain (set_of_semi_factor A)"
    by transfer (simp add: is_semi_factor_iff_subdomain)
  show "stable_subdomain.p (set_of_semi_factor A) \<equiv> semi_factor_p A"
    unfolding set_of_semi_factor.rep_eq semi_factor_p.rep_eq
    by (rule eq_reflection, rule p_set_of_subdom)
qed

lemma semi_factor_defl_semi_factor_p: "semi_factor_defl (semi_factor_p F)"
  using is_semi_factor_subdom_of_semi_factor[of F]
  by (simp add: is_semi_factor_def semi_factor_p.rep_eq)

text \<open>Morally semi-factors are deflations; @{const semi_factor_p} is the representation and
  \<open>semi_factor_of_defl\<close> the abstraction.\<close>

definition semi_factor_of_defl :: "('a \<rightarrow> 'a) \<Rightarrow> 'a semi_factor"
  where "semi_factor_of_defl d = semi_factor_of_subdom (subdom_of_defl d)"

lemma semi_factor_p_of_defl:
  assumes d: "semi_factor_defl d"
  shows "semi_factor_p (semi_factor_of_defl d) = d"
proof -
  have st: "stable_defl d" by (rule semi_factor_defl.axioms(1)[OF d])
  have "is_semi_factor (subdom_of_defl d)"
    by (simp add: is_semi_factor_def stable_subdom_p_subdom_of_defl[OF st] d)
  then show ?thesis
    by (simp add: semi_factor_of_defl_def semi_factor_p.rep_eq semi_factor_of_subdom_inverse
        stable_subdom_p_subdom_of_defl[OF st])
qed

lemma semi_factor_below_iff_p: "F \<sqsubseteq> G \<longleftrightarrow> semi_factor_p F \<sqsubseteq> semi_factor_p G"
  by (simp add: below_semi_factor_def stable_subdom_below_iff semi_factor_p.rep_eq)

text \<open>The bottom semi-factor projects to \<open>\<bottom>\<close>, the top one is the identity, and joins
  project to joins.\<close>

lemma semi_factor_bot_bottom: "(bot :: 'a semi_factor) = \<bottom>"
  by (rule bottomI) (simp add: below_semi_factor_iff_le)

lemma semi_factor_top_lattice_top: "(top :: 'a semi_factor) = lattice_top"
  by (rule below_antisym) (rule below_lattice_top, simp add: below_semi_factor_iff_le)

lemma semi_factor_p_bot: "semi_factor_p \<bottom> = \<bottom>"
  by (rule cfun_eqI) (simp add: semi_factor_bot_bottom[symmetric] semi_factor_p.rep_eq
      bot_semi_factor.rep_eq p_bot_stable_subdom)

lemma semi_factor_p_top: "semi_factor_p lattice_top = ID"
  by (simp add: semi_factor_top_lattice_top[symmetric] semi_factor_p.rep_eq top_semi_factor.rep_eq
      p_top_stable_subdom)

lemma semi_factor_p_sup: "semi_factor_p (F \<squnion> G)\<cdot>x = semi_factor_p F\<cdot>x \<squnion> semi_factor_p G\<cdot>x"
  by (simp add: join_semi_factor semi_factor_p.rep_eq sup_semi_factor.rep_eq p_sup_join)

lemma semi_factor_p_inject: "semi_factor_p F = semi_factor_p G \<longleftrightarrow> F = G"
  by transfer (auto intro: stable_subdom_proj_eqI)

lemma semi_factor_of_defl_p [simp]: "semi_factor_of_defl (semi_factor_p F) = F"
  by (rule semi_factor_p_inject[THEN iffD1])
    (simp add: semi_factor_p_of_defl semi_factor_defl_semi_factor_p)

abbreviation semi_factor_proj (infixl \<open>\<downharpoonright>\<close> 200)
  where "semi_factor_proj x a \<equiv> semi_factor_p a\<cdot>x"

lemma semi_factor_proj_comp:
  "x \<downharpoonright> a \<downharpoonright> b = x \<downharpoonright> (a \<sqinter> b)"
  unfolding meet_semi_factor by (transfer', rule p_comp_inf)

lemma semi_factor_proj_comm:
  "x \<downharpoonright> a \<downharpoonright> b = x \<downharpoonright> b \<downharpoonright> a"
  by (simp add: semi_factor_proj_comp lattice_meet_commute)

corollary semi_factor_comp_simp[simp]:
  "a \<sqsubseteq> b \<Longrightarrow> x \<downharpoonright> a \<downharpoonright> b = x \<downharpoonright> a"
  "a \<sqsubseteq> b \<Longrightarrow> x \<downharpoonright> b \<downharpoonright> a = x \<downharpoonright> a"
  by (simp_all add: semi_factor_proj_comp lattice_meet_absorb1 lattice_meet_absorb2)

end
