theory Bounded_Complete imports HOLCF Top Definitions FiniteCF Directed begin

default_sort po

class bounded_complete = pcpo +
  assumes ex_bound_ne_ex_lub: "A \<noteq> {} \<Longrightarrow> A <| b \<Longrightarrow> \<exists>a. A <<| a"
begin

lemma ex_bound_ex_lub: "A <| b \<Longrightarrow> \<exists>a. A <<| a"
  by (cases "A = {}") (auto intro: ex_bound_ne_ex_lub lub_empty)

lemma ex_bound_lub: "A <| b \<Longrightarrow> A <<| lub A"
  using ex_bound_ex_lub[THEN exE] is_lub_lub by blast

lemma join_is_lub: "x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> {x, y} <<| x \<squnion> y"
  using ex_bound_lub[of "{x, y}" z] by (simp add: join_def)

lemma join_belowI: "x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<squnion> y \<sqsubseteq> z"
  using join_is_lub[THEN lub_below_iff']
  by simp

lemma lub_belowI: "A \<noteq> {} \<Longrightarrow> A <| b \<Longrightarrow> lub A \<sqsubseteq> b"
  using ex_bound_lub[THEN is_lubD2]
  by simp

lemma below_lubI: "A <| b \<Longrightarrow> x \<in> A \<Longrightarrow> x \<sqsubseteq> lub A"
  using ex_bound_lub[THEN is_lubD1, THEN is_ubD] .

lemma is_glb: fixes S :: "'a set" assumes "S \<noteq> {}"
  obtains s where "is_glb S s"
proof -
  from assms obtain y where "y \<in> S" by blast
  define B where "B \<equiv> {x. \<forall>y \<in> S. x \<sqsubseteq> y}"
  have "\<bottom> \<in> B" unfolding B_def by simp
  then have 1: "B \<noteq> {}" by auto
  from \<open>y \<in> S\<close> have 2: "B <| y" by (simp add: B_def is_ub_def)
  from 1 2 obtain s where s: "B <<| s" using ex_bound_ex_lub by auto
  have sinB: "s \<sqsubseteq> y" if "y \<in> S" for y
  proof -
    from that have "B <| y" by (simp add: B_def is_ub_def)
    with s show ?thesis by (rule is_lubD2)
  qed
  have "x \<sqsubseteq> s \<longleftrightarrow> (\<forall>y \<in> S. x \<sqsubseteq> y)" for x
  proof
    show "x \<sqsubseteq> s \<Longrightarrow> (\<forall>y \<in> S. x \<sqsubseteq> y)"
      using below_trans[of x s, OF _ sinB] by blast
    show "(\<forall>y \<in> S. x \<sqsubseteq> y) \<Longrightarrow> x \<sqsubseteq> s"
      using s[THEN is_lubD1, THEN is_ubD, unfolded B_def]
      by simp
  qed
  with \<open>S \<noteq> {}\<close> have "is_glb S s" unfolding is_glb_def by simp
  then show ?thesis by (rule that)
qed

lemma glb: fixes S :: "'a set"
  assumes "S \<noteq> {}"
  shows "is_glb S (glb S)"
  using is_glb[OF assms] by (blast intro: is_glb_glb)

lemma glb_below: "x \<in> S \<Longrightarrow> glb S \<sqsubseteq> x"
  by (auto intro: glb is_glb_below)

lemma glb_greatest: "S \<noteq> {} \<Longrightarrow> (\<forall>x \<in> S. b \<sqsubseteq> x) \<Longrightarrow> b \<sqsubseteq> glb S"
  by (auto intro: glb is_glb_greatest)

lemma glb_below_iff: "S \<noteq> {} \<Longrightarrow> (b \<sqsubseteq> glb S) = (\<forall>x \<in> S. b \<sqsubseteq> x)"
  by (drule glb) (simp add: is_glb_def)

lemma glb_eq_lub:
  assumes "S \<noteq> {}"
  shows "glb S = lub {x. \<forall>y \<in> S. x \<sqsubseteq> y}" (is "_ = lub ?B")
proof (rule glb_eqI, rule is_glbI)
  obtain y where "y \<in> S" using assms by blast
  then have "?B <| y" by (simp add: is_ub_def)
  then have B: "?B <<| lub ?B" by (rule ex_bound_lub)
  show "lub ?B \<sqsubseteq> x" if "x \<in> S" for x
    by (rule is_lubD2[OF B]) (simp add: is_ub_def that)
  show "b \<sqsubseteq> lub ?B" if "\<forall>x \<in> S. b \<sqsubseteq> x" for b
    by (rule is_ubD[OF is_lubD1[OF B]]) (simp add: that)
qed

lemma meet_below1: "a \<sqinter> b \<sqsubseteq> a" and meet_below2: "a \<sqinter> b \<sqsubseteq> b"
  unfolding meet_def
  by (fast intro: glb_below)+

lemma meet_below_iff: "c \<sqsubseteq> a \<sqinter> b \<longleftrightarrow> c \<sqsubseteq> a \<and> c \<sqsubseteq> b"
  unfolding meet_def
  by (auto simp add: glb_below_iff)

lemma meet_greatest: "c \<sqsubseteq> a \<Longrightarrow> c \<sqsubseteq> b \<Longrightarrow> c \<sqsubseteq> a \<sqinter> b"
  by (auto simp add: meet_below_iff)

lemma meet_sym: "a \<sqinter> b = b \<sqinter> a"
  unfolding meet_def
  by (simp only: insert_commute)

definition joinable (infix "\<Up>" 50)
  where "a \<Up> b \<equiv> \<exists>z. a \<sqsubseteq> z \<and> b \<sqsubseteq> z"

lemma joinable_lub: "a \<Up> b \<Longrightarrow> {a, b} <<| a \<squnion> b"
  unfolding joinable_def
  by (fast intro: join_is_lub)

lemma joinableI: "a \<sqsubseteq> c \<Longrightarrow> b \<sqsubseteq> c \<Longrightarrow> a \<Up> b"
  unfolding joinable_def
  by fast

lemma joinableD: "a \<Up> b \<Longrightarrow> a \<sqsubseteq> a \<squnion> b" "a \<Up> b \<Longrightarrow> b \<sqsubseteq> a \<squnion> b"
  using joinable_lub
  by (auto dest: is_lubD1 is_ubD)

lemma joinable_mono1: "a \<Up> b \<Longrightarrow> c \<sqsubseteq> a \<Longrightarrow> c \<Up> b"
  apply (frule joinableD(1), drule joinableD(2))
  apply (rule joinableI[of c "a \<squnion> b" b])
   apply (rule below_trans[of c a])
  .

lemma joinable_refl[simp]: "a \<Up> a"
  unfolding joinable_def join_def by fast

lemma joinable_sym: "a \<Up> b \<longleftrightarrow> b \<Up> a"
  unfolding joinable_def
  by fast

lemma joinable_mono2: "a \<Up> b \<Longrightarrow> c \<sqsubseteq> b \<Longrightarrow> a \<Up> c"
  using joinable_mono1 joinable_sym by metis

text \<open>A fact rather than a \<open>sublocale\<close>, for the same reason as @{thm [source] below_order}.\<close>

lemma semilattice_meet: "class.semilattice_inf meet below below_strict"
  by (rule class.semilattice_inf.intro[OF below_order])
    (unfold_locales, (fact meet_below1 meet_below2 meet_greatest)+)

lemma join_mono1: "c \<squnion> b \<sqsubseteq> a \<squnion> b" if "a \<Up> b" "c \<sqsubseteq> a"
proof -
  from that have "c \<sqsubseteq> a \<squnion> b" by (blast intro: below_trans joinableD(1))
  also from that have "b \<sqsubseteq> a \<squnion> b" by (blast intro: joinableD(2))
  finally(join_belowI) show ?thesis.
qed

lemma join_mono2: "a \<squnion> c \<sqsubseteq> a \<squnion> b" if "a \<Up> b" "c \<sqsubseteq> b"
  by (metis join_mono1 join_sym joinable_sym that)

lemma join_absorbI: "a \<sqsubseteq> b \<Longrightarrow> a \<squnion> b = b"
  by (meson below_antisym below_refl join_belowI joinableD(2) joinableI)

lemma joinable_if_below1[simp]: "a \<sqsubseteq> b \<Longrightarrow> a \<Up> b"
  by (auto intro: joinableI)

lemma joinable_if_below2[simp]: "a \<sqsubseteq> b \<Longrightarrow> b \<Up> a"
  by (auto intro: joinableI)

corollary join_absorb_meet[simp]: "(a \<sqinter> b) \<squnion> b = b"
  by (auto intro: join_absorbI meet_below2)

corollary join_absorb_meet2[simp]: "a \<squnion> (a \<sqinter> b) = a"
  using join_absorb_meet join_sym meet_sym by metis

corollary join_absorb_meet3[simp]: "(b \<sqinter> a) \<squnion> b = b"
  by (simp add: meet_sym)

corollary join_absorb_meet4[simp]: "a \<squnion> (b \<sqinter> a) = a"
  by (simp add: meet_sym)

lemma meet_absorbI: "a \<sqsubseteq> b \<Longrightarrow> a \<sqinter> b = a"
  by (rule semilattice_inf.inf_absorb1[OF semilattice_meet])

corollary meet_absorb_join[simp]: "a \<Up> b \<Longrightarrow> (a \<squnion> b) \<sqinter> a = a"
  using meet_absorbI[OF joinableD(1)] by (simp add: meet_sym)

lemma join_assoc: assumes "a \<Up> b" "b \<Up> c" "a \<squnion> b \<Up> c" "a \<Up> b \<squnion> c"
  shows "(a \<squnion> b) \<squnion> c = a \<squnion> (b \<squnion> c)"
  by (intro below_antisym join_belowI joinableD assms)
   (metis join_belowI joinableD assms below_trans)+

lemma joinable_simps[simp]:
  assumes "a \<Up> b"
  shows
  "a \<Up> a \<squnion> b" "a \<squnion> b \<Up> a"
  "b \<Up> a \<squnion> b" "a \<squnion> b \<Up> b"
  "a \<Up> b \<sqinter> d" "a \<sqinter> c \<Up> b"
  "a \<sqinter> c \<Up> b \<sqinter> d"
proof -
  from assms show "a \<sqinter> c \<Up> b" by (auto intro: joinable_mono1 meet_below1)
  then show "a \<sqinter> c \<Up> b \<sqinter> d" by (auto intro: joinable_mono2 meet_below1)
  from assms show "a \<Up> b \<sqinter> d" by (auto intro: joinable_mono2 meet_below1)
qed (auto intro: joinable_mono1 joinable_mono2 joinableD[OF assms] joinableI)

end

lemmas bounded_complete_locale_eqs [class_locale_eqs] =
  bounded_complete_class.joinable_dict[symmetric]

lemma bounded_complete_finite_joinI:
  assumes "\<And>a b c::'a::dcpo. \<lbrakk> a \<sqsubseteq> c; b \<sqsubseteq> c \<rbrakk> \<Longrightarrow> \<exists>z. {a, b} <<| z"
  shows "OFCLASS('a, bounded_complete_class)"
proof
  from assms have joinI: "a \<sqsubseteq> c \<Longrightarrow> b \<sqsubseteq> c \<Longrightarrow> {a, b} <<| a \<squnion> b" for a b c :: 'a
    unfolding join_def using is_lub_lub by blast
  have "B <| z \<Longrightarrow> \<exists>b. B <<| b" if "finite B"
    for z and B :: "'a set"
    using that(1)
  proof (induction B rule: finite_induct)
    case empty
    then show ?case by (blast intro: lub_empty)
  next
    case (insert x F)
    from insert.prems have prev: "F <| z" and x: "x \<sqsubseteq> z" by simp_all
    from insert.IH[OF prev] obtain w where w: "F <<| w" ..
    from w prev have "w \<sqsubseteq> z" by (rule is_lubD2)
    with x have pairlub: "{x, w} <<| x \<squnion> w" by (rule joinI)
    from is_lubD1[OF this] have belows: "x \<sqsubseteq> x \<squnion> w" "w \<sqsubseteq> x \<squnion> w" 
      by simp_all
    have "(insert x F) <<| x \<squnion> w"
    proof (rule is_lubI)
      show "insert x F <| x \<squnion> w" unfolding is_ub_insert
        using is_lubD1 pairlub w is_ub_upward belows by blast
    next
      fix u assume "insert x F <| u"
      then have "F <| u" and "x \<sqsubseteq> u" by simp_all
      with is_lubD2[OF w] have "{x, w} <| u" by fastforce
      with is_lubD2[OF pairlub] show "x \<squnion> w \<sqsubseteq> u" .
    qed
    then show ?case ..
  qed
  then have finite_lub: "finite B \<Longrightarrow> B <| z \<Longrightarrow> B <<| lub B" for z and B :: "'a set"
    using is_lub_lub by auto
  fix A and b :: 'a assume "A \<noteq> {}" "A <| b"
  from \<open>A <| b\<close> have "B \<in> Fpow(A) \<Longrightarrow> B <| b" for B
    unfolding Fpow_def is_ub_def by fast
  moreover have "B \<in> Fpow(A) \<Longrightarrow> finite B" for B by (simp add: Fpow_def)
  ultimately have "B \<in> Fpow(A) \<Longrightarrow> B <<| lub B" for B
    using finite_lub by fast
  with directed_join_of_finite_subsets(2)
  have "A <<| lub (lub ` Fpow(A))" by blast
  then show "\<exists>a. A <<| a" ..
qed

lemma (in cpo) bin_join_chain1:
  assumes cX: "chain X"
   and Z: "\<And>i. {X i, y} <<| Z i"
  shows "chain Z" and "{\<Squnion>i. X i, y} <<| (\<Squnion>i. Z i)"
proof -
  from Z show cZ: "chain Z"
    by (rule ch2ch_lub_gen) (blast intro: chainE[OF cX])
  show "{\<Squnion>i. X i, y} <<| (\<Squnion>i. Z i)"
  proof (rule is_lubI)
    from Z have "X i \<sqsubseteq> Z i" for i using is_lubD1[THEN is_ubD] by blast
    with cX cZ have 1: "(\<Squnion>i. X i) \<sqsubseteq> (\<Squnion>i. Z i)" by (rule lub_mono)
    from Z have "y \<sqsubseteq> Z i" for i using is_lubD1[THEN is_ubD] by blast
    with cZ have 2: "y \<sqsubseteq> (\<Squnion>i. Z i)" by (rule below_lub)
    from 1 2 show "{\<Squnion>i. X i, y} <| (\<Squnion>i. Z i)" by (intro is_ubI) auto
  next
    fix u assume u: "{\<Squnion>i. X i, y} <| u"
    from is_ubD[OF u] have 1: "(\<Squnion>i. X i) \<sqsubseteq> u" and 2: "y \<sqsubseteq> u" by auto
    from cX 1 have 1: "X i \<sqsubseteq> u" for i using lub_below_iff by blast
    from 1 2 have "{X i, y} <| u" for i by (intro is_ubI) auto
    with Z have "Z i \<sqsubseteq> u" for i by (rule is_lubD2)
    with cZ show "(\<Squnion>i. Z i) \<sqsubseteq> u" by (rule lub_below)
  qed
qed

lemma (in cpo) ex_join_adm: "adm (\<lambda>x. \<exists>z. {x, y} <<| z)"
proof (rule admI)
  fix X :: "nat \<Rightarrow> 'a"
  assume cX: "chain X"
  assume "\<forall>i. \<exists>z. {X i, y} <<| z"
  then obtain Z where Z: "{X i, y} <<| Z i" for i by metis
  with cX bin_join_chain1(2) show "\<exists>z. {\<Squnion>i. X i, y} <<| z" by blast
qed

lemma (in cpo) ex_join_adm2: "adm (\<lambda>y. \<exists>z. {x, y} <<| z)"
  unfolding bin_join_ex_symm by (fact ex_join_adm)

lemma compact_eq_approx2:
  fixes a b :: "'a::bifinite"
  assumes "compact a" "compact b"
  obtains d where "finite_deflation d" "d\<cdot>a = a" "d\<cdot>b = b"
proof -
  from bifinite obtain approx :: "nat \<Rightarrow> 'a \<rightarrow> 'a" where "approx_chain approx" ..
  then interpret approx_chain approx .
  note approx_mono = chain_mono[OF chain_approx,
      THEN deflation.belowD[OF deflation_approx]]
  from assms compact_eq_approx obtain i j where "approx i\<cdot>a = a" "approx j\<cdot>b = b" 
    by presburger
  with approx_mono have "approx (max i j)\<cdot>a = a" "approx (max i j)\<cdot>b = b"
    by (cases rule: le_cases[of i j], simp_all)+
  with finite_deflation_approx show ?thesis by (rule that)
qed

lemma compact_lubI:
  fixes a b :: "'a::bifinite"
  assumes compacts: "compact a" "compact b"
  assumes compactRule: "\<And>c. compact c \<Longrightarrow> a \<sqsubseteq> c \<Longrightarrow> b \<sqsubseteq> c \<Longrightarrow> a \<sqsubseteq> F a b \<and> b \<sqsubseteq> F a b \<and> F a b \<sqsubseteq> c"
 and c: "a \<sqsubseteq> c" "b \<sqsubseteq> c"
shows "{a, b} <<| F a b"
proof (rule is_lubI)
  from compacts obtain d where "finite_deflation d" and fixing: "d\<cdot>a = a" "d\<cdot>b = b"
    by (rule compact_eq_approx2)
  then interpret finite_deflation d by presburger
  from c have "a \<sqsubseteq> d\<cdot>c" "b \<sqsubseteq> d\<cdot>c"
    by (subst fixing[symmetric], fast intro: monofun_cfun_arg)+
  moreover have "compact (d\<cdot>c)" by (rule compact)
  ultimately have "a \<sqsubseteq> F a b" "b \<sqsubseteq> F a b" using compactRule by auto
  then show "{a, b} <| F a b" by simp
next
  fix u
  show "{a, b} <| u \<Longrightarrow> F a b \<sqsubseteq> u"
  proof (induction u rule: compact_induct', simp add: compacts)
    fix uu assume "compact uu" "{a, b} <| uu"
    with compactRule show "F a b \<sqsubseteq> uu" by auto
  qed
qed


text \<open>Bounded completeness through any chain of maps with lub \<open>ID\<close> (e.g. the \<open>take\<close> functions of
  a domain, or an approximation chain): it suffices that pairs of approximants have lubs
  under any common bound.\<close>

lemma chain_bounded_lub:
  fixes t :: "nat \<Rightarrow> 'a::cpo \<rightarrow> 'a"
  assumes t: "chain t" "(\<Squnion>i. t i) = ID"
    and lubs: "\<And>n a b c. t n\<cdot>a \<sqsubseteq> c \<Longrightarrow> t n\<cdot>b \<sqsubseteq> c \<Longrightarrow> \<exists>z. {t n\<cdot>a, t n\<cdot>b} <<| z"
    and "(a::'a) \<sqsubseteq> c" "b \<sqsubseteq> c"
  shows "\<exists>z. {a, b} <<| z"
proof -
  have reach: "(\<Squnion>n. t n\<cdot>x) = x" for x
    by (simp add: contlub_cfun_fun[OF t(1), symmetric] t(2))
  have chx: "chain (\<lambda>n. t n\<cdot>x)" for x by (rule ch2ch_Rep_cfunL[OF t(1)])
  have below: "t n\<cdot>x \<sqsubseteq> x" for n x
    using is_ub_thelub[OF chx, of n x] by (simp add: reach)
  define L where "L n = lub {t n\<cdot>a, t n\<cdot>b}" for n
  have L: "{t n\<cdot>a, t n\<cdot>b} <<| L n" for n
  proof -
    have "t n\<cdot>a \<sqsubseteq> c" "t n\<cdot>b \<sqsubseteq> c"
      using below \<open>a \<sqsubseteq> c\<close> \<open>b \<sqsubseteq> c\<close> by (blast intro: below_trans)+
    from lubs[OF this] obtain z where "{t n\<cdot>a, t n\<cdot>b} <<| z" by (elim exE)
    then show ?thesis unfolding L_def by (rule is_lub_lub)
  qed
  have chL: "chain L"
  proof (rule chainI)
    fix n
    have "t n\<cdot>a \<sqsubseteq> L (Suc n)" "t n\<cdot>b \<sqsubseteq> L (Suc n)"
      using chainE[OF chx] is_lubD1[OF L, THEN is_ubD]
      by (blast intro: below_trans)+
    then show "L n \<sqsubseteq> L (Suc n)" by (blast intro: is_lubD2[OF L] is_ubI)
  qed
  have "{a, b} <<| (\<Squnion>n. L n)"
  proof (rule is_lubI)
    have "(\<Squnion>n. t n\<cdot>a) \<sqsubseteq> (\<Squnion>n. L n)" "(\<Squnion>n. t n\<cdot>b) \<sqsubseteq> (\<Squnion>n. L n)"
      using is_lubD1[OF L, THEN is_ubD] by (blast intro: lub_mono chx chL)+
    then show "{a, b} <| (\<Squnion>n. L n)" by (simp add: reach is_ub_def)
  next
    fix u assume "{a, b} <| u"
    then have "a \<sqsubseteq> u" "b \<sqsubseteq> u" by (auto dest: is_ubD)
    then have "L n \<sqsubseteq> u" for n
      using below by (blast intro: is_lubD2[OF L] is_ubI below_trans)
    then show "(\<Squnion>n. L n) \<sqsubseteq> u" by (rule lub_below[OF chL])
  qed
  then show ?thesis ..
qed

lemma bounded_complete_chainI:
  fixes t :: "nat \<Rightarrow> 'a::dcpo \<rightarrow> 'a"
  assumes "chain t" "(\<Squnion>i. t i) = ID"
    and "\<And>n a b c. t n\<cdot>a \<sqsubseteq> c \<Longrightarrow> t n\<cdot>b \<sqsubseteq> c \<Longrightarrow> \<exists>z. {t n\<cdot>a, t n\<cdot>b} <<| z"
  shows "OFCLASS('a, bounded_complete_class)"
  by (rule bounded_complete_finite_joinI) (rule chain_bounded_lub[OF assms])

text \<open>The compact version is the approximation-chain instance.\<close>

lemma bounded_complete_finite_compact_joinI:
  assumes "\<And>a b c::'a::bifinite. \<lbrakk> compact a; compact b; a \<sqsubseteq> c; b \<sqsubseteq> c \<rbrakk> \<Longrightarrow> \<exists>z. {a, b} <<| z"
  shows "OFCLASS('a, bounded_complete_class)"
proof (rule bounded_complete_finite_joinI)
  fix a b c :: 'a assume "a \<sqsubseteq> c" "b \<sqsubseteq> c"
  from bifinite obtain approx :: "nat \<Rightarrow> 'a \<rightarrow> 'a" where "approx_chain approx" ..
  then interpret approx_chain approx .
  show "\<exists>z. {a, b} <<| z"
    by (rule chain_bounded_lub[OF chain_approx lub_approx _ \<open>a \<sqsubseteq> c\<close> \<open>b \<sqsubseteq> c\<close>], rule assms) simp_all
qed

lemma bounded_complete_finite_compact_joinI':
  assumes
    "\<And>a b c::'a::bifinite. \<lbrakk> compact a; compact b; compact c; a \<sqsubseteq> c; b \<sqsubseteq> c\<rbrakk> \<Longrightarrow> a \<sqsubseteq> F a b"
    "\<And>a b c::'a::bifinite. \<lbrakk> compact a; compact b; compact c; a \<sqsubseteq> c; b \<sqsubseteq> c\<rbrakk> \<Longrightarrow> b \<sqsubseteq> F a b"
    "\<And>a b c::'a::bifinite. \<lbrakk> compact a; compact b; compact c; a \<sqsubseteq> c; b \<sqsubseteq> c\<rbrakk> \<Longrightarrow> F a b \<sqsubseteq> c"
  shows "OFCLASS('a, bounded_complete_class)"
proof (rule bounded_complete_finite_compact_joinI)
  fix a b c :: 'a
  assume "compact a" "compact b" "a \<sqsubseteq> c" "b \<sqsubseteq> c"
  with assms have "{a, b} <<| F a b"
    by (intro compact_lubI[of a b F c]) presburger+
  then show "\<exists>z. {a, b} <<| z" ..
qed

lemma down_below: "fup\<cdot>ID\<cdot>x \<sqsubseteq> y \<longleftrightarrow> x \<sqsubseteq> up\<cdot>y"
  by (cases x) simp_all

corollary down_below_ub: "(\<lambda>x. fup\<cdot>ID\<cdot>x) ` X <| y \<longleftrightarrow> X <| up\<cdot>y"
  unfolding is_ub_def
  using down_below by blast

instance u :: (bounded_complete) bounded_complete
proof
  fix A :: "'a u set" assume "A \<noteq> {}"
  fix b assume "A <| b"
  show "\<exists>a. A <<| a"
  proof (cases "A <| \<bottom>")
    case True
    from is_ubD[OF this] have "A = {} \<or> A = {\<bottom>}" by auto
    then have "A <<| \<bottom>" by auto
    then show ?thesis ..
  next
    case False
    let ?down = "(\<lambda>x. fup\<cdot>ID\<cdot>x)"
    from \<open>A <| b\<close> have 1: "?down ` A <| ?down b"
      by (simp add: is_ub_def monofun_cfun_arg)
    define a where "a = lub (?down ` A)"
    thm ex_bound_lub
    from 1 have a: "?down ` A <<| a" unfolding a_def by (rule ex_bound_lub)
    have "A <<| up\<cdot>a"
    proof (rule is_lubI)
      show "A <| up\<cdot>a" using a[THEN is_lubD1] down_below_ub by blast
      fix u assume "A <| u"
      with \<open>\<not>(A <| \<bottom>)\<close> obtain u' where *: "u = up\<cdot>u'" "A <| up\<cdot>u'" by (cases u) simp_all
      then have "?down ` A <| u'" by (simp add: down_below_ub)
      with a have "a \<sqsubseteq> u'" by (rule is_lubD2)
      with * show "up\<cdot>a \<sqsubseteq> u" by simp
    qed
    then show ?thesis ..
  qed
qed

lemma meet_bottom [simp]:
  fixes x :: "'a::bounded_complete"
  shows "x \<sqinter> \<bottom> = \<bottom>" "\<bottom> \<sqinter> x = \<bottom>"
  by (simp_all add: meet_sym meet_absorbI)

lemma up_joinable_iff [simp]:
  fixes x y :: "'a::bounded_complete"
  shows "up\<cdot>x \<Up> up\<cdot>y \<longleftrightarrow> x \<Up> y"
proof
  assume "up\<cdot>x \<Up> up\<cdot>y"
  then obtain z where "up\<cdot>x \<sqsubseteq> z" "up\<cdot>y \<sqsubseteq> z" unfolding joinable_def by blast
  then show "x \<Up> y" by (cases z) (auto intro: joinableI)
next
  assume "x \<Up> y"
  then obtain z where "x \<sqsubseteq> z" "y \<sqsubseteq> z" unfolding joinable_def by blast
  then show "up\<cdot>x \<Up> up\<cdot>y" by (auto intro: joinableI[of _ "up\<cdot>z"])
qed

lemma up_join:
  fixes x y :: "'a::bounded_complete"
  assumes "x \<Up> y" shows "up\<cdot>x \<squnion> up\<cdot>y = up\<cdot>(x \<squnion> y)"
proof (rule below_antisym)
  have xy: "up\<cdot>x \<Up> up\<cdot>y" using assms by simp
  show "up\<cdot>x \<squnion> up\<cdot>y \<sqsubseteq> up\<cdot>(x \<squnion> y)"
    by (rule join_belowI) (simp_all add: joinableD[OF assms])
  have "up\<cdot>x \<sqsubseteq> up\<cdot>x \<squnion> up\<cdot>y" "up\<cdot>y \<sqsubseteq> up\<cdot>x \<squnion> up\<cdot>y" using joinableD[OF xy] by simp_all
  then show "up\<cdot>(x \<squnion> y) \<sqsubseteq> up\<cdot>x \<squnion> up\<cdot>y"
    by (cases "up\<cdot>x \<squnion> up\<cdot>y") (simp_all add: join_belowI)
qed

lemma up_meet [simp]:
  fixes x y :: "'a::bounded_complete"
  shows "up\<cdot>x \<sqinter> up\<cdot>y = up\<cdot>(x \<sqinter> y)"
proof (rule below_antisym)
  show "up\<cdot>(x \<sqinter> y) \<sqsubseteq> up\<cdot>x \<sqinter> up\<cdot>y"
    by (rule meet_greatest) (simp_all add: meet_below1 meet_below2)
  have "up\<cdot>x \<sqinter> up\<cdot>y \<sqsubseteq> up\<cdot>x" "up\<cdot>x \<sqinter> up\<cdot>y \<sqsubseteq> up\<cdot>y" by (rule meet_below1, rule meet_below2)
  then show "up\<cdot>x \<sqinter> up\<cdot>y \<sqsubseteq> up\<cdot>(x \<sqinter> y)"
    by (cases "up\<cdot>x \<sqinter> up\<cdot>y") (simp_all add: meet_greatest)
qed


subsection \<open>Strict sums\<close>

text \<open>A bounded set of a strict sum lies on one side, so its lub is computed there: projecting
  onto the side with \<open>sscase\<close> transports bounds back and forth.\<close>

lemma ssum_lub_sinl:
  fixes A :: "('a::bounded_complete \<oplus> 'b::bounded_complete) set"
  assumes "A <| sinl\<cdot>b" shows "\<exists>a. A <<| a"
proof -
  define d where "d = (sscase\<cdot>ID\<cdot>\<bottom> :: 'a \<oplus> 'b \<rightarrow> 'a)"
  define l where "l = lub ((\<lambda>x. d\<cdot>x) ` A)"
  have sinl_d_below: "sinl\<cdot>(d\<cdot>u) \<sqsubseteq> u" for u by (cases u) (simp_all add: d_def)
  have sinl_d: "x = sinl\<cdot>(d\<cdot>x)" if "x \<sqsubseteq> sinl\<cdot>b" for x
    using that by (cases x) (simp_all add: d_def)
  have "d\<cdot>x \<sqsubseteq> b" if "x \<in> A" for x
    using monofun_cfun_arg[OF is_ubD[OF assms that], of d] by (cases "b = \<bottom>") (simp_all add: d_def)
  then have "(\<lambda>x. d\<cdot>x) ` A <| b" by (auto intro: is_ubI)
  then have l: "(\<lambda>x. d\<cdot>x) ` A <<| l" unfolding l_def by (rule ex_bound_lub)
  have "A <<| sinl\<cdot>l"
  proof (rule is_lubI)
    show "A <| sinl\<cdot>l"
    proof (rule is_ubI)
      fix x assume x: "x \<in> A"
      have "d\<cdot>x \<sqsubseteq> l" using x by (blast intro: is_ubD[OF is_lubD1[OF l]])
      then have "sinl\<cdot>(d\<cdot>x) \<sqsubseteq> sinl\<cdot>l" by (rule monofun_cfun_arg)
      then show "x \<sqsubseteq> sinl\<cdot>l"
        by (rule back_subst) (rule sinl_d[OF is_ubD[OF assms x], symmetric])
    qed
  next
    fix u assume "A <| u"
    then have "(\<lambda>x. d\<cdot>x) ` A <| d\<cdot>u" by (auto intro!: is_ubI monofun_cfun_arg dest: is_ubD)
    with l have "l \<sqsubseteq> d\<cdot>u" by (rule is_lubD2)
    then have "sinl\<cdot>l \<sqsubseteq> sinl\<cdot>(d\<cdot>u)" by (rule monofun_cfun_arg)
    then show "sinl\<cdot>l \<sqsubseteq> u" using sinl_d_below by (rule below_trans)
  qed
  then show ?thesis ..
qed

lemma ssum_lub_sinr:
  fixes A :: "('a::bounded_complete \<oplus> 'b::bounded_complete) set"
  assumes "A <| sinr\<cdot>b" shows "\<exists>a. A <<| a"
proof -
  define d where "d = (sscase\<cdot>\<bottom>\<cdot>ID :: 'a \<oplus> 'b \<rightarrow> 'b)"
  define l where "l = lub ((\<lambda>x. d\<cdot>x) ` A)"
  have sinr_d_below: "sinr\<cdot>(d\<cdot>u) \<sqsubseteq> u" for u by (cases u) (simp_all add: d_def)
  have sinr_d: "x = sinr\<cdot>(d\<cdot>x)" if "x \<sqsubseteq> sinr\<cdot>b" for x
    using that by (cases x) (simp_all add: d_def)
  have "d\<cdot>x \<sqsubseteq> b" if "x \<in> A" for x
    using monofun_cfun_arg[OF is_ubD[OF assms that], of d] by (cases "b = \<bottom>") (simp_all add: d_def)
  then have "(\<lambda>x. d\<cdot>x) ` A <| b" by (auto intro: is_ubI)
  then have l: "(\<lambda>x. d\<cdot>x) ` A <<| l" unfolding l_def by (rule ex_bound_lub)
  have "A <<| sinr\<cdot>l"
  proof (rule is_lubI)
    show "A <| sinr\<cdot>l"
    proof (rule is_ubI)
      fix x assume x: "x \<in> A"
      have "d\<cdot>x \<sqsubseteq> l" using x by (blast intro: is_ubD[OF is_lubD1[OF l]])
      then have "sinr\<cdot>(d\<cdot>x) \<sqsubseteq> sinr\<cdot>l" by (rule monofun_cfun_arg)
      then show "x \<sqsubseteq> sinr\<cdot>l"
        by (rule back_subst) (rule sinr_d[OF is_ubD[OF assms x], symmetric])
    qed
  next
    fix u assume "A <| u"
    then have "(\<lambda>x. d\<cdot>x) ` A <| d\<cdot>u" by (auto intro!: is_ubI monofun_cfun_arg dest: is_ubD)
    with l have "l \<sqsubseteq> d\<cdot>u" by (rule is_lubD2)
    then have "sinr\<cdot>l \<sqsubseteq> sinr\<cdot>(d\<cdot>u)" by (rule monofun_cfun_arg)
    then show "sinr\<cdot>l \<sqsubseteq> u" using sinr_d_below by (rule below_trans)
  qed
  then show ?thesis ..
qed

instance ssum :: (bounded_complete, bounded_complete) bounded_complete
proof
  fix A :: "('a \<oplus> 'b) set" and b assume b: "A <| b"
  show "\<exists>a. A <<| a"
  proof (cases b)
    case bottom with b show ?thesis using ssum_lub_sinl[of A \<bottom>] by simp
  next
    case (sinl x) with b show ?thesis by (simp add: ssum_lub_sinl)
  next
    case (sinr y) with b show ?thesis by (simp add: ssum_lub_sinr)
  qed
qed

context
  fixes x x' :: "'a::bounded_complete" and y y' :: "'b::bounded_complete"
begin

lemma sinl_meet [simp]: "sinl\<cdot>x \<sqinter> sinl\<cdot>x' = (sinl\<cdot>(x \<sqinter> x') :: 'a \<oplus> 'b)"
proof (rule below_antisym)
  let ?m = "sinl\<cdot>x \<sqinter> sinl\<cdot>x' :: 'a \<oplus> 'b"
  show "sinl\<cdot>(x \<sqinter> x') \<sqsubseteq> ?m"
    by (rule meet_greatest) (simp_all add: meet_below1 meet_below2)
  have "?m \<sqsubseteq> sinl\<cdot>x" "?m \<sqsubseteq> sinl\<cdot>x'" by (rule meet_below1, rule meet_below2)
  then show "?m \<sqsubseteq> sinl\<cdot>(x \<sqinter> x')"
    by (cases ?m) (simp_all add: meet_greatest)
qed

lemma sinr_meet [simp]: "sinr\<cdot>y \<sqinter> sinr\<cdot>y' = (sinr\<cdot>(y \<sqinter> y') :: 'a \<oplus> 'b)"
proof (rule below_antisym)
  let ?m = "sinr\<cdot>y \<sqinter> sinr\<cdot>y' :: 'a \<oplus> 'b"
  show "sinr\<cdot>(y \<sqinter> y') \<sqsubseteq> ?m"
    by (rule meet_greatest) (simp_all add: meet_below1 meet_below2)
  have "?m \<sqsubseteq> sinr\<cdot>y" "?m \<sqsubseteq> sinr\<cdot>y'" by (rule meet_below1, rule meet_below2)
  then show "?m \<sqsubseteq> sinr\<cdot>(y \<sqinter> y')"
    by (cases ?m) (simp_all add: meet_greatest)
qed

lemma sinl_sinr_meet [simp]: "sinl\<cdot>x \<sqinter> sinr\<cdot>y = (\<bottom> :: 'a \<oplus> 'b)" "sinr\<cdot>y \<sqinter> sinl\<cdot>x = (\<bottom> :: 'a \<oplus> 'b)"
proof -
  have "sinl\<cdot>x \<sqinter> sinr\<cdot>y \<sqsubseteq> sinl\<cdot>x" "sinl\<cdot>x \<sqinter> sinr\<cdot>y \<sqsubseteq> (sinr\<cdot>y :: 'a \<oplus> 'b)"
    by (rule meet_below1, rule meet_below2)
  then show "sinl\<cdot>x \<sqinter> sinr\<cdot>y = (\<bottom> :: 'a \<oplus> 'b)"
    by (cases "sinl\<cdot>x \<sqinter> sinr\<cdot>y :: 'a \<oplus> 'b") simp_all
  then show "sinr\<cdot>y \<sqinter> sinl\<cdot>x = (\<bottom> :: 'a \<oplus> 'b)" by (simp add: meet_sym)
qed

lemma sinl_joinable_iff [simp]: "(sinl\<cdot>x :: 'a \<oplus> 'b) \<Up> sinl\<cdot>x' \<longleftrightarrow> x \<Up> x'"
proof
  assume "(sinl\<cdot>x :: 'a \<oplus> 'b) \<Up> sinl\<cdot>x'"
  then obtain z :: "'a \<oplus> 'b" where "sinl\<cdot>x \<sqsubseteq> z" "sinl\<cdot>x' \<sqsubseteq> z" unfolding joinable_def by blast
  then show "x \<Up> x'" by (cases z) (auto intro: joinableI)
next
  assume "x \<Up> x'"
  then obtain z where "x \<sqsubseteq> z" "x' \<sqsubseteq> z" unfolding joinable_def by blast
  then show "(sinl\<cdot>x :: 'a \<oplus> 'b) \<Up> sinl\<cdot>x'" by (auto intro: joinableI[of _ "sinl\<cdot>z"])
qed

lemma sinr_joinable_iff [simp]: "(sinr\<cdot>y :: 'a \<oplus> 'b) \<Up> sinr\<cdot>y' \<longleftrightarrow> y \<Up> y'"
proof
  assume "(sinr\<cdot>y :: 'a \<oplus> 'b) \<Up> sinr\<cdot>y'"
  then obtain z :: "'a \<oplus> 'b" where "sinr\<cdot>y \<sqsubseteq> z" "sinr\<cdot>y' \<sqsubseteq> z" unfolding joinable_def by blast
  then show "y \<Up> y'" by (cases z) (auto intro: joinableI)
next
  assume "y \<Up> y'"
  then obtain z where "y \<sqsubseteq> z" "y' \<sqsubseteq> z" unfolding joinable_def by blast
  then show "(sinr\<cdot>y :: 'a \<oplus> 'b) \<Up> sinr\<cdot>y'" by (auto intro: joinableI[of _ "sinr\<cdot>z"])
qed

lemma sinl_sinr_joinable_iff [simp]:
  "(sinl\<cdot>x :: 'a \<oplus> 'b) \<Up> sinr\<cdot>y \<longleftrightarrow> x = \<bottom> \<or> y = \<bottom>" "(sinr\<cdot>y :: 'a \<oplus> 'b) \<Up> sinl\<cdot>x \<longleftrightarrow> x = \<bottom> \<or> y = \<bottom>"
proof -
  have "(sinl\<cdot>x :: 'a \<oplus> 'b) \<Up> sinr\<cdot>y \<longleftrightarrow> x = \<bottom> \<or> y = \<bottom>"
  proof
    assume "(sinl\<cdot>x :: 'a \<oplus> 'b) \<Up> sinr\<cdot>y"
    then obtain z :: "'a \<oplus> 'b" where "sinl\<cdot>x \<sqsubseteq> z" "sinr\<cdot>y \<sqsubseteq> z" unfolding joinable_def by blast
    then show "x = \<bottom> \<or> y = \<bottom>" by (cases z) simp_all
  qed auto
  then show "(sinl\<cdot>x :: 'a \<oplus> 'b) \<Up> sinr\<cdot>y \<longleftrightarrow> x = \<bottom> \<or> y = \<bottom>"
    "(sinr\<cdot>y :: 'a \<oplus> 'b) \<Up> sinl\<cdot>x \<longleftrightarrow> x = \<bottom> \<or> y = \<bottom>" by (simp_all add: joinable_sym)
qed

lemma sinl_join: "x \<Up> x' \<Longrightarrow> sinl\<cdot>x \<squnion> sinl\<cdot>x' = (sinl\<cdot>(x \<squnion> x') :: 'a \<oplus> 'b)"
proof (rule below_antisym)
  assume xx: "x \<Up> x'"
  let ?j = "sinl\<cdot>x \<squnion> sinl\<cdot>x' :: 'a \<oplus> 'b"
  have j: "(sinl\<cdot>x :: 'a \<oplus> 'b) \<Up> sinl\<cdot>x'" using xx by simp
  show "?j \<sqsubseteq> sinl\<cdot>(x \<squnion> x')"
    by (rule join_belowI) (simp_all add: joinableD[OF xx])
  have "sinl\<cdot>x \<sqsubseteq> ?j" "sinl\<cdot>x' \<sqsubseteq> ?j" using joinableD[OF j] by simp_all
  then show "sinl\<cdot>(x \<squnion> x') \<sqsubseteq> ?j"
    by (cases ?j) (simp_all add: join_belowI)
qed

lemma sinr_join: "y \<Up> y' \<Longrightarrow> sinr\<cdot>y \<squnion> sinr\<cdot>y' = (sinr\<cdot>(y \<squnion> y') :: 'a \<oplus> 'b)"
proof (rule below_antisym)
  assume yy: "y \<Up> y'"
  let ?j = "sinr\<cdot>y \<squnion> sinr\<cdot>y' :: 'a \<oplus> 'b"
  have j: "(sinr\<cdot>y :: 'a \<oplus> 'b) \<Up> sinr\<cdot>y'" using yy by simp
  show "?j \<sqsubseteq> sinr\<cdot>(y \<squnion> y')"
    by (rule join_belowI) (simp_all add: joinableD[OF yy])
  have "sinr\<cdot>y \<sqsubseteq> ?j" "sinr\<cdot>y' \<sqsubseteq> ?j" using joinableD[OF j] by simp_all
  then show "sinr\<cdot>(y \<squnion> y') \<sqsubseteq> ?j"
    by (cases ?j) (simp_all add: join_belowI)
qed

end


subsection \<open>Cartesian products\<close>

text \<open>Everything is componentwise.\<close>

lemma prod_ub_iff: "A <| b \<longleftrightarrow> fst ` A <| fst b \<and> snd ` A <| snd b"
  by (auto simp: is_ub_def below_prod_def)

instance prod :: (bounded_complete, bounded_complete) bounded_complete
proof
  fix A :: "('a \<times> 'b) set" and b assume "A <| b"
  then have "fst ` A <<| lub (fst ` A)" "snd ` A <<| lub (snd ` A)"
    by (auto simp: prod_ub_iff intro: ex_bound_lub)
  then have "A <<| (lub (fst ` A), lub (snd ` A))"
    by (auto simp: is_lub_def prod_ub_iff below_prod_def)
  then show "\<exists>a. A <<| a" ..
qed

lemma prod_joinable_iff: "x \<Up> y \<longleftrightarrow> fst x \<Up> fst y \<and> snd x \<Up> snd y"
  unfolding joinable_def below_prod_def by (metis fst_conv snd_conv)

context
  fixes x y :: "'a::bounded_complete \<times> 'b::bounded_complete"
begin

lemma prod_meet: "x \<sqinter> y = (fst x \<sqinter> fst y, snd x \<sqinter> snd y)"
proof (rule below_antisym)
  show "x \<sqinter> y \<sqsubseteq> (fst x \<sqinter> fst y, snd x \<sqinter> snd y)"
    using meet_below1[of x y] meet_below2[of x y] by (simp add: below_prod_def meet_greatest)
  show "(fst x \<sqinter> fst y, snd x \<sqinter> snd y) \<sqsubseteq> x \<sqinter> y"
    by (rule meet_greatest) (simp_all add: below_prod_def meet_below1 meet_below2)
qed

lemma prod_join: "x \<Up> y \<Longrightarrow> x \<squnion> y = (fst x \<squnion> fst y, snd x \<squnion> snd y)"
proof (rule below_antisym)
  assume xy: "x \<Up> y"
  then have c: "fst x \<Up> fst y" "snd x \<Up> snd y" by (simp_all add: prod_joinable_iff)
  show "x \<squnion> y \<sqsubseteq> (fst x \<squnion> fst y, snd x \<squnion> snd y)"
    by (rule join_belowI) (simp_all add: below_prod_def joinableD[OF c(1)] joinableD[OF c(2)])
  show "(fst x \<squnion> fst y, snd x \<squnion> snd y) \<sqsubseteq> x \<squnion> y"
    using joinableD[OF xy] by (simp add: below_prod_def join_belowI)
qed

end

subsection \<open>Smash products\<close>

text \<open>Componentwise, through @{thm [source] below_sprod}; the only care needed is that the pair
  of component lubs does not collapse, which holds as soon as one element is nonbottom.\<close>

instance sprod :: (bounded_complete, bounded_complete) bounded_complete
proof
  fix A :: "('a \<otimes> 'b) set" and b assume ne: "A \<noteq> {}" and ub: "A <| b"
  show "\<exists>a. A <<| a"
  proof (cases "A = {\<bottom>}")
    case True then show ?thesis by (auto intro: is_lubI is_ubI)
  next
    case False
    with ne obtain x0 where x0: "x0 \<in> A" "x0 \<noteq> \<bottom>" by blast
    have "(\<lambda>x. sfst\<cdot>x) ` A <| sfst\<cdot>b" "(\<lambda>x. ssnd\<cdot>x) ` A <| ssnd\<cdot>b"
      using ub by (auto intro!: is_ubI monofun_cfun_arg dest: is_ubD)
    then obtain L1 L2 where L1: "(\<lambda>x. sfst\<cdot>x) ` A <<| L1" and L2: "(\<lambda>x. ssnd\<cdot>x) ` A <<| L2"
      by (blast dest: ex_bound_ex_lub)
    have le: "sfst\<cdot>x \<sqsubseteq> L1" "ssnd\<cdot>x \<sqsubseteq> L2" if "x \<in> A" for x
      using that is_lubD1[OF L1] is_lubD1[OF L2] by (auto dest: is_ubD)
    have nb: "L1 \<noteq> \<bottom>" "L2 \<noteq> \<bottom>"
      using le[OF x0(1)] x0(2) by (auto dest: bottomI)
    have "A <<| (:L1, L2:)"
    proof (rule is_lubI)
      show "A <| (:L1, L2:)"
        using le nb by (auto intro!: is_ubI simp: below_sprod)
    next
      fix u assume u: "A <| u"
      have "L1 \<sqsubseteq> sfst\<cdot>u" "L2 \<sqsubseteq> ssnd\<cdot>u"
        using u by (auto intro!: is_lubD2[OF L1] is_lubD2[OF L2] is_ubI monofun_cfun_arg
          dest: is_ubD)
      then show "(:L1, L2:) \<sqsubseteq> u" using nb by (simp add: below_sprod)
    qed
    then show ?thesis ..
  qed
qed

lemma sfst_spair_below: "sfst\<cdot>(:x, y:) \<sqsubseteq> x" and ssnd_spair_below: "ssnd\<cdot>(:x, y:) \<sqsubseteq> y"
  by (cases "y = \<bottom>"; simp) (cases "x = \<bottom>"; simp)

context
  fixes x x' :: "'a::bounded_complete" and y y' :: "'b::bounded_complete"
begin

text \<open>Meets are componentwise without side conditions: a collapsing component makes the whole
  pair \<open>\<bottom>\<close>, by strictness of @{const spair}.\<close>

lemma spair_meet: "(:x, y:) \<sqinter> (:x', y':) = (:x \<sqinter> x', y \<sqinter> y':)"
proof (rule below_antisym)
  let ?m = "(:x, y:) \<sqinter> (:x', y':)"
  have "sfst\<cdot>?m \<sqsubseteq> x \<sqinter> x'" "ssnd\<cdot>?m \<sqsubseteq> y \<sqinter> y'"
    by (intro meet_greatest below_trans[OF monofun_cfun_arg[OF meet_below1] sfst_spair_below]
        below_trans[OF monofun_cfun_arg[OF meet_below2] sfst_spair_below]
        below_trans[OF monofun_cfun_arg[OF meet_below1] ssnd_spair_below]
        below_trans[OF monofun_cfun_arg[OF meet_below2] ssnd_spair_below])+
  then have "(:sfst\<cdot>?m, ssnd\<cdot>?m:) \<sqsubseteq> (:x \<sqinter> x', y \<sqinter> y':)" by (intro monofun_cfun) simp_all
  then show "?m \<sqsubseteq> (:x \<sqinter> x', y \<sqinter> y':)" by (simp only: spair_sfst_ssnd)
  show "(:x \<sqinter> x', y \<sqinter> y':) \<sqsubseteq> ?m"
    by (intro meet_greatest monofun_cfun monofun_cfun_arg meet_below1 meet_below2)
qed

context
  assumes nb: "x \<noteq> \<bottom>" "y \<noteq> \<bottom>" "x' \<noteq> \<bottom>" "y' \<noteq> \<bottom>"
begin

lemma spair_joinable_iff: "(:x, y:) \<Up> (:x', y':) \<longleftrightarrow> x \<Up> x' \<and> y \<Up> y'"
proof
  assume "(:x, y:) \<Up> (:x', y':)"
  then obtain u where "(:x, y:) \<sqsubseteq> u" "(:x', y':) \<sqsubseteq> u" unfolding joinable_def by blast
  then show "x \<Up> x' \<and> y \<Up> y'" using nb by (auto simp: below_sprod intro: joinableI)
next
  assume "x \<Up> x' \<and> y \<Up> y'"
  then have "(:x, y:) \<sqsubseteq> (:x \<squnion> x', y \<squnion> y':)" "(:x', y':) \<sqsubseteq> (:x \<squnion> x', y \<squnion> y':)"
    by (auto intro!: monofun_cfun monofun_cfun_arg joinableD)
  then show "(:x, y:) \<Up> (:x', y':)" by (rule joinableI)
qed

lemma spair_join:
  assumes "x \<Up> x'" "y \<Up> y'" shows "(:x, y:) \<squnion> (:x', y':) = (:x \<squnion> x', y \<squnion> y':)"
proof (rule below_antisym)
  have j: "(:x, y:) \<Up> (:x', y':)" using assms by (simp add: spair_joinable_iff)
  show "(:x, y:) \<squnion> (:x', y':) \<sqsubseteq> (:x \<squnion> x', y \<squnion> y':)"
    using assms by (intro join_belowI monofun_cfun monofun_cfun_arg joinableD)
  have "x \<sqsubseteq> sfst\<cdot>((:x, y:) \<squnion> (:x', y':))" "x' \<sqsubseteq> sfst\<cdot>((:x, y:) \<squnion> (:x', y':))"
    "y \<sqsubseteq> ssnd\<cdot>((:x, y:) \<squnion> (:x', y':))" "y' \<sqsubseteq> ssnd\<cdot>((:x, y:) \<squnion> (:x', y':))"
    using monofun_cfun_arg[OF joinableD(1)[OF j], of sfst] monofun_cfun_arg[OF joinableD(2)[OF j], of sfst]
      monofun_cfun_arg[OF joinableD(1)[OF j], of ssnd] monofun_cfun_arg[OF joinableD(2)[OF j], of ssnd]
    using nb by simp_all
  then have "(:x \<squnion> x', y \<squnion> y':) \<sqsubseteq> (:sfst\<cdot>((:x, y:) \<squnion> (:x', y':)), ssnd\<cdot>((:x, y:) \<squnion> (:x', y':)):)"
    by (intro monofun_cfun monofun_cfun_arg join_belowI)
  then show "(:x \<squnion> x', y \<squnion> y':) \<sqsubseteq> (:x, y:) \<squnion> (:x', y':)" by (simp only: spair_sfst_ssnd)
qed

end

end

subclass (in flat) bounded_complete
proof
  fix A :: "'a set" and b :: 'a
  assume "A \<noteq> {}"
  assume "A <| b"
  then have "\<forall>x \<in> A. x = \<bottom> \<or> x = b" using is_ubD[THEN ax_flat] by blast
  with \<open>A \<noteq> {}\<close> consider "A = {b}" | "A = {\<bottom>}" | "A = {\<bottom>, b}"
    by fast
  then show "\<exists>z. A <<| z"
    by (cases) (auto intro: is_lubI is_ubI dest: is_ubD)
qed


instantiation "fun" :: (type, bounded_complete) bounded_complete
begin

lemma fun_ub_iff: "A <| b \<longleftrightarrow> (\<forall>p. (\<lambda>f. f p) ` A <| b p)"
  by (auto simp add: is_ub_def fun_below_iff)

lemma fun_lub_iff: "A <<| b \<longleftrightarrow> (\<forall>p. (\<lambda>f. f p) ` A <<| b p)"
(is "?f \<longleftrightarrow> (\<forall>p. ?p p)")
proof
  show "(\<forall>p. ?p p) \<Longrightarrow> ?f"
    by (auto simp add: is_lub_def is_ub_def fun_ub_iff fun_below_iff)
  show "(\<forall>p. ?p p)" if "?f"
  proof (intro strip is_lubI)
    from that have b_ub: "A <| b" by (rule is_lubD1)
    fix p
    show "(\<lambda>f. f p) ` A <| b p" using b_ub fun_ub_iff by fast
    fix u
    assume "(\<lambda>f. f p) ` A <| u"
    with b_ub have "A <| b(p := u)"
      unfolding fun_ub_iff by simp
    with that have "b \<sqsubseteq> b(p := u)"
      by (rule is_lubD2)
    from fun_belowD[OF this, of p] show "b p \<sqsubseteq> u" by simp
  qed
qed

lemma fun_bounded_complete:
  fixes A :: "('a \<Rightarrow> 'b) set"
    and b
  assumes "A <| b"
  shows "A <<| (\<lambda>p. (\<Squnion>f \<in> A. f p))"
proof -
  from assms have "(\<lambda>f. f p) ` A <| b p" for p
    by (simp add: fun_ub_iff)
  then have "(\<lambda>f. f p) ` A <<| (\<Squnion>f \<in> A. f p)" for p
    by (rule ex_bound_lub)
  then show "A <<| (\<lambda>p. (\<Squnion>f \<in> A. f p))"
    by (simp add: fun_lub_iff)
qed

instance proof qed (blast intro: fun_bounded_complete)

end

lemma fun_lub:
  fixes A :: "('a::type \<Rightarrow> 'b::bounded_complete) set"
    and b
  assumes "A <| b"
  shows "lub A = (\<lambda>p. (\<Squnion>f \<in> A. f p))"
  using lub_eqI[OF fun_bounded_complete, OF assms] .

lemma fun_join:
  fixes f g :: "'a::type \<Rightarrow> 'b::bounded_complete"
  assumes "f \<Up> g"
  shows "f \<squnion> g = (\<lambda>x. f x \<squnion> g x)"
proof -
  from assms obtain z where "{f, g} <| z"
    by (auto simp add: joinable_def is_ub_def)
  from fun_lub[OF this]
  show ?thesis unfolding join_def by simp
qed

lemma fun_meet:
  fixes f g :: "'a::type \<Rightarrow> 'b::bounded_complete"
  shows "f \<sqinter> g = (\<lambda>x. f x \<sqinter> g x)"
proof (rule below_antisym)
  show "f \<sqinter> g \<sqsubseteq> (\<lambda>x. f x \<sqinter> g x)"
  proof (rule fun_belowI)
    fix x
    have "(f \<sqinter> g) x \<sqsubseteq> f x" "(f \<sqinter> g) x \<sqsubseteq> g x"
      by (auto intro: fun_belowD meet_below1 meet_below2)
    thus "(f \<sqinter> g) x \<sqsubseteq> (\<lambda>x. f x \<sqinter> g x) x" by (simp add: meet_greatest)
  qed
next
  show "(\<lambda>x. f x \<sqinter> g x) \<sqsubseteq> f \<sqinter> g"
    by (rule meet_greatest; rule fun_belowI) (simp_all add: meet_below1 meet_below2)
qed


instantiation cfun :: (cpo, bounded_complete) bounded_complete
begin

lemma cfun_ub_iff: "A <| b \<longleftrightarrow> (\<forall>p. (\<lambda>f. f\<cdot>p) ` A <| b\<cdot>p)"
  by (auto simp add: is_ub_def cfun_below_iff)

lemma cfun_lubI: "(\<And>p. (\<lambda>f. f\<cdot>p) ` A <<| b\<cdot>p) \<Longrightarrow> (A <<| b)"
by (simp add: is_lub_def cfun_ub_iff cfun_below_iff)

context
  fixes  A :: "('a \<rightarrow> 'b) set"
    and b
  assumes Ab: "A <| b"
begin

private lemma pointwise_lubs: "(\<lambda>f. f\<cdot>p) ` A <<| (\<Squnion> f \<in> A. f\<cdot>p)" for p
proof -
  from Ab have "(\<lambda>f. f\<cdot>p) ` A <| b\<cdot>p" for p
    by (auto dest: is_ubD intro!: is_ubI monofun_cfun_fun)
  then show ?thesis
    by (rule ex_bound_lub)
qed

lemma cfun_bound_cont[simp]: "(\<Lambda> p. (\<Squnion>f \<in> A. f\<cdot>p))\<cdot>p = (\<Squnion> f \<in> A. f\<cdot>p)" for p
proof (rule beta_cfun, rule contI)
  fix Y :: "nat \<Rightarrow> 'a" assume "chain Y"
  then have "range (\<lambda>i. \<Squnion>f\<in>A. f\<cdot>(Y i)) <<| (\<Squnion>f\<in>A. (\<Squnion>i. f\<cdot>(Y i)))"
    by (auto intro: chain_lub_family_converse pointwise_lubs)
  then show "range (\<lambda>i. \<Squnion>f\<in>A. f\<cdot>(Y i)) <<| (\<Squnion>f\<in>A. f\<cdot>(\<Squnion>i. Y i))"
    by (simp add: \<open>chain Y\<close> contlub_cfun_arg)
qed

lemma cfun_bounded_complete: "A <<| (\<Lambda> p. (\<Squnion>f \<in> A. f\<cdot>p))"
  using pointwise_lubs by (simp add: is_lub_def is_ub_def cfun_below_iff)
end

instance proof qed (blast intro: cfun_bounded_complete)

end

lemma cfun_lub:
  fixes A :: "('a::cpo \<rightarrow> 'b::bounded_complete) set"
    and b
  assumes "A <| b"
  shows "(lub A)\<cdot>p = (\<Squnion>f \<in> A. f\<cdot>p)"
  using cfun_bounded_complete[OF assms, THEN lub_eqI]
  cfun_bound_cont[OF assms] by simp

lemma cfun_join:
  fixes f g :: "'a::cpo \<rightarrow> 'b::bounded_complete"
  assumes "f \<Up> g"
  shows "(f \<squnion> g)\<cdot>p = f\<cdot>p \<squnion> g\<cdot>p"
proof -
  from assms obtain z where "{f, g} <| z"
    by (auto simp add: joinable_def is_ub_def)
  from cfun_lub[OF this]
  show ?thesis unfolding join_def by simp
qed

instantiation sfun :: (pcpo, bounded_complete) bounded_complete
begin

context
  fixes A and b :: "'a \<rightarrow>! 'b"
  assumes Ab: "A <| b"
begin

private lemma sfun_cfun_lub: "(\<lambda>f. sfun_rep\<cdot>f) ` A <<| (\<Squnion>f \<in> A. sfun_rep\<cdot>f)"
proof -
  from Ab have "(\<lambda>f. sfun_rep\<cdot>f) ` A <| sfun_rep\<cdot>b"
    by (auto dest: is_ubD intro!: is_ubI monofun_cfun_arg)
  then show ?thesis by (rule ex_bound_lub)
qed

lemma sfun_lub_strict: "strictify\<cdot>(\<Squnion>f \<in> A. sfun_rep\<cdot>f) = (\<Squnion>f \<in> A. sfun_rep\<cdot>f)"
(is "strictify\<cdot>?lub = ?lub")
proof (rule below_antisym)
  show "strictify\<cdot>?lub \<sqsubseteq> ?lub" by (rule cfun_belowI) (simp add: strictify_conv_if)
  show "?lub \<sqsubseteq> strictify\<cdot>?lub" using sfun_cfun_lub
    apply (rule is_lubD2, intro is_ubI cfun_belowI)
    by (auto simp add: strictify_conv_if
          intro!: sfun_cfun_lub[THEN is_lubD1, THEN is_ubD, THEN monofun_cfun_fun])
qed

lemma sfun_bounded_complete:
  "A <<| sfun_abs\<cdot>(\<Squnion>f \<in> A. sfun_rep\<cdot>f)" (is "?A <<| sfun_abs\<cdot>?lub")
proof -
  from sfun_cfun_lub have "(\<lambda>f. sfun_rep\<cdot>f) ` A <<| sfun_rep\<cdot>(sfun_abs\<cdot>?lub)"
    by (simp add: sfun_lub_strict)
  then show ?thesis
    by (simp add: is_lub_def is_ub_def sfun_below_iff)
qed

end

instance proof qed (blast intro: sfun_bounded_complete)

end

default_sort bifinite

lemma (in bounded_complete) lattice:
  assumes "\<And>a b. a \<Up> b"
  shows "class.lattice meet below below_strict join"
  by (intro class.lattice.intro semilattice_meet class.semilattice_sup.intro below_order)
    (unfold_locales, auto intro: joinableD[OF assms] join_belowI)

lemma (in bounded_complete) bdd_above_iff:
"preorder.bdd_above (\<sqsubseteq>) A \<longleftrightarrow> (\<exists>a. A <| a)"
  unfolding preorder.bdd_above_def[OF class.order.axioms(1)[OF below_order]] is_ub_def
  by fast

lemma (in bounded_complete) cclattice:
  assumes "\<And>a b. a \<Up> b"
  shows "class.conditionally_complete_lattice glb lub meet below below_strict join"
  by (intro class.conditionally_complete_lattice.intro lattice[OF assms])
    (unfold_locales, auto intro: joinableD[OF assms] join_belowI glb_below glb_greatest
      lub_belowI[unfolded is_ub_def] below_lubI simp add: bdd_above_iff)

instantiation lower_pd :: (bifinite) bounded_complete
begin
instance proof (intro bounded_complete_finite_compact_joinI')
  fix a b c :: "'a lower_pd"
  show "a \<sqsubseteq> a \<union>\<flat> b" "b \<sqsubseteq> a \<union>\<flat> b" by (fact lower_plus_below1 lower_plus_below2)+
  assume "a \<sqsubseteq> c" "b \<sqsubseteq> c"
  then show "a \<union>\<flat> b \<sqsubseteq> c" unfolding lower_plus_below_iff by presburger
qed

lemma joinable[simp]: "(a :: 'a lower_pd) \<Up> b" using lower_plus_below1 lower_plus_below2
  by (rule joinableI)

lemma lower_join_eq: "(a :: 'a lower_pd) \<squnion> b = a \<union>\<flat> b"
proof (rule below_antisym)
  from lower_plus_below1 lower_plus_below2 show "a \<squnion> b \<sqsubseteq> a \<union>\<flat> b" by (rule join_belowI)
  from joinableD[OF joinable] show "a \<union>\<flat> b \<sqsubseteq> a \<squnion> b"
    by (rule lower_plus_least)
qed


global_interpretation lower_pd_lattice: conditionally_complete_lattice "glb :: ('a lower_pd) set \<Rightarrow> ('a lower_pd)" lub meet below below_strict join
  using cclattice[OF joinable] .

end

definition min_ub :: "'a::po \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "min_ub a b z \<equiv> a \<sqsubseteq> z \<and> b \<sqsubseteq> z \<and> (\<forall>w. a \<sqsubseteq> w \<longrightarrow> b \<sqsubseteq> w \<longrightarrow> w \<sqsubseteq> z \<longrightarrow> w = z)"

lemma min_ubI[intro]:
  assumes "a \<sqsubseteq> z" "b \<sqsubseteq> z" "\<And>w. a \<sqsubseteq> w \<Longrightarrow> b \<sqsubseteq> w \<Longrightarrow> w \<sqsubseteq> z \<Longrightarrow> w = z"
  shows "min_ub a b z"
  unfolding min_ub_def using assms by blast

lemma min_ub_of_compact: fixes a b :: "'a::bifinite" assumes "compact a" "compact b"
  shows min_ub_below: "a \<sqsubseteq> z \<Longrightarrow> b \<sqsubseteq> z \<Longrightarrow> \<exists>w. min_ub a b w \<and> w \<sqsubseteq> z"
    and min_ub_compact: "\<And>w. min_ub a b w \<Longrightarrow> compact w"
    and min_ub_finite: "finite {w. min_ub a b w}"
proof -
  from bifinite obtain approx :: "nat \<Rightarrow> 'a \<rightarrow> 'a" where "approx_chain approx" ..
  then interpret approx_chain approx .
  have idem_mono: "i \<le> j \<Longrightarrow> approx i\<cdot>x = x \<Longrightarrow> approx j\<cdot>x = x" for i j x
  proof -
    assume "i \<le> j" then have "approx i\<cdot>x \<sqsubseteq> approx j\<cdot>x"
      by (rule chain_approx[THEN chain_mono, THEN monofun_cfun_fun])
    also assume "approx i\<cdot>x = x"
    also have "approx j\<cdot>x \<sqsubseteq> x" by (rule approx_below)
    finally show ?thesis ..
  qed

  from compact_eq_approx assms(1,2) obtain i j where f: "approx i\<cdot>a = a" "approx j\<cdot>b = b"
    by blast
  define k where "k = max i j"
  with f have idem: "approx k\<cdot>a = a" "approx k\<cdot>b = b"
    by (auto intro: idem_mono max.cobounded1 max.cobounded2)
  define D where "D \<equiv> range (\<lambda>x. approx k\<cdot>x)"  
  have "finite D" unfolding D_def by (rule finite_range_approx)

  {
    fix z :: 'a
    define z' where "z' = approx k\<cdot>z"
    assume "a \<sqsubseteq> z" "b \<sqsubseteq> z"
    with idem have deflated: "a \<sqsubseteq> z'" "b \<sqsubseteq> z'"
    unfolding z'_def
    by (metis monofun_cfun_arg)+
    define B where "B = {x \<in> D. a \<sqsubseteq> x \<and> b \<sqsubseteq> x \<and> x \<sqsubseteq> z'}"
    from \<open>finite D\<close> have fin: "finite B" unfolding B_def by force
    have "z' \<in> D" unfolding z'_def D_def by simp
    then have "z' \<in> B" unfolding B_def using deflated by force
    then have ne: "B \<noteq> {}" by blast
    from fin ne have "\<exists>mu \<in> B. (\<forall>x \<in> B. x \<sqsubseteq> mu \<longrightarrow> x = mu)"
    proof (induction B rule: finite_ne_induct)
      case (singleton x)
      then show ?case by simp
    next
      case (insert nu F)
      show ?case
        by (metis insert.IH below_trans insert_iff po_eq_conv)
    qed
    then obtain mu where "mu \<in> B" and muR: "\<And>x. x \<in> B \<Longrightarrow> x \<sqsubseteq> mu \<Longrightarrow> x = mu"
      by blast
    have mu_idem: "approx k\<cdot>mu = mu"
      using \<open>mu \<in> B\<close>[unfolded B_def D_def]
      approx_idem by blast
    have mu_lower: "mu \<sqsubseteq> z'" using \<open>mu \<in> B\<close>[unfolded B_def] by blast
    have "min_ub a b mu"
    proof
      from \<open>mu \<in> B\<close>[unfolded B_def] show "a \<sqsubseteq> mu" "b \<sqsubseteq> mu" by simp_all
      fix w assume "a \<sqsubseteq> w" "b \<sqsubseteq> w" "w \<sqsubseteq> mu"
      with idem mu_idem have "a \<sqsubseteq> approx k\<cdot>w \<and> b \<sqsubseteq> approx k\<cdot>w"
        and under: "approx k\<cdot>w \<sqsubseteq> mu"
        by (metis monofun_cfun_arg)+
      with mu_lower have "approx k\<cdot>w \<in> B" unfolding B_def D_def
        using below_trans by blast
      from this under have "approx k\<cdot>w = mu" by (rule muR)
      then have "mu \<sqsubseteq> w" using approx_below by blast
      with \<open>w \<sqsubseteq> mu\<close> show "w = mu" by (rule below_antisym)
    qed
    moreover from mu_lower[unfolded z'_def] approx_below have "mu \<sqsubseteq> z"
      by (rule below_trans)
    ultimately show "\<exists>w. min_ub a b w \<and> w \<sqsubseteq> z" by blast
  }
  {
    have w_idem: "approx k\<cdot>w = w" if "min_ub a b w" for w
    proof -
      from that have "a \<sqsubseteq> w \<and> b \<sqsubseteq> w" by (simp add: min_ub_def)
      with idem have "a \<sqsubseteq> approx k\<cdot>w \<and> b \<sqsubseteq> approx k\<cdot>w"
        by (metis monofun_cfun_arg)
      with that approx_below show ?thesis by (simp add: min_ub_def)
    qed
    then have "{w. min_ub a b w} \<subseteq> D" unfolding D_def 
      by (simp add: Collect_mono_iff deflation.range_eq_fixes
          deflation_approx)
    from this \<open>finite D\<close> show "finite {w. min_ub a b w}" by (rule finite_subset)
    from w_idem show "min_ub a b w \<Longrightarrow> compact w" for w by (metis compact_approx)
  }
qed



context begin
private alias Cb = Rep_compact_basis
definition pd_sup_set :: "'a pd_basis \<Rightarrow> 'a pd_basis \<Rightarrow> 'a compact_basis set"
  where "pd_sup_set A B \<equiv>
\<Union>a \<in> Rep_pd_basis A. \<Union>b \<in> Rep_pd_basis B. {w. min_ub (Cb a) (Cb b) (Cb w)}"

lemma finite_pd_sup_set: "finite (pd_sup_set A B)"
proof -
  {
    fix a b :: "'a compact_basis"
    have c: "compact (Cb a)" "compact (Cb b)" by simp_all
    note min_ub_finite = min_ub_finite[OF c]
    note min_ub_compact = min_ub_compact[OF c]
    have "finite {w. min_ub (Cb a) (Cb b) w}"
      by (auto intro: min_ub_finite)
    moreover have "{w. min_ub (Cb a) (Cb b) (Cb w)} = Abs_compact_basis ` ..."
      using Abs_compact_basis_inverse'[OF min_ub_compact, symmetric]
      by (auto intro: Rep_compact_basis_inverse[symmetric])

    ultimately have "finite {w. min_ub (Rep_compact_basis a) (Rep_compact_basis b) (Rep_compact_basis w)}"
      using finite_imageI by simp
  }
  with finite_Rep_pd_basis
  show ?thesis unfolding pd_sup_set_def by blast
qed

definition "pd_sup A B \<equiv> Abs_pd_basis (pd_sup_set A B)"

lemma pd_sup_rep: "pd_sup_set A B \<noteq> {} \<Longrightarrow> Rep_pd_basis (pd_sup A B) = pd_sup_set A B"
  unfolding pd_sup_def
  using finite_pd_sup_set
    Abs_pd_basis_inverse[unfolded pd_basis_def mem_Collect_eq]
  by blast

lemma min_ub_Cb_def:
  fixes a b z :: "'a::bifinite compact_basis"
  shows "min_ub (Cb a) (Cb b) (Cb z) \<longleftrightarrow> a \<sqsubseteq> z \<and> b \<sqsubseteq> z \<and> (\<forall>w. a \<sqsubseteq> w \<longrightarrow> b \<sqsubseteq> w \<longrightarrow> w \<sqsubseteq> z \<longrightarrow> w = z)"
proof -
  let ?noncompact = "\<forall>w. Cb a \<sqsubseteq> w \<longrightarrow> Cb b \<sqsubseteq> w \<longrightarrow> w \<sqsubseteq> Cb z \<longrightarrow> w = Cb z"
  let ?compact = "\<forall>w. a \<sqsubseteq> w \<longrightarrow> b \<sqsubseteq> w \<longrightarrow> w \<sqsubseteq> z \<longrightarrow> w = z"
  have "?noncompact \<longleftrightarrow> ?compact"
    term type_definition
  proof
    show "?noncompact \<Longrightarrow> ?compact" unfolding compact_le_def
      using type_definition.Rep_inject[OF type_definition_compact_basis]
      by blast
    show "?noncompact" if "?compact"
    proof (intro allI)
      show "Cb a \<sqsubseteq> w \<longrightarrow> Cb b \<sqsubseteq> w \<longrightarrow> w \<sqsubseteq> Cb z \<longrightarrow> w = Cb z" (is "?P w") for w
      proof (induction w rule: compact_basis.principal_induct)
        from Rep_compact_basis'[unfolded compact_def]
        show "adm ?P" by simp
        from that show "?P (Cb w)" for w by auto
      qed
    qed
  qed
  then show ?thesis unfolding min_ub_def by simp
qed

lemma min_ub_below':
  fixes a z :: "'a::bifinite compact_basis"
  shows "a \<sqsubseteq> z \<Longrightarrow> b \<sqsubseteq> z \<Longrightarrow> \<exists>w. min_ub (Cb a) (Cb b) (Cb w) \<and> w \<sqsubseteq> z"
proof -
  assume "a \<sqsubseteq> z" "b \<sqsubseteq> z"
  from this[unfolded compact_le_def] obtain w where 1: "min_ub (Cb a) (Cb b) w" and 2: "w \<sqsubseteq> Cb z"
    using min_ub_below Rep_compact_basis' by blast
  from 1 have "compact w" using Rep_compact_basis' min_ub_compact by blast
  then have "w = Cb (Abs_compact_basis w)" by simp
  with 1 2 compact_le_def show ?thesis by metis
qed

lemma pd_sup_ex: assumes "A \<le>\<sharp> Z" "B \<le>\<sharp> Z"
  shows pd_sup_ne: "pd_sup_set A B \<noteq> {}"
    and pd_sup_le: "pd_sup A B \<le>\<sharp> Z"
proof -
  {
    fix z assume  z: "z \<in> Rep_pd_basis Z"
    from z assms(1)[unfolded upper_le_def] obtain a where a: "a \<in> Rep_pd_basis A" "a \<sqsubseteq> z"
      by blast
    from z assms(2)[unfolded upper_le_def] obtain b where b: "b \<in> Rep_pd_basis B" "b \<sqsubseteq> z"
      by blast
    from a(2) b(2) obtain w where w: "min_ub (Cb a) (Cb b) (Cb w)" "w \<sqsubseteq> z" using min_ub_below'
      by blast
    from a(1) b(1) w(1) have "w \<in> pd_sup_set A B" unfolding pd_sup_set_def by blast
    with w(2) have "\<exists>w \<in> pd_sup_set A B. w \<sqsubseteq> z" by blast
  }
  note sup_finder = this
  from Rep_pd_basis_nonempty obtain z where "z \<in> Rep_pd_basis Z" by blast
  from sup_finder[OF this] show "pd_sup_set A B \<noteq> {}" by blast
  then have "Rep_pd_basis (pd_sup A B) = pd_sup_set A B" by (rule pd_sup_rep)
  with sup_finder show "pd_sup A B \<le>\<sharp> Z" unfolding upper_le_def by blast
qed

lemma pd_sup_ge:
  assumes "pd_sup_set A B \<noteq> {}"
  shows "A \<le>\<sharp> pd_sup A B" "B \<le>\<sharp> pd_sup A B"
  unfolding upper_le_def pd_sup_rep[OF assms] 
    pd_sup_set_def min_ub_Cb_def
  by blast+

end


instantiation upper_pd :: (bifinite) bounded_complete
begin
(* It would be really convenient to have a top in upper PDs but alas *)
instance
proof (rule bounded_complete_finite_compact_joinI')
  fix x y z :: "'a upper_pd"
  assume z: "x \<sqsubseteq> z" "y \<sqsubseteq> z"
  define unp :: "'a upper_pd \<Rightarrow> 'a pd_basis"
    where "unp x = (SOME xb. x = upper_principal xb)" for x
  have unp_p: "compact x \<Longrightarrow> x = upper_principal (unp x)" for x
    unfolding unp_def
    by (drule upper_pd.compact_imp_principal) (rule someI_ex)
  define xb where "xb = unp x"
  define yb where "yb = unp y"
  define zb where "zb = unp z"
  assume "compact x" "compact y" "compact z"
  with upper_pd.compact_imp_principal
  have princ: "x = upper_principal xb" "y = upper_principal yb"
    "z = upper_principal zb" unfolding xb_def yb_def zb_def by (fast intro: unp_p)+
  with z have "xb \<le>\<sharp> zb" "yb \<le>\<sharp> zb" by simp_all 
  from pd_sup_ex[OF this]
  have "xb \<le>\<sharp> pd_sup xb yb" "yb \<le>\<sharp> pd_sup xb yb" "pd_sup xb yb \<le>\<sharp> zb"
    by (auto intro: pd_sup_ge)
  with princ show 
    "x \<sqsubseteq> upper_principal (pd_sup xb yb)"
    "y \<sqsubseteq> upper_principal (pd_sup xb yb)"
    "upper_principal (pd_sup xb yb) \<sqsubseteq> z" by simp_all
qed

lemma upper_meet_eq: "x \<sqinter> y = x \<union>\<sharp> y"
proof (rule below_antisym)
  show "x \<union>\<sharp> y \<sqsubseteq> x \<sqinter> y" using meet_below_iff upper_plus_below1 upper_plus_below2
    by fast
  show "x \<sqinter> y \<sqsubseteq> x \<union>\<sharp> y" using upper_below_plus_iff meet_below1 meet_below2 by fast
qed

end
(*
theorem upper_pd_self_rep: "s = glb {{x}\<sharp> | x. s \<sqsubseteq> {x}\<sharp>}" sorry
*)

instantiation top :: (bounded_complete) bounded_complete
begin

lemma top_is_ub_transfer: "(\<lambda>x. down\<cdot>x) ` A <| down\<cdot>w \<longleftrightarrow> A <| w"
  unfolding is_ub_def by simp

lemma top_is_lub_transfer: "A <<| w \<Longrightarrow> (\<lambda>x. down\<cdot>x) ` A <<| down\<cdot>w"
proof (rule is_lubI)
  show "A <<| w \<Longrightarrow> (\<lambda>x. down\<cdot>x) ` A <| down\<cdot>w" by (auto dest: is_lubD1 simp add: top_is_ub_transfer)
  show "A <<| w \<Longrightarrow> (\<lambda>x. down\<cdot>x) ` A <| u \<Longrightarrow> down\<cdot>w \<sqsubseteq> u" for u
    by (cases u) (auto dest: is_lubD2 simp add: top_is_ub_transfer)
qed

lemma is_ub_Top: "A <| Top"
  by (auto intro: is_ubI)

instance
proof
  fix A :: "'a top set" and b
  show "\<exists>a. A <<| a"
  proof (cases "Top \<in> A")
    case True
    then have "A <<| Top" by (rule top_lub_Top)
    then show ?thesis ..
  next
    case False
    then have 1: "\<forall>x \<in> A. \<exists>y. x = down\<cdot>y" by (metis top_cases)
    define A' where "A' = {y. \<exists>x \<in> A. x = down\<cdot>y}"
    with 1 have 2: "A = (\<lambda>x. down\<cdot>x) ` A'" by fast
    show ?thesis proof (cases "\<exists>w. A' <<| w")
      case True
      then show ?thesis unfolding 2 by (fast intro: top_is_lub_transfer)
    next
      case False
      with ex_bound_ex_lub have 3: "\<nexists>w. A' <| w" by auto
      then have 4: "A <| w \<Longrightarrow> w = Top" for w
        unfolding 2 using top_is_ub_transfer by (cases w) auto
      then have "A <<| Top" by (auto intro: is_lubI simp add: is_ub_Top)
      then show ?thesis ..
    qed
  qed
qed

lemmas top_is_lub = ex_bound_ex_lub[OF is_ub_Top]
lemmas top_lub = ex_bound_lub[OF is_ub_Top]

lemmas top_join_is_lub = join_is_lub[OF below_Top below_Top]

lemma [simp]: "(a :: 'a top) \<Up> b" by (auto intro: joinableI below_Top)

end

subsection \<open>Joins: auxiliary lemmas\<close>

lemma bottom_joinable: "\<bottom> \<Up> (y::'a::bounded_complete)"
  by (auto simp add: joinable_def)

lemma cfun_arg_joinable:
  fixes a b :: "'a::bounded_complete" and f :: "'a \<rightarrow> 'b::bounded_complete"
  assumes "a \<Up> b" shows "f\<cdot>a \<Up> f\<cdot>b"
  using assms unfolding joinable_def by (blast intro: monofun_cfun_arg)

text \<open>Deflations lie below @{term ID}, so any two are joinable.\<close>

lemma deflation_joinable:
  assumes "deflation p" and "deflation q" shows "p \<Up> q"
  by (rule joinableI[OF deflation.below_ID[OF assms(1)] deflation.below_ID[OF assms(2)]])

lemma compact_join:
  fixes x y :: "'a::bounded_complete"
  assumes x: "compact x" and y: "compact y" and xy: "x \<Up> y"
  shows "compact (x \<squnion> y)"
proof (rule compactI2)
  fix Y :: "nat \<Rightarrow> 'a" assume Y: "chain Y" and le: "x \<squnion> y \<sqsubseteq> (\<Squnion>i. Y i)"
  from le joinableD[OF xy] have "x \<sqsubseteq> (\<Squnion>i. Y i)" "y \<sqsubseteq> (\<Squnion>i. Y i)"
    by (blast intro: below_trans)+
  then obtain i j where "x \<sqsubseteq> Y i" "y \<sqsubseteq> Y j"
    using compactD2[OF x Y] compactD2[OF y Y] by blast
  then have "x \<sqsubseteq> Y (max i j)" "y \<sqsubseteq> Y (max i j)"
    using chain_mono[OF Y] by (blast intro: below_trans max.cobounded1 max.cobounded2)+
  then show "\<exists>i. x \<squnion> y \<sqsubseteq> Y i" by (blast intro: join_belowI)
qed

lemma insert_join_is_lub:
  fixes S :: "'a::bounded_complete set"
  assumes Sl: "S <<| l" and j: "z \<Up> l"
  shows "insert z S <<| z \<squnion> l"
proof (rule is_lubI)
  show "insert z S <| z \<squnion> l"
  proof (rule is_ubI)
    fix w assume w: "w \<in> insert z S"
    show "w \<sqsubseteq> z \<squnion> l"
    proof (cases "w = z")
      case True then show ?thesis by (simp add: joinableD(1)[OF j])
    next
      case False with w have "w \<in> S" by simp
      with is_lubD1[OF Sl] have "w \<sqsubseteq> l" by (rule is_ubD)
      also have "l \<sqsubseteq> z \<squnion> l" by (rule joinableD(2)[OF j])
      finally show ?thesis .
    qed
  qed
next
  fix u assume "insert z S <| u"
  then have zu: "z \<sqsubseteq> u" and Su: "S <| u" by (auto simp: is_ub_insert)
  from Sl Su have "l \<sqsubseteq> u" by (rule is_lubD2)
  with zu show "z \<squnion> l \<sqsubseteq> u" by (rule join_belowI)
qed

end
