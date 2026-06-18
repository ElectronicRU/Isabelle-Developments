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
proof -
  from is_glb[OF assms] obtain s where 1: "is_glb S s" .
  have 2: "a = s" if "is_glb S a" for a
  proof -
    from 1 that assms have "x \<sqsubseteq> a \<longleftrightarrow> x \<sqsubseteq> s" for x
      by (simp add: is_glb_def)
    from this[of a] this[of s] below_refl below_antisym show ?thesis by simp
  qed
  from 1 2 show ?thesis 
    unfolding glb_def by (rule theI)
qed

lemma glb_below: "x \<in> S \<Longrightarrow> glb S \<sqsubseteq> x"
  by (auto intro: glb is_glb_below)

lemma glb_greatest: "S \<noteq> {} \<Longrightarrow> (\<forall>x \<in> S. b \<sqsubseteq> x) \<Longrightarrow> b \<sqsubseteq> glb S"
  by (auto intro: glb is_glb_greatest)

lemma glb_below_iff: "S \<noteq> {} \<Longrightarrow> (b \<sqsubseteq> glb S) = (\<forall>x \<in> S. b \<sqsubseteq> x)"
  by (drule glb) (simp add: is_glb_def)

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

lemma joinableD[simp]: "a \<Up> b \<Longrightarrow> a \<sqsubseteq> a \<squnion> b" "a \<Up> b \<Longrightarrow> b \<sqsubseteq> a \<squnion> b"
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

sublocale semilattice_meet: semilattice_inf meet below below_strict
  by unfold_locales (fact meet_below1 meet_below2 meet_greatest)+

lemma join_mono1: "c \<squnion> b \<sqsubseteq> a \<squnion> b" if "a \<Up> b" "c \<sqsubseteq> a"
proof -
  from that have "c \<sqsubseteq> a \<squnion> b" by (auto intro: below_trans)
  also from that have "b \<sqsubseteq> a \<squnion> b" by auto
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
  by (rule semilattice_meet.inf_absorb1)

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
  from assms show "a \<sqinter> c \<Up> b" by (auto intro: joinable_mono1)
  then show "a \<sqinter> c \<Up> b \<sqinter> d" by (auto intro: joinable_mono2)
  from assms show "a \<Up> b \<sqinter> d" by (auto intro: joinable_mono2)
qed (auto intro: joinable_mono1 joinable_mono2 joinableD[OF assms] joinableI)

end

class distributive_cpo = bounded_complete +
  assumes meet_join_distrib: "a \<Up> b \<Longrightarrow> c \<sqinter> (a \<squnion> b) = (c \<sqinter> a) \<squnion> (c \<sqinter> b)"
begin

lemma meet_join_distrib2: "a \<Up> b \<Longrightarrow> (a \<squnion> b) \<sqinter> c = (a \<sqinter> c) \<squnion> (b \<sqinter> c)"
  by (simp add: meet_join_distrib meet_sym)

lemma join_meet_distrib: "a \<squnion> (b \<sqinter> c) = (a \<squnion> b) \<sqinter> (a \<squnion> c)" if "a \<Up> b" "a \<Up> c"
proof -
  have d1: "(a \<squnion> b) \<sqinter> c = (a \<sqinter> c) \<squnion> (b \<sqinter> c)"
    by (auto intro: meet_join_distrib2 \<open>a \<Up> b\<close>)
  have "a \<squnion> (b \<sqinter> c) = (a \<squnion> (a \<sqinter> c)) \<squnion> (b \<sqinter> c)"
    by (simp add: join_absorb_meet2)
  also have "... = a \<squnion> ((a \<sqinter> c) \<squnion> (b \<sqinter> c))"
    by (rule join_assoc, simp_all add: that d1[symmetric])
  also have "... = a \<squnion> ((a \<squnion> b)\<sqinter> c)"
    by (simp add: d1)
  also have "... = ((a \<squnion> b) \<sqinter> a) \<squnion> ((a \<squnion> b) \<sqinter> c)"
    by (simp add: that)
  also have "... = (a \<squnion> b) \<sqinter> (a \<squnion> c)"
    by (simp add: that meet_join_distrib meet_sym)
  finally show ?thesis .
qed

end

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

lemma bounded_complete_compact_to_general_aux:
  assumes compactI: "\<And>a b c::'a::bifinite. \<lbrakk> compact a; compact b; a \<sqsubseteq> c; b \<sqsubseteq> c \<rbrakk> \<Longrightarrow> \<exists>z. {a, b} <<| z"
    and c: "(a::'a) \<sqsubseteq> c" "b \<sqsubseteq> c"
  shows "\<exists>z. {a, b} <<| z"
proof -
  obtain A where A: "chain A" "\<forall>i. compact (A i)" "a = (\<Squnion>i. A i)"
    by (rule obtain_compact_chain)
  obtain B where B: "chain B" "\<forall>j. compact (B j)" "b = (\<Squnion>j. B j)"
    by (rule obtain_compact_chain)
  from A B c lub_below_iff have "A i \<sqsubseteq> c" "B i \<sqsubseteq> c" for i
    by blast+
  with A(2) B(2) compactI obtain Z where "{A i, B j} <<| Z i j" for i j
    by meson
  with A have "{a, B j} <<| (\<Squnion>i. Z i j)" for j
    by (blast intro: bin_join_chain1)
  then have "{B j, a} <<| (\<Squnion>i. Z i j)" for j
    by (simp add: bin_join_ex_symm)
  with B have "{b, a} <<| (\<Squnion>j. (\<Squnion>i. Z i j))"
    by (blast intro: bin_join_chain1)
  then show "\<exists>z. {a, b} <<| z"
    by (auto simp add: bin_join_ex_symm)
qed

lemma bounded_complete_finite_compact_joinI:
  assumes "\<And>a b c::'a::bifinite. \<lbrakk> compact a; compact b; a \<sqsubseteq> c; b \<sqsubseteq> c \<rbrakk> \<Longrightarrow> \<exists>z. {a, b} <<| z"
  shows "OFCLASS('a, bounded_complete_class)"
proof
  have "a \<sqsubseteq> c \<Longrightarrow> b \<sqsubseteq> c \<Longrightarrow> \<exists>z. {a, b} <<| z" for a b c :: 'a
    by (rule bounded_complete_compact_to_general_aux[OF assms])
  then have joinI: "a \<sqsubseteq> c \<Longrightarrow> b \<sqsubseteq> c \<Longrightarrow> {a, b} <<| a \<squnion> b" for a b c :: 'a
    unfolding join_def using is_lub_lub by blast
  have finite_is_lub: "B <| z \<Longrightarrow> \<exists>b. B <<| b" if "finite B"
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
  from bifinite obtain approx :: "nat \<Rightarrow> 'a \<rightarrow> 'a" where "approx_chain approx" ..
  then interpret approx_chain approx .

  fix F and z :: 'a assume *: "F <| z"

  define cF where "cF \<equiv> \<lambda>i. (\<lambda>x. approx i\<cdot>x) ` F"
  have bound: "cF i <| x" if "F <| x" for i x
  proof (rule is_ubI)
    fix y assume "y \<in> cF i"
    from this[unfolded cF_def] obtain y0
      where 1: "y = approx i\<cdot>y0"
        and 2: "y0 \<in> F"
      by blast
    from approx_below 1 have "y \<sqsubseteq> y0" by simp
    also have "y0 \<sqsubseteq> x" using is_ubD[OF that 2] .
    finally show "y \<sqsubseteq> x" .
  qed

  have cF_finite: "finite (cF i)" for i
    unfolding cF_def
    apply (rule finite_subset)
     apply (rule image_mono)
     apply (rule subset_UNIV)
    apply (fact finite_range_approx)
    .

  from * have cF_bounded: "cF i <| z" for i by (rule bound)
  from cF_finite cF_bounded have cF_lub: "cF i <<| lub (cF i)" for i
    using finite_is_lub is_lub_lub by blast
  with approx_lub_family cF_def
  show "\<exists>w. F <<| w" by blast
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
  by unfold_locales (auto intro: joinableD[OF assms] join_belowI)

lemma (in bounded_complete) bdd_above_iff:
"preorder.bdd_above (\<sqsubseteq>) A \<longleftrightarrow> (\<exists>a. A <| a)"
  unfolding preorder.bdd_above_def[OF below_order.preorder_axioms] is_ub_def
  by fast

lemma (in bounded_complete) cclattice:
  assumes "\<And>a b. a \<Up> b"
  shows "class.conditionally_complete_lattice glb lub meet below below_strict join"
proof
qed (auto intro: joinableD[OF assms] join_belowI glb_below glb_greatest
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
      apply (intro subset_antisym image_subsetI subsetI image_eqI)
        apply (rule Rep_compact_basis_inverse[symmetric])
      apply simp
      using Abs_compact_basis_inverse'[OF min_ub_compact, symmetric] apply simp
      .

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

end
