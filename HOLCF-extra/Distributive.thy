theory Distributive imports Bounded_Complete begin

section \<open>Distributive bounded-complete cpos\<close>

text \<open>A bounded-complete cpo is \<^emph>\<open>distributive\<close> when binary meet distributes over joins of
  joinable pairs.\<close>

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

class scott_domain = "domain" + distributive_cpo

section \<open>Instances\<close>

text \<open>Two joinable elements of a flat domain are comparable, so distributivity is a case split.\<close>

instance flat \<subseteq> distributive_cpo
proof
  fix a b c :: 'a assume ab: "a \<Up> b"
  have mb: "x \<sqinter> \<bottom> = \<bottom>" for x :: 'a by (simp add: meet_sym meet_absorbI)
  from joinableD[OF ab] have "a = \<bottom> \<or> b = \<bottom> \<or> a = b"
    by (metis ax_flat)
  then show "c \<sqinter> (a \<squnion> b) = c \<sqinter> a \<squnion> (c \<sqinter> b)"
    by (elim disjE) (simp_all add: mb join_bottom)
qed

instance "fun" :: (type, distributive_cpo) distributive_cpo
proof
  fix a b c :: "'a \<Rightarrow> 'b"
  assume ab: "a \<Up> b"
  have ptw: "a x \<Up> b x" for x
  proof -
    from ab obtain z where "a \<sqsubseteq> z" "b \<sqsubseteq> z" unfolding joinable_def by blast
    thus "a x \<Up> b x" by (meson fun_belowD joinableI)
  qed
  have cab: "(c \<sqinter> a) \<Up> (c \<sqinter> b)" by (rule joinableI[OF meet_below1 meet_below1])
  have "c \<sqinter> (a \<squnion> b) = (\<lambda>x. c x \<sqinter> (a x \<squnion> b x))"
    using ab by (simp add: fun_meet fun_join)
  also have "... = (\<lambda>x. (c x \<sqinter> a x) \<squnion> (c x \<sqinter> b x))"
    using ptw by (simp add: meet_join_distrib)
  also have "... = (c \<sqinter> a) \<squnion> (c \<sqinter> b)"
    using cab by (simp add: fun_meet fun_join)
  finally show "c \<sqinter> (a \<squnion> b) = (c \<sqinter> a) \<squnion> (c \<sqinter> b)" .
qed

instance u :: (distributive_cpo) distributive_cpo
proof
  fix a b c :: "'a u" assume ab: "a \<Up> b"
  show "c \<sqinter> (a \<squnion> b) = c \<sqinter> a \<squnion> (c \<sqinter> b)"
  proof (cases a; cases b; cases c)
    fix a' b' c' assume *: "a = up\<cdot>a'" "b = up\<cdot>b'" "c = up\<cdot>c'"
    with ab have a'b': "a' \<Up> b'" by simp
    have "c' \<sqinter> a' \<Up> c' \<sqinter> b'" by (rule joinableI[OF meet_below1 meet_below1])
    with * a'b' show ?thesis by (simp add: up_join meet_join_distrib)
  qed simp_all
qed

instance ssum :: (distributive_cpo, distributive_cpo) distributive_cpo
proof
  fix a b c :: "'a \<oplus> 'b" assume ab: "a \<Up> b"
  have ml: "x \<sqinter> x' \<Up> x \<sqinter> x''" for x x' x'' :: 'a by (rule joinableI[OF meet_below1 meet_below1])
  have mr: "y \<sqinter> y' \<Up> y \<sqinter> y''" for y y' y'' :: 'b by (rule joinableI[OF meet_below1 meet_below1])
  show "c \<sqinter> (a \<squnion> b) = c \<sqinter> a \<squnion> (c \<sqinter> b)"
    using ab by (cases a; cases b; cases c)
      (simp_all add: sinl_join sinr_join meet_join_distrib ml mr)
qed

instance prod :: (distributive_cpo, distributive_cpo) distributive_cpo
proof
  fix a b c :: "'a \<times> 'b" assume ab: "a \<Up> b"
  then have c: "fst a \<Up> fst b" "snd a \<Up> snd b" by (simp_all add: prod_joinable_iff)
  have "c \<sqinter> a \<Up> c \<sqinter> b" by (rule joinableI[OF meet_below1 meet_below1])
  with ab c show "c \<sqinter> (a \<squnion> b) = c \<sqinter> a \<squnion> (c \<sqinter> b)"
    by (simp add: prod_meet prod_join meet_join_distrib)
qed

section \<open>Continuity of meet, and distributivity from compacts\<close>

text \<open>In a bifinite bounded-complete domain binary meet is continuous: this is the
  \<open>approximants\<close> observation — a compact below @{term \<open>(\<Squnion>i. X i) \<sqinter> y\<close>} already lies
  below some @{term \<open>X i \<sqinter> y\<close>}.\<close>

lemma approximants_meet:
  "approximants ((x::'a::{bifinite, bounded_complete}) \<sqinter> y) = approximants x \<inter> approximants y"
  unfolding approximants_def by (auto simp add: meet_below_iff)

lemma cont_meet_arg: "cont (\<lambda>x::'a::{bifinite, bounded_complete}. x \<sqinter> y)"
proof -
  have mono: "monofun (\<lambda>x::'a. x \<sqinter> y)"
  proof (rule monofunI)
    fix a b :: 'a assume "a \<sqsubseteq> b"
    have "a \<sqinter> y \<sqsubseteq> b" using meet_below1[of a y] \<open>a \<sqsubseteq> b\<close> by (rule below_trans)
    moreover have "a \<sqinter> y \<sqsubseteq> y" by (rule meet_below2)
    ultimately show "a \<sqinter> y \<sqsubseteq> b \<sqinter> y" by (rule meet_greatest)
  qed
  show ?thesis
  proof (rule contI2[OF mono])
    fix X :: "nat \<Rightarrow> 'a" assume X: "chain X"
    assume chXy: "chain (\<lambda>i. X i \<sqinter> y)"
    show "(\<Squnion>i. X i) \<sqinter> y \<sqsubseteq> (\<Squnion>i. X i \<sqinter> y)"
      by (rule compact_basis.belowI) (simp add: compact_basis.rep_lub X chXy approximants_meet)
  qed
qed

lemma cont_meet_arg2: "cont (\<lambda>y::'a::{bifinite, bounded_complete}. x \<sqinter> y)"
  using cont_meet_arg[of x] by (simp add: meet_sym)

lemma cont2cont_meet [simp, cont2cont]:
  fixes f g :: "'b::cpo \<Rightarrow> 'a::{bifinite, bounded_complete}"
  assumes contf: "cont f" and contg: "cont g" shows "cont (\<lambda>x. f x \<sqinter> g x)"
  by (rule cont_apply [OF contg cont_meet_arg2 cont_compose [OF cont_meet_arg contf]])

lemma meet_lub_chains:
  fixes X Y :: "nat \<Rightarrow> 'a::{bifinite, bounded_complete}"
  assumes "chain X" "chain Y" shows "(\<Squnion>i. X i) \<sqinter> (\<Squnion>i. Y i) = (\<Squnion>i. X i \<sqinter> Y i)"
proof -
  have c: "cont (\<lambda>p::'a \<times> 'a. fst p \<sqinter> snd p)" by simp
  have ch: "chain (\<lambda>i. (X i, Y i))" using assms by (simp add: chain_def)
  have "(\<Squnion>i. (X i, Y i)) = ((\<Squnion>i. X i), (\<Squnion>i. Y i))" using assms by (rule lub_Pair)
  with cont2contlubE[OF c ch] show ?thesis by simp
qed

text \<open>Joins of pointwise joinable chains: the lubs are joinable, and joining commutes with lubs.\<close>

lemma lub_join_chains:
  fixes X Y :: "nat \<Rightarrow> 'a::bounded_complete"
  assumes X: "chain X" and Y: "chain Y" and j: "\<And>i. X i \<Up> Y i"
  shows "chain (\<lambda>i. X i \<squnion> Y i)" "(\<Squnion>i. X i) \<Up> (\<Squnion>i. Y i)"
    "(\<Squnion>i. X i \<squnion> Y i) = (\<Squnion>i. X i) \<squnion> (\<Squnion>i. Y i)"
proof -
  have XY: "X i \<sqsubseteq> (\<Squnion>i. X i)" "Y i \<sqsubseteq> (\<Squnion>i. Y i)" for i using X Y by (simp_all add: is_ub_thelub)
  show ch: "chain (\<lambda>i. X i \<squnion> Y i)"
  proof (rule chainI)
    fix i
    have "X i \<sqsubseteq> X (Suc i) \<squnion> Y (Suc i)" "Y i \<sqsubseteq> X (Suc i) \<squnion> Y (Suc i)"
      using chainE[OF X, of i] chainE[OF Y, of i] joinableD[OF j[of "Suc i"]]
      by (blast intro: below_trans)+
    then show "X i \<squnion> Y i \<sqsubseteq> X (Suc i) \<squnion> Y (Suc i)" by (rule join_belowI)
  qed
  have "(\<Squnion>i. X i) \<sqsubseteq> (\<Squnion>i. X i \<squnion> Y i)" "(\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. X i \<squnion> Y i)"
    using joinableD[OF j] by (blast intro: lub_mono X Y ch)+
  then show jl: "(\<Squnion>i. X i) \<Up> (\<Squnion>i. Y i)" by (rule joinableI)
  show "(\<Squnion>i. X i \<squnion> Y i) = (\<Squnion>i. X i) \<squnion> (\<Squnion>i. Y i)"
  proof (rule below_antisym)
    show "(\<Squnion>i. X i \<squnion> Y i) \<sqsubseteq> (\<Squnion>i. X i) \<squnion> (\<Squnion>i. Y i)"
    proof (rule lub_below[OF ch])
      fix i
      show "X i \<squnion> Y i \<sqsubseteq> (\<Squnion>i. X i) \<squnion> (\<Squnion>i. Y i)"
        using XY joinableD[OF jl] by (blast intro: join_belowI below_trans)
    qed
    show "(\<Squnion>i. X i) \<squnion> (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. X i \<squnion> Y i)"
      using \<open>(\<Squnion>i. X i) \<sqsubseteq> _\<close> \<open>(\<Squnion>i. Y i) \<sqsubseteq> _\<close> by (rule join_belowI)
  qed
qed

text \<open>So distributivity of a bifinite bounded-complete domain need only be checked on compacts.\<close>

lemma distributive_cpo_compactI:
  assumes "\<And>a b c::'a::{bifinite, bounded_complete}. compact a \<Longrightarrow> compact b \<Longrightarrow> compact c \<Longrightarrow>
    a \<Up> b \<Longrightarrow> c \<sqinter> (a \<squnion> b) = c \<sqinter> a \<squnion> (c \<sqinter> b)"
  shows "OFCLASS('a, distributive_cpo_class)"
proof intro_classes
  fix a b c :: 'a assume ab: "a \<Up> b"
  obtain approx :: "nat \<Rightarrow> 'a \<rightarrow> 'a" where "approx_chain approx" using bifinite by blast
  then interpret approx_chain approx .
  have lub: "(\<Squnion>i. approx i\<cdot>x) = x" for x
    by (simp add: contlub_cfun_fun[OF chain_approx, symmetric])
  have ch: "chain (\<lambda>i. approx i\<cdot>x)" for x by (rule ch2ch_Rep_cfunL[OF chain_approx])
  have mch: "chain X \<Longrightarrow> chain Y \<Longrightarrow> chain (\<lambda>i. X i \<sqinter> Y i)" for X Y :: "nat \<Rightarrow> 'a"
    by (rule chainI, rule meet_greatest)
      (blast intro: below_trans[OF meet_below1 chainE] below_trans[OF meet_below2 chainE])+
  define A where "A = (\<lambda>i. approx i\<cdot>a)"
  define B where "B = (\<lambda>i. approx i\<cdot>b)"
  define C where "C = (\<lambda>i. approx i\<cdot>c)"
  have chs: "chain A" "chain B" "chain C" unfolding A_def B_def C_def by (rule ch)+
  have AB: "A i \<Up> B i" for i
  proof -
    have "approx i\<cdot>a \<sqsubseteq> approx i\<cdot>(a \<squnion> b)" "approx i\<cdot>b \<sqsubseteq> approx i\<cdot>(a \<squnion> b)"
      by (rule monofun_cfun_arg[OF joinableD(1)[OF ab]],
          rule monofun_cfun_arg[OF joinableD(2)[OF ab]])
    then show ?thesis unfolding A_def B_def by (rule joinableI)
  qed
  have CAB: "C i \<sqinter> A i \<Up> C i \<sqinter> B i" for i by (rule joinableI[OF meet_below1 meet_below1])
  have ca: "(\<Squnion>i. C i \<sqinter> A i) = c \<sqinter> a" and cb: "(\<Squnion>i. C i \<sqinter> B i) = c \<sqinter> b"
    using meet_lub_chains[OF chs(3,1)] meet_lub_chains[OF chs(3,2)]
    by (simp_all add: A_def B_def C_def lub)
  have "c \<sqinter> (a \<squnion> b) = (\<Squnion>i. C i) \<sqinter> ((\<Squnion>i. A i) \<squnion> (\<Squnion>i. B i))" by (simp add: A_def B_def C_def lub)
  also have "\<dots> = (\<Squnion>i. C i) \<sqinter> (\<Squnion>i. A i \<squnion> B i)" by (simp add: lub_join_chains(3)[OF chs(1,2) AB])
  also have "\<dots> = (\<Squnion>i. C i \<sqinter> (A i \<squnion> B i))"
    by (rule meet_lub_chains[OF chs(3) lub_join_chains(1)[OF chs(1,2) AB]])
  also have "\<dots> = (\<Squnion>i. (C i \<sqinter> A i) \<squnion> (C i \<sqinter> B i))"
    using AB by (simp add: A_def B_def C_def assms)
  also have "\<dots> = (\<Squnion>i. C i \<sqinter> A i) \<squnion> (\<Squnion>i. C i \<sqinter> B i)"
    by (rule lub_join_chains(3)[OF mch[OF chs(3,1)] mch[OF chs(3,2)] CAB])
  also have "\<dots> = c \<sqinter> a \<squnion> (c \<sqinter> b)" by (simp only: ca cb)
  finally show "c \<sqinter> (a \<squnion> b) = c \<sqinter> a \<squnion> (c \<sqinter> b)" .
qed

end
