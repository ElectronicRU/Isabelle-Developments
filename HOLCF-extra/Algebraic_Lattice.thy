theory Algebraic_Lattice imports Lattice_Complete begin

section \<open>Algebraic lattices are bifinite\<close>

text \<open>If every element of a complete lattice is the lub of the compacts below it, and the compacts
  are enumerated by \<open>c\<close>, then truncating to the lub of the first \<open>n\<close> compacts below the argument is
  an approximation chain.\<close>

definition approx_alg :: "(nat \<Rightarrow> 'a::lattice_complete) \<Rightarrow> nat \<Rightarrow> 'a \<rightarrow> 'a" where
  "approx_alg c n = (\<Lambda> x. lub {c i |i. i \<le> n \<and> c i \<sqsubseteq> x})"

lemma lattice_lub_mono: "S \<subseteq> T \<Longrightarrow> lub (S :: 'a::lattice_complete set) \<sqsubseteq> lub T"
  by (rule lattice_lub_least) (auto simp: is_ub_def intro: lattice_lub_upper)

lemma common_chain_index:
  fixes Y :: "nat \<Rightarrow> 'a::cpo" and c :: "nat \<Rightarrow> 'a" and n :: nat
  assumes Y: "chain Y" and c: "\<And>i. compact (c i)"
  shows "\<exists>J. \<forall>i\<le>n. c i \<sqsubseteq> (\<Squnion>j. Y j) \<longrightarrow> c i \<sqsubseteq> Y J"
proof (induct n)
  case 0
  obtain j where "c 0 \<sqsubseteq> (\<Squnion>j. Y j) \<longrightarrow> c 0 \<sqsubseteq> Y j" using compactD2[OF c Y] by blast
  then show ?case by blast
next
  case (Suc n)
  then obtain J where J: "\<forall>i\<le>n. c i \<sqsubseteq> (\<Squnion>j. Y j) \<longrightarrow> c i \<sqsubseteq> Y J" by blast
  obtain j where j: "c (Suc n) \<sqsubseteq> (\<Squnion>j. Y j) \<longrightarrow> c (Suc n) \<sqsubseteq> Y j" using compactD2[OF c Y] by blast
  have JJ: "Y J \<sqsubseteq> Y (max J j)" and jJ: "Y j \<sqsubseteq> Y (max J j)" by (simp_all add: chain_mono[OF Y])
  show ?case
  proof (intro exI[of _ "max J j"] allI impI)
    fix i assume i: "i \<le> Suc n" "c i \<sqsubseteq> (\<Squnion>j. Y j)"
    show "c i \<sqsubseteq> Y (max J j)"
    proof (cases "i \<le> n")
      case True with J i JJ show ?thesis by (blast intro: below_trans)
    next
      case False with i have "i = Suc n" by simp
      with j i jJ show ?thesis by (blast intro: below_trans)
    qed
  qed
qed

lemma cont_approx_alg:
  fixes c :: "nat \<Rightarrow> 'a::lattice_complete"
  assumes c: "\<And>i. compact (c i)"
  shows "cont (\<lambda>x. lub {c i |i. i \<le> n \<and> c i \<sqsubseteq> x})" (is "cont ?f")
proof (rule contI2)
  show "monofun ?f" by (rule monofunI, rule lattice_lub_mono) (auto intro: below_trans)
  fix Y :: "nat \<Rightarrow> 'a" assume Y: "chain Y" and fY: "chain (\<lambda>i. ?f (Y i))"
  obtain J where J: "\<forall>i\<le>n. c i \<sqsubseteq> (\<Squnion>j. Y j) \<longrightarrow> c i \<sqsubseteq> Y J"
    using common_chain_index[where c = c and n = n, OF Y c] by blast
  have "?f (\<Squnion>j. Y j) \<sqsubseteq> ?f (Y J)" by (rule lattice_lub_mono) (use J in auto)
  also have "\<dots> \<sqsubseteq> (\<Squnion>i. ?f (Y i))" by (rule is_ub_thelub[OF fY])
  finally show "?f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. ?f (Y i))" .
qed

lemma approx_alg_beta:
  "(\<And>i. compact (c i)) \<Longrightarrow> approx_alg c n\<cdot>x = lub {c i |i. i \<le> n \<and> c i \<sqsubseteq> x}"
  unfolding approx_alg_def by (simp add: cont_approx_alg)

lemma approx_chain_algebraic:
  fixes c :: "nat \<Rightarrow> 'a::lattice_complete"
  assumes comp: "range c = {k. compact k}" and alg: "\<And>x :: 'a. x = lub {k. compact k \<and> k \<sqsubseteq> x}"
  shows "approx_chain (approx_alg c)"
proof -
  have c: "\<And>i. compact (c i)" using comp by blast
  have ch: "chain (approx_alg c)"
    by (rule chainI, rule cfun_belowI) (simp add: approx_alg_beta[OF c], rule lattice_lub_mono, auto)
  have below: "approx_alg c n\<cdot>x \<sqsubseteq> x" for n and x :: 'a
    by (simp add: approx_alg_beta[OF c], rule lattice_lub_least) (auto simp: is_ub_def)
  show ?thesis
  proof
    show "chain (approx_alg c)" by (fact ch)
    show "(\<Squnion>i. approx_alg c i) = ID"
    proof (rule cfun_eqI)
      fix x :: 'a
      have "x \<sqsubseteq> (\<Squnion>i. approx_alg c i\<cdot>x)"
      proof (subst alg[of x], rule lattice_lub_least, rule is_ubI)
        fix k assume "k \<in> {k. compact k \<and> k \<sqsubseteq> x}"
        then obtain i where ki: "k = c i" and kx: "k \<sqsubseteq> x" using comp by blast
        have "k \<sqsubseteq> approx_alg c i\<cdot>x"
          by (simp add: approx_alg_beta[OF c], rule lattice_lub_upper) (use ki kx in blast)
        also have "\<dots> \<sqsubseteq> (\<Squnion>i. approx_alg c i\<cdot>x)" by (rule is_ub_thelub[OF ch2ch_Rep_cfunL[OF ch]])
        finally show "k \<sqsubseteq> (\<Squnion>i. approx_alg c i\<cdot>x)" .
      qed
      moreover have "(\<Squnion>i. approx_alg c i\<cdot>x) \<sqsubseteq> x" by (rule lub_below[OF ch2ch_Rep_cfunL[OF ch] below])
      ultimately show "(\<Squnion>i. approx_alg c i)\<cdot>x = ID\<cdot>x"
        by (simp add: contlub_cfun_fun[OF ch] below_antisym)
    qed
    show "approx_alg c i\<cdot>(approx_alg c i\<cdot>x) = approx_alg c i\<cdot>x" for i and x :: 'a
    proof -
      have "{c j |j. j \<le> i \<and> c j \<sqsubseteq> approx_alg c i\<cdot>x} = {c j |j. j \<le> i \<and> c j \<sqsubseteq> x}"
        using below[of i x]
        by (auto intro: below_trans simp: approx_alg_beta[OF c] intro!: lattice_lub_upper)
      then show ?thesis by (simp only: approx_alg_beta[OF c])
    qed
    show "approx_alg c i\<cdot>x \<sqsubseteq> x" for i and x :: 'a by (rule below)
    show "finite {x. approx_alg c i\<cdot>x = x}" for i
    proof -
      have "{x. approx_alg c i\<cdot>x = x} \<subseteq> lub ` Pow (c ` {..i})"
      proof
        fix x assume "x \<in> {x. approx_alg c i\<cdot>x = x}"
        then have "x = lub {c j |j. j \<le> i \<and> c j \<sqsubseteq> x}" by (simp add: approx_alg_beta[OF c])
        moreover have "{c j |j. j \<le> i \<and> c j \<sqsubseteq> x} \<in> Pow (c ` {..i})" by auto
        ultimately show "x \<in> lub ` Pow (c ` {..i})" by blast
      qed
      then show ?thesis by (rule finite_subset) simp
    qed
  qed
qed

lemma bifinite_algebraic_lattice:
  assumes comp: "\<exists>c :: nat \<Rightarrow> 'a::lattice_complete. range c = {k. compact k}"
    and alg: "\<And>x :: 'a. x = lub {k. compact k \<and> k \<sqsubseteq> x}"
  shows "OFCLASS('a, bifinite_class)"
proof
  obtain c :: "nat \<Rightarrow> 'a" where "range c = {k. compact k}" using comp by blast
  then show "\<exists>a :: nat \<Rightarrow> 'a \<rightarrow> 'a. approx_chain a" by (blast intro: approx_chain_algebraic alg)
qed

end
