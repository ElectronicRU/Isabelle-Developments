theory Algebraic_Lattice imports Lattice_Complete begin

section ‹Algebraic lattices are bifinite›

text ‹If every element of a complete lattice is the lub of the compacts below it, and the compacts
  are enumerated by ‹c›, then truncating to the lub of the first ‹n› compacts below the argument is
  an approximation chain.›

definition approx_alg :: "(nat ⇒ 'a::lattice_complete) ⇒ nat ⇒ 'a → 'a" where
  "approx_alg c n = (Λ x. lub {c i |i. i ≤ n ∧ c i ⊑ x})"

lemma lattice_lub_mono: "S ⊆ T ⟹ lub (S :: 'a::lattice_complete set) ⊑ lub T"
  by (rule lattice_lub_least) (auto simp: is_ub_def intro: lattice_lub_upper)

lemma common_chain_index:
  fixes Y :: "nat ⇒ 'a::cpo" and c :: "nat ⇒ 'a" and n :: nat
  assumes Y: "chain Y" and c: "⋀i. compact (c i)"
  shows "∃J. ∀i≤n. c i ⊑ (⨆j. Y j) ⟶ c i ⊑ Y J"
proof (induct n)
  case 0
  obtain j where "c 0 ⊑ (⨆j. Y j) ⟶ c 0 ⊑ Y j" using compactD2[OF c Y] by blast
  then show ?case by blast
next
  case (Suc n)
  then obtain J where J: "∀i≤n. c i ⊑ (⨆j. Y j) ⟶ c i ⊑ Y J" by blast
  obtain j where j: "c (Suc n) ⊑ (⨆j. Y j) ⟶ c (Suc n) ⊑ Y j" using compactD2[OF c Y] by blast
  have JJ: "Y J ⊑ Y (max J j)" and jJ: "Y j ⊑ Y (max J j)" by (simp_all add: chain_mono[OF Y])
  show ?case
  proof (intro exI[of _ "max J j"] allI impI)
    fix i assume i: "i ≤ Suc n" "c i ⊑ (⨆j. Y j)"
    show "c i ⊑ Y (max J j)"
    proof (cases "i ≤ n")
      case True with J i JJ show ?thesis by (blast intro: below_trans)
    next
      case False with i have "i = Suc n" by simp
      with j i jJ show ?thesis by (blast intro: below_trans)
    qed
  qed
qed

lemma cont_approx_alg:
  fixes c :: "nat ⇒ 'a::lattice_complete"
  assumes c: "⋀i. compact (c i)"
  shows "cont (λx. lub {c i |i. i ≤ n ∧ c i ⊑ x})" (is "cont ?f")
proof (rule contI2)
  show "monofun ?f" by (rule monofunI, rule lattice_lub_mono) (auto intro: below_trans)
  fix Y :: "nat ⇒ 'a" assume Y: "chain Y" and fY: "chain (λi. ?f (Y i))"
  obtain J where J: "∀i≤n. c i ⊑ (⨆j. Y j) ⟶ c i ⊑ Y J"
    using common_chain_index[where c = c and n = n, OF Y c] by blast
  have "?f (⨆j. Y j) ⊑ ?f (Y J)" by (rule lattice_lub_mono) (use J in auto)
  also have "… ⊑ (⨆i. ?f (Y i))" by (rule is_ub_thelub[OF fY])
  finally show "?f (⨆i. Y i) ⊑ (⨆i. ?f (Y i))" .
qed

lemma approx_alg_beta:
  "(⋀i. compact (c i)) ⟹ approx_alg c n⋅x = lub {c i |i. i ≤ n ∧ c i ⊑ x}"
  unfolding approx_alg_def by (simp add: cont_approx_alg)

lemma approx_chain_algebraic:
  fixes c :: "nat ⇒ 'a::lattice_complete"
  assumes comp: "range c = {k. compact k}" and alg: "⋀x :: 'a. x = lub {k. compact k ∧ k ⊑ x}"
  shows "approx_chain (approx_alg c)"
proof -
  have c: "⋀i. compact (c i)" using comp by blast
  have ch: "chain (approx_alg c)"
    by (rule chainI, rule cfun_belowI) (simp add: approx_alg_beta[OF c], rule lattice_lub_mono, auto)
  have below: "approx_alg c n⋅x ⊑ x" for n and x :: 'a
    by (simp add: approx_alg_beta[OF c], rule lattice_lub_least) (auto simp: is_ub_def)
  show ?thesis
  proof
    show "chain (approx_alg c)" by (fact ch)
    show "(⨆i. approx_alg c i) = ID"
    proof (rule cfun_eqI)
      fix x :: 'a
      have "x ⊑ (⨆i. approx_alg c i⋅x)"
      proof (subst alg[of x], rule lattice_lub_least, rule is_ubI)
        fix k assume "k ∈ {k. compact k ∧ k ⊑ x}"
        then obtain i where ki: "k = c i" and kx: "k ⊑ x" using comp by blast
        have "k ⊑ approx_alg c i⋅x"
          by (simp add: approx_alg_beta[OF c], rule lattice_lub_upper) (use ki kx in blast)
        also have "… ⊑ (⨆i. approx_alg c i⋅x)" by (rule is_ub_thelub[OF ch2ch_Rep_cfunL[OF ch]])
        finally show "k ⊑ (⨆i. approx_alg c i⋅x)" .
      qed
      moreover have "(⨆i. approx_alg c i⋅x) ⊑ x" by (rule lub_below[OF ch2ch_Rep_cfunL[OF ch] below])
      ultimately show "(⨆i. approx_alg c i)⋅x = ID⋅x"
        by (simp add: contlub_cfun_fun[OF ch] below_antisym)
    qed
    show "approx_alg c i⋅(approx_alg c i⋅x) = approx_alg c i⋅x" for i and x :: 'a
    proof -
      have "{c j |j. j ≤ i ∧ c j ⊑ approx_alg c i⋅x} = {c j |j. j ≤ i ∧ c j ⊑ x}"
        using below[of i x]
        by (auto intro: below_trans simp: approx_alg_beta[OF c] intro!: lattice_lub_upper)
      then show ?thesis by (simp only: approx_alg_beta[OF c])
    qed
    show "approx_alg c i⋅x ⊑ x" for i and x :: 'a by (rule below)
    show "finite {x. approx_alg c i⋅x = x}" for i
    proof -
      have "{x. approx_alg c i⋅x = x} ⊆ lub ` Pow (c ` {..i})"
      proof
        fix x assume "x ∈ {x. approx_alg c i⋅x = x}"
        then have "x = lub {c j |j. j ≤ i ∧ c j ⊑ x}" by (simp add: approx_alg_beta[OF c])
        moreover have "{c j |j. j ≤ i ∧ c j ⊑ x} ∈ Pow (c ` {..i})" by auto
        ultimately show "x ∈ lub ` Pow (c ` {..i})" by blast
      qed
      then show ?thesis by (rule finite_subset) simp
    qed
  qed
qed

lemma bifinite_algebraic_lattice:
  assumes comp: "∃c :: nat ⇒ 'a::lattice_complete. range c = {k. compact k}"
    and alg: "⋀x :: 'a. x = lub {k. compact k ∧ k ⊑ x}"
  shows "OFCLASS('a, bifinite_class)"
proof
  obtain c :: "nat ⇒ 'a" where "range c = {k. compact k}" using comp by blast
  then show "∃a :: nat ⇒ 'a → 'a. approx_chain a" by (blast intro: approx_chain_algebraic alg)
qed

end
