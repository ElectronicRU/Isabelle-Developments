theory DI imports Filter_Sum begin

section ‹dI-domains›

text ‹A ∗‹dI-domain› (Berry) is a distributive bifinite domain with property I: every compact
  element has finitely many elements below it.  Everything below a compact element is then
  compact itself.›

class dI = bifinite + distributive_cpo +
  assumes finite_below_compact: "compact k ⟹ finite {x. x ⊑ k}"

lemma compact_below_compact:
  fixes x :: "'a::dI"
  assumes k: "compact k" and xk: "x ⊑ k"
  shows "compact x"
proof -
  obtain a :: "nat ⇒ 'a → 'a" where a: "approx_chain a" using bifinite by blast
  interpret approx_chain a by (fact a)
  let ?Y = "λi. a i⋅x"
  have ch: "chain ?Y" by (rule ch2ch_Rep_cfunL[OF chain_approx])
  have "range ?Y ⊆ {y. y ⊑ k}" using approx_below xk by (blast intro: below_trans)
  then have "finite (range ?Y)" by (rule finite_subset) (rule finite_below_compact[OF k])
  then obtain i where "max_in_chain i ?Y"
    using finite_range_imp_finch[OF ch] unfolding finite_chain_def by blast
  then have l: "(⨆j. ?Y j) = ?Y i" using maxinch_is_thelub[OF ch] by blast
  have "(⨆j. ?Y j) = x" by (simp add: contlub_cfun_fun[OF chain_approx, symmetric])
  with l have "x = a i⋅x" by simp
  then show ?thesis by (metis compact_approx)
qed

subsection ‹Transfer along isomorphisms›

text ‹Domain types are dI-domains when their representation is: the derivation machinery for
  map functions does not apply, since property I is not preserved by recursion.›

lemma dI_iso:
  fixes abs :: "'r::dI → 't::{bifinite, distributive_cpo}" and rep
  assumes "iso abs rep" shows "OFCLASS('t, dI_class)"
proof (intro_classes)
  fix k :: 't assume "compact k"
  then have c: "compact (rep⋅k)" by (rule iso.compact_rep[OF assms])
  have "{x. x ⊑ k} ⊆ (λy. abs⋅y) ` {y. y ⊑ rep⋅k}"
  proof
    fix x assume "x ∈ {x. x ⊑ k}"
    then have "rep⋅x ⊑ rep⋅k" by (simp add: monofun_cfun_arg)
    moreover have "x = abs⋅(rep⋅x)" by (simp add: iso.rep_iso[OF assms])
    ultimately show "x ∈ (λy. abs⋅y) ` {y. y ⊑ rep⋅k}" by blast
  qed
  then show "finite {x. x ⊑ k}"
    by (rule finite_subset) (rule finite_imageI[OF finite_below_compact[OF c]])
qed

subsection ‹Instances›

text ‹Flat domains have at most two elements below anything.›

instance lift :: (countable) dI
proof
  fix k :: "'a lift"
  show "finite {x. x ⊑ k}"
    by (rule finite_subset[of _ "{⊥, k}"]) (auto dest: flat_eq)
qed

text ‹Lifting adds one element below everything.›

instance u :: (dI) dI
proof
  fix k :: "'a u" assume k: "compact k"
  show "finite {x. x ⊑ k}"
  proof (cases k rule: upE)
    case bottom
    then show ?thesis by simp
  next
    case (up a)
    with k have a: "compact a" by simp
    have "{x. x ⊑ k} ⊆ insert ⊥ ((λz. up⋅z) ` {z. z ⊑ a})"
    proof
      fix x assume "x ∈ {x. x ⊑ k}"
      with up show "x ∈ insert ⊥ ((λz. up⋅z) ` {z. z ⊑ a})" by (cases x rule: upE) auto
    qed
    then show ?thesis
      by (rule finite_subset) (simp add: finite_below_compact[OF a])
  qed
qed

text ‹Below an injection lie the injections of what lies below its argument.›

instance ssum :: (dI, dI) dI
proof
  fix k :: "'a ⊕ 'b" assume k: "compact k"
  show "finite {x. x ⊑ k}"
  proof (cases k rule: ssumE)
    case bottom
    then show ?thesis by simp
  next
    case (sinl a)
    with k have a: "compact a" by simp
    have "{x. x ⊑ k} ⊆ (λz. sinl⋅z) ` {z. z ⊑ a}"
    proof
      fix x assume "x ∈ {x. x ⊑ k}"
      with sinl show "x ∈ (λz. sinl⋅z) ` {z. z ⊑ a}"
        by (cases x rule: ssumE) (auto intro: image_eqI[where x = ⊥])
    qed
    then show ?thesis by (rule finite_subset) (simp add: finite_below_compact[OF a])
  next
    case (sinr b)
    with k have b: "compact b" by simp
    have "{x. x ⊑ k} ⊆ (λz. sinr⋅z) ` {z. z ⊑ b}"
    proof
      fix x assume "x ∈ {x. x ⊑ k}"
      with sinr show "x ∈ (λz. sinr⋅z) ` {z. z ⊑ b}"
        by (cases x rule: ssumE) (auto intro: image_eqI[where x = ⊥])
    qed
    then show ?thesis by (rule finite_subset) (simp add: finite_below_compact[OF b])
  qed
qed

text ‹Below a pair lie the pairs of what lies below its components.›

instance prod :: (dI, dI) dI
proof
  fix k :: "'a × 'b" assume k: "compact k"
  obtain a b where ab: "k = (a, b)" by (cases k)
  with k have a: "compact a" and b: "compact b" by simp_all
  have "{x. x ⊑ k} ⊆ {z. z ⊑ a} × {z. z ⊑ b}"
    using ab by (auto simp: below_prod_def)
  then show "finite {x. x ⊑ k}"
    by (rule finite_subset) (simp add: finite_below_compact[OF a] finite_below_compact[OF b])
qed

text ‹Strict products are distributive over filter-sum factors (see ‹Filter_Sum›).›

instance sprod :: ("{filter_sum, dI}", "{filter_sum, dI}") dI
proof
  fix k :: "'a ⊗ 'b" assume k: "compact k"
  show "finite {x. x ⊑ k}"
  proof (cases k rule: sprodE)
    case bottom
    then show ?thesis by simp
  next
    case (spair a b)
    with k have a: "compact a" and b: "compact b" by (simp_all add: compact_spair_iff)
    have "{x. x ⊑ k} ⊆ (λ(y, z). (:y, z:)) ` ({y. y ⊑ a} × {z. z ⊑ b})"
    proof
      fix x assume x: "x ∈ {x. x ⊑ k}"
      show "x ∈ (λ(y, z). (:y, z:)) ` ({y. y ⊑ a} × {z. z ⊑ b})"
      proof (cases x rule: sprodE)
        case bottom
        then show ?thesis
          by (intro image_eqI[where x = "(⊥ :: 'a, ⊥ :: 'b)"]) (simp_all add: mem_Times_iff)
      next
        case (spair c d)
        with x ‹k = (:a, b:)› have "c ⊑ a" "d ⊑ b" by (simp_all add: spair_below)
        with spair show ?thesis by (intro image_eqI[where x = "(c, d)"]) simp_all
      qed
    qed
    then show ?thesis
      by (rule finite_subset) (simp add: finite_below_compact[OF a] finite_below_compact[OF b])
  qed
qed

end
