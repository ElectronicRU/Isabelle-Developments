theory Congruence
  imports HOLCF
begin

default_sort pcpo

section \<open>Continuous congruences (functional-dependence relations)\<close>

text \<open>
  A \<^emph>\<open>continuous congruence\<close> on a cpo \<^typ>\<open>'a\<close> is a relation \<^term>\<open>R\<close> that is transitive,
  refines the cpo order \<^term>\<open>(\<sqsubseteq>)\<close>, and is admissible (Scott-closed) in each argument: a
  coarser ``below''.  The motivating instance is the kernel order \<^term>\<open>\<lambda>x y. f\<cdot>x \<sqsubseteq> f\<cdot>y\<close> of a
  continuous map; a bigger relation identifies more points, i.e.\ is \<^emph>\<open>coarser\<close>.

  These are used only as \<^emph>\<open>predicates\<close>, to state functional dependence between levels of
  detail; levels of detail themselves are syntactic dimension sets (see the frame
  development).  We deliberately do not build a type of congruences: the only reason to do so
  would be meets, and finitely flat-generated congruences are not closed under them.
\<close>

subsection \<open>Continuous congruences (admissible refining preorders)\<close>

locale is_cong =
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes trans: "R x y \<Longrightarrow> R y z \<Longrightarrow> R x z"
    and belowD: "x \<sqsubseteq> y \<Longrightarrow> R x y"
    and adm1: "adm (\<lambda>x. R x y)"
    and adm2: "adm (\<lambda>y. R x y)"
begin
lemmas axioms = trans belowD adm1 adm2
end

lemma (in is_cong) refl: "R x x"
  by (auto simp: trans belowD)

lemma is_cong_top: "is_cong top"
  by (simp add: is_cong_def)

lemma is_cong_below: "is_cong (\<lambda>x y. x \<sqsubseteq> y)"
  by (auto simp: is_cong_def intro: below_trans adm_below cont_id cont_const)

lemma is_cong_Inter:
  assumes "\<And>i. i \<in> I \<Longrightarrow> is_cong (R i)"
  shows "is_cong (\<lambda>x y. \<forall>i\<in>I. R i x y)"
proof
  show "\<forall>i \<in> I. R i x y \<Longrightarrow> \<forall>i \<in> I. R i y z \<Longrightarrow> \<forall>i \<in> I. R i x z" for x y z
    using assms[THEN is_cong.trans] by blast
  show "x \<sqsubseteq> y \<Longrightarrow> \<forall>i \<in> I. R i x y" for x y
    using assms[THEN is_cong.belowD] by blast
  show "adm (\<lambda>x. \<forall>i \<in> I. R i x y)" for y
    using assms[THEN is_cong.adm1] adm_ball[of I] by force 
  show "adm (\<lambda>y. \<forall>i \<in> I. R i x y)" for x
    using assms[THEN is_cong.adm2] adm_ball[of I] by force
qed

lemma Inf_iff: "Inf \<R> = (\<lambda>x y. \<forall>R \<in> \<R>. R x y)"
  by fast

corollary is_cong_Inf: "(\<And>R. R \<in> \<R> \<Longrightarrow> is_cong R) \<Longrightarrow> is_cong (Inf \<R>)"
  unfolding Inf_iff
  using is_cong_Inter[of "\<R>" "(\<lambda>x. x)"] .

lemma inf2_def: "inf R S = (\<lambda>x y. R x y \<and> S x y)"
  by auto

lemma is_cong_inf2:
  assumes "is_cong R" "is_cong S" shows "is_cong (inf R S)"
  unfolding inf2_def
proof
  from assms show "R x y \<and> S x y \<Longrightarrow> R y z \<and> S y z \<Longrightarrow> R x z \<and> S x z" for x y z
    by (blast dest: is_cong.trans)
  from assms show "x \<sqsubseteq> y \<Longrightarrow> R x y \<and> S x y" for x y
    by (blast dest: is_cong.belowD)
  from assms show "adm (\<lambda>x. R x y \<and> S x y)" for y
    by (intro adm_conj) (blast intro: assms dest: is_cong.adm1)+
  from assms show "adm (\<lambda>y. R x y \<and> S x y)" for x
    by (intro adm_conj) (blast intro: assms dest: is_cong.adm2)+
qed

subsection \<open>The generated congruence (least cong above a relation)\<close>

definition gen :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)" where
  "gen B = (\<lambda>x y. \<forall>R. is_cong R \<longrightarrow> (\<forall>u v. B u v \<longrightarrow> R u v) \<longrightarrow> R x y)"

lemma is_cong_gen: "is_cong (gen B)"
proof -
  have *: "gen B = (\<lambda>x y. \<forall>R\<in>{R. is_cong R \<and> (\<forall>u v. B u v \<longrightarrow> R u v)}. R x y)"
    by (auto simp: gen_def fun_eq_iff)
  show ?thesis unfolding * by (rule is_cong_Inter) auto
qed

lemma gen_upper: "B x y \<Longrightarrow> gen B x y"
  by (auto simp: gen_def)

lemma gen_least: "is_cong R \<Longrightarrow> (\<And>u v. B u v \<Longrightarrow> R u v) \<Longrightarrow> gen B x y \<Longrightarrow> R x y"
  by (auto simp: gen_def)


lemma map_is_cong: assumes "is_cong R" "cont f" shows "is_cong (inv_imagep R f)"
  unfolding inv_imagep_def
proof (standard)
  from assms(1) show "R (f x) (f y) \<Longrightarrow> R (f y) (f z) \<Longrightarrow> R (f x) (f z)" for x y z
    by (rule is_cong.trans)
  from assms(1)[THEN is_cong.belowD] assms(2)[THEN cont2monofunE]
  show "x \<sqsubseteq> y \<Longrightarrow> R (f x) (f y)" for x y
    by presburger
  from assms(2) assms(1)[THEN is_cong.adm1]
  show "adm (\<lambda>x. R (f x) (f y))" for y by (rule adm_subst)
  from assms(2) assms(1)[THEN is_cong.adm2]
  show "adm (\<lambda>y. R (f x) (f y))" for x by (rule adm_subst)
qed


subsection \<open>Flat LODs (the generators)\<close>

text \<open>A flat congruence is one whose quotient has height at most 1: a bottom class of
  ``undefined'' points (each \<open>R\<close>-below everything) and an antichain of value classes above.
  These arise exactly from continuous maps into flat domains, and generate the LOD frame.\<close>

locale is_flat_cong = is_cong +
  assumes height1: "R x y \<Longrightarrow> R y x \<or> (\<forall>z. R x z)"

lemma is_flat_cong_eq_on:
  fixes f :: "'a \<rightarrow> 'b::flat"
  shows "is_flat_cong (\<lambda>x y. f\<cdot>x \<sqsubseteq> f\<cdot>y)"
proof unfold_locales
  show "f\<cdot>x \<sqsubseteq> f\<cdot>y \<Longrightarrow> f\<cdot>y \<sqsubseteq> f\<cdot>z \<Longrightarrow> f\<cdot>x \<sqsubseteq> f\<cdot>z" for x y z by (rule below_trans)
  show "x \<sqsubseteq> y \<Longrightarrow> f\<cdot>x \<sqsubseteq> f\<cdot>y" for x y by (rule monofun_cfun_arg)
  show "adm (\<lambda>x. f\<cdot>x \<sqsubseteq> f\<cdot>y)" for y by simp
  show "adm (\<lambda>y. f\<cdot>x \<sqsubseteq> f\<cdot>y)" for x by simp
  show "f\<cdot>x \<sqsubseteq> f\<cdot>y \<Longrightarrow> f\<cdot>y \<sqsubseteq> f\<cdot>x \<or> (\<forall>z. f\<cdot>x \<sqsubseteq> f\<cdot>z)" for x y
    by (metis ax_flat minimal)
qed

text \<open>The family generated by the flats under arbitrary cong-joins, i.e.\ boolean-level
  intersections (\<^term>\<open>Inf\<close> at the predicate level = \<^const>\<open>Sup\<close> at the cong level).\<close>

definition is_flat_gen :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "is_flat_gen R \<longleftrightarrow> (\<exists>\<F>. (\<forall>f\<in>\<F>. is_flat_cong f) \<and> R = Inf \<F>)"

lemma is_flat_gen_flat: "is_flat_cong f \<Longrightarrow> is_flat_gen f"
  unfolding is_flat_gen_def by (rule exI[of _ "{f}"]) simp

text \<open>Meet of two flats is flat: the generated congruence stays height at most 1.  No induction,
  no distributivity of @{typ 'a} — the symmetric companion @{term U} is squeezed in between.\<close>

lemma is_flat_cong_meet:
  fixes f g :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes f: "is_flat_cong f" and g: "is_flat_cong g"
  shows "is_flat_cong (gen (sup f g))"
proof -
  let ?R = "gen (sup f g)"
  have R: "is_cong ?R" by (rule is_cong_gen)
  have cf: "is_cong f" using f by (simp add: is_flat_cong_def)
  note fh = is_flat_cong.height1[OF f]
  note gh = is_flat_cong.height1[OF g]
  have sup1: "?R a b" if "f a b" for a b
    using that by (intro gen_upper) simp
  have sup2: "?R a b" if "g a b" for a b
    using that by (intro gen_upper) simp
  define U :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    where "U = (\<lambda>x y. (\<forall>z. ?R x z) \<or> (?R x y \<and> ?R y x))"
  have Ucong: "is_cong U"
  proof unfold_locales
    fix x y z assume xy: "U x y" and yz: "U y z"
    show "U x z" unfolding U_def
      using xy[unfolded U_def] yz[unfolded U_def] is_cong.trans[OF R] by metis
  next
    fix x y :: "'a" assume "x \<sqsubseteq> y"
    hence fxy: "f x y" by (rule is_cong.belowD[OF cf])
    hence Rxy: "?R x y" by (rule sup1)
    from fh[OF fxy] show "U x y" unfolding U_def
    proof (elim disjE)
      assume "f y x" hence "?R y x" by (rule sup1)
      with Rxy show "(\<forall>z. ?R x z) \<or> (?R x y \<and> ?R y x)" by blast
    next
      assume "\<forall>z. f x z" hence "\<forall>z. ?R x z" using sup1 by blast
      thus "(\<forall>z. ?R x z) \<or> (?R x y \<and> ?R y x)" by blast
    qed
  next
    fix y show "adm (\<lambda>x. U x y)" unfolding U_def
      by (intro adm_disj adm_all adm_conj is_cong.adm1[OF R] is_cong.adm2[OF R])
  next
    fix x show "adm (\<lambda>y. U x y)" unfolding U_def
      by (intro adm_disj adm_const adm_conj is_cong.adm2[OF R] is_cong.adm1[OF R])
  qed
  have supU: "U u v" if huv: "sup f g u v" for u v
    unfolding U_def using sup1 sup2 fh gh
    by (metis sup1 fh sup2 gh that sup_apply sup_bool_def)
  have RU: "?R x y \<Longrightarrow> U x y" for x y
    by (rule gen_least[OF Ucong supU])
  show "is_flat_cong ?R"
  proof unfold_locales
    show "?R x y \<Longrightarrow> ?R y z \<Longrightarrow> ?R x z" for x y z by (rule is_cong.trans[OF R])
    show "x \<sqsubseteq> y \<Longrightarrow> ?R x y" for x y by (rule is_cong.belowD[OF R])
    show "adm (\<lambda>x. ?R x y)" for y by (rule is_cong.adm1[OF R])
    show "adm (\<lambda>y. ?R x y)" for x by (rule is_cong.adm2[OF R])
    show "?R x y \<Longrightarrow> ?R y x \<or> (\<forall>z. ?R x z)" for x y
      using RU unfolding U_def by blast
  qed
qed

lemma gen_inf: "gen R = Inf {z. z \<ge> R \<and> is_cong z}"
  unfolding gen_def
  by blast

end
