theory Kleene_Logic
  imports HOLCF
begin

default_sort type

section \<open>Parallel connectives\<close>

text \<open>Kleene's strong connectives on @{typ tr}: falsity decides a conjunction and truth a
  disjunction, whatever the other side, so they are parallel rather than sequential.\<close>

lemma cont2cont_chfin2:
  fixes f :: "'a::chfin \<Rightarrow> 'b::chfin \<Rightarrow> 'c::cpo"
  assumes "\<And>x. monofun (f x)" and "\<And>y. monofun (\<lambda>x. f x y)"
  shows "cont (\<lambda>x. \<Lambda> y. f x y)"
  by (intro cont2cont_LAM chfindom_monofun2cont assms)

lemma beta_chfin2:
  fixes f :: "'a::chfin \<Rightarrow> 'b::chfin \<Rightarrow> 'c::cpo"
  assumes "\<And>x. monofun (f x)" and "\<And>y. monofun (\<lambda>x. f x y)"
  shows "(\<Lambda> x y. f x y)\<cdot>a\<cdot>b = f a b"
  by (simp add: cont2cont_chfin2 assms chfindom_monofun2cont)

definition pand :: "tr \<rightarrow> tr \<rightarrow> tr" where
  "pand = (\<Lambda> x y. if x = FF \<or> y = FF then FF else if x = TT \<and> y = TT then TT else \<bottom>)"

definition por :: "tr \<rightarrow> tr \<rightarrow> tr" where
  "por = (\<Lambda> x y. if x = TT \<or> y = TT then TT else if x = FF \<and> y = FF then FF else \<bottom>)"

lemma pand_apply: "pand\<cdot>x\<cdot>y = (if x = FF \<or> y = FF then FF else if x = TT \<and> y = TT then TT else \<bottom>)"
  unfolding pand_def by (rule beta_chfin2; rule monofunI; auto simp: flat_below_iff)

lemma por_apply: "por\<cdot>x\<cdot>y = (if x = TT \<or> y = TT then TT else if x = FF \<and> y = FF then FF else \<bottom>)"
  unfolding por_def by (rule beta_chfin2; rule monofunI; auto simp: flat_below_iff)

lemma pand_simps [simp]:
  "pand\<cdot>FF\<cdot>y = FF" "pand\<cdot>x\<cdot>FF = FF" "pand\<cdot>TT\<cdot>y = y" "pand\<cdot>x\<cdot>TT = x" "pand\<cdot>\<bottom>\<cdot>\<bottom> = \<bottom>"
  by (simp_all add: pand_apply) (metis Exh_tr)+

lemma por_simps [simp]:
  "por\<cdot>TT\<cdot>y = TT" "por\<cdot>x\<cdot>TT = TT" "por\<cdot>FF\<cdot>y = y" "por\<cdot>x\<cdot>FF = x" "por\<cdot>\<bottom>\<cdot>\<bottom> = \<bottom>"
  by (simp_all add: por_apply) (metis Exh_tr)+

lemma pand_TT_iff: "pand\<cdot>x\<cdot>y = TT \<longleftrightarrow> x = TT \<and> y = TT"
  and pand_FF_iff: "pand\<cdot>x\<cdot>y = FF \<longleftrightarrow> x = FF \<or> y = FF"
  and por_TT_iff: "por\<cdot>x\<cdot>y = TT \<longleftrightarrow> x = TT \<or> y = TT"
  and por_FF_iff: "por\<cdot>x\<cdot>y = FF \<longleftrightarrow> x = FF \<and> y = FF"
  by (auto simp: pand_apply por_apply)

lemma pand_commute: "pand\<cdot>x\<cdot>y = pand\<cdot>y\<cdot>x"
  and por_commute: "por\<cdot>x\<cdot>y = por\<cdot>y\<cdot>x"
  by (auto simp: pand_apply por_apply)

lemma pand_assoc: "pand\<cdot>(pand\<cdot>x\<cdot>y)\<cdot>z = pand\<cdot>x\<cdot>(pand\<cdot>y\<cdot>z)"
  and por_assoc: "por\<cdot>(por\<cdot>x\<cdot>y)\<cdot>z = por\<cdot>x\<cdot>(por\<cdot>y\<cdot>z)"
  by (cases x rule: trE; cases y rule: trE; cases z rule: trE; simp)+

lemma neg_pand: "neg\<cdot>(pand\<cdot>x\<cdot>y) = por\<cdot>(neg\<cdot>x)\<cdot>(neg\<cdot>y)"
  and neg_por: "neg\<cdot>(por\<cdot>x\<cdot>y) = pand\<cdot>(neg\<cdot>x)\<cdot>(neg\<cdot>y)"
  by (cases x rule: trE; cases y rule: trE; simp)+

section \<open>The Kleene existential over an up-set\<close>

text \<open>Three-valued existential quantification of a \<open>tr\<close>-valued predicate over the elements above
  a bound: true if the predicate is true somewhere above the bound, false if it is false everywhere
  there, and undefined otherwise.  It is monotone in the predicate.  It is continuous in the
  predicate as long as falsity is preserved upwards: the up-set is then refuted by refuting the
  bound alone, so a single approximant suffices.  Monotone predicates are such, and so is the
  existential as a function of its bound, which is neither monotone nor antitone there (raising the
  bound loses witnesses for truth and gains falsity).\<close>

definition kleene_ex :: "'a::po \<Rightarrow> ('a \<Rightarrow> tr) \<Rightarrow> tr" where
  "kleene_ex a P = (if \<exists>x. a \<sqsubseteq> x \<and> P x = TT then TT else if \<forall>x. a \<sqsubseteq> x \<longrightarrow> P x = FF then FF else \<bottom>)"

syntax "_kleene_ex" :: "pttrn \<Rightarrow> 'a \<Rightarrow> tr \<Rightarrow> tr"  ("(3\<exists>\<^sub>K _ \<sqsupseteq> _./ _)" [0, 0, 10] 10)
syntax_consts "_kleene_ex" \<rightleftharpoons> kleene_ex
translations "\<exists>\<^sub>K x \<sqsupseteq> a. t" \<rightleftharpoons> "CONST kleene_ex a (\<lambda>x. t)"

lemma kleene_ex_TT_iff: "kleene_ex a P = TT \<longleftrightarrow> (\<exists>x. a \<sqsubseteq> x \<and> P x = TT)"
  by (simp add: kleene_ex_def)

lemma kleene_ex_FF_iff: "kleene_ex a P = FF \<longleftrightarrow> (\<forall>x. a \<sqsubseteq> x \<longrightarrow> P x = FF)"
  by (auto simp: kleene_ex_def)

lemma kleene_ex_bottom_iff:
  "kleene_ex a P = \<bottom> \<longleftrightarrow> \<not> (\<exists>x. a \<sqsubseteq> x \<and> P x = TT) \<and> \<not> (\<forall>x. a \<sqsubseteq> x \<longrightarrow> P x = FF)"
  by (simp add: kleene_ex_def)

lemma kleene_ex_const [simp]: "(\<exists>\<^sub>K x \<sqsupseteq> a. t) = t"
  by (cases t rule: trE) (auto simp: kleene_ex_def)

lemma kleene_ex_mono: "(\<And>x. P x \<sqsubseteq> Q x) \<Longrightarrow> kleene_ex a P \<sqsubseteq> kleene_ex a Q"
  unfolding kleene_ex_def by (auto simp: flat_below_iff) (metis dist_eq_tr flat_below_iff)+

lemma monofun_kleene_ex: "monofun (kleene_ex a)"
  by (rule monofunI) (simp add: kleene_ex_mono fun_below_iff)

text \<open>Nested existentials collapse.\<close>

lemma kleene_ex_kleene_ex: "(\<exists>\<^sub>K y \<sqsupseteq> b. \<exists>\<^sub>K x \<sqsupseteq> y. P x) = (\<exists>\<^sub>K x \<sqsupseteq> b. P x)"
  unfolding kleene_ex_def by (auto intro: below_trans)

subsection \<open>Predicates preserving falsity upwards\<close>

definition FF_upward :: "('a::po \<Rightarrow> tr) \<Rightarrow> bool" where
  "FF_upward P \<longleftrightarrow> (\<forall>x y. P x = FF \<longrightarrow> x \<sqsubseteq> y \<longrightarrow> P y = FF)"

lemma FF_upwardD: "FF_upward P \<Longrightarrow> P x = FF \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> P y = FF"
  unfolding FF_upward_def by blast

lemma FF_upward_monofun: "monofun P \<Longrightarrow> FF_upward P"
  unfolding FF_upward_def by (metis flat_eq monofunE dist_eq_tr(2))

lemma FF_upward_cfun: "FF_upward (Rep_cfun f)"
  by (rule FF_upward_monofun) (rule monofun_Rep_cfun2)

lemma FF_upward_const: "FF_upward (\<lambda>x. t)"
  unfolding FF_upward_def by simp

lemma FF_upward_kleene_ex: "FF_upward (\<lambda>a. kleene_ex a P)"
  unfolding FF_upward_def kleene_ex_FF_iff by (blast intro: below_trans)

lemma kleene_ex_FF_iff_upward: "FF_upward P \<Longrightarrow> kleene_ex a P = FF \<longleftrightarrow> P a = FF"
  unfolding kleene_ex_FF_iff by (blast dest: FF_upwardD)

lemma kleene_ex_above: "FF_upward P \<Longrightarrow> P a \<sqsubseteq> kleene_ex a P"
  by (cases "P a" rule: trE) (auto simp: kleene_ex_TT_iff kleene_ex_FF_iff_upward)

lemma lub_tr_eq: "chain (Y :: nat \<Rightarrow> tr) \<Longrightarrow> \<exists>i. (\<Squnion>i. Y i) = Y i"
  using chfin maxinch_is_thelub by blast

lemma FF_upward_pand: "FF_upward P \<Longrightarrow> FF_upward Q \<Longrightarrow> FF_upward (\<lambda>x. pand\<cdot>(P x)\<cdot>(Q x))"
  and FF_upward_por: "FF_upward P \<Longrightarrow> FF_upward Q \<Longrightarrow> FF_upward (\<lambda>x. por\<cdot>(P x)\<cdot>(Q x))"
  unfolding FF_upward_def pand_FF_iff por_FF_iff by blast+

theorem cont_kleene_ex:
  assumes F: "cont F" and up: "\<And>y. FF_upward (F y)"
  shows "cont (\<lambda>y. kleene_ex a (F y))"
proof (rule contI2)
  show "monofun (\<lambda>y. kleene_ex a (F y))"
    by (rule monofunI) (rule kleene_ex_mono, simp add: fun_belowD cont2monofunE[OF F])
next
  fix Y :: "nat \<Rightarrow> 'a" assume Y: "chain Y"
  assume K: "chain (\<lambda>i. kleene_ex a (F (Y i)))"
  have at: "\<exists>i. F (\<Squnion>i. Y i) x = F (Y i) x" for x
  proof -
    have ch: "chain (\<lambda>i. F (Y i))" using ch2ch_cont[OF F Y] .
    have "F (\<Squnion>i. Y i) x = (\<Squnion>i. F (Y i) x)"
      by (simp add: cont2contlubE[OF F Y] lub_fun[OF ch])
    then show ?thesis using lub_tr_eq[OF ch2ch_fun[OF ch]] by metis
  qed
  show "kleene_ex a (F (\<Squnion>i. Y i)) \<sqsubseteq> (\<Squnion>i. kleene_ex a (F (Y i)))"
  proof (cases "kleene_ex a (F (\<Squnion>i. Y i))" rule: trE)
    case TT
    then obtain x i where "a \<sqsubseteq> x" and "F (Y i) x = TT" using at unfolding kleene_ex_TT_iff by metis
    then have "kleene_ex a (F (Y i)) = TT" unfolding kleene_ex_TT_iff by blast
    then show ?thesis using TT is_ub_thelub[OF K, of i] by simp
  next
    case FF
    then obtain i where "F (Y i) a = FF" using at unfolding kleene_ex_FF_iff_upward[OF up] by metis
    then have "kleene_ex a (F (Y i)) = FF" unfolding kleene_ex_FF_iff_upward[OF up] .
    then show ?thesis using FF is_ub_thelub[OF K, of i] by simp
  qed simp
qed

end
