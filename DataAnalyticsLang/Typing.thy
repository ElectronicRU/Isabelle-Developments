theory Typing imports Main begin

unbundle lattice_syntax

section \<open>Typing terms that obey lattice subtyping\<close>
locale typing =
  fixes of_type :: "'val \<Rightarrow> 'typ::{complete_lattice} \<Rightarrow> bool"
  assumes of_type_mono: "t \<le> t' \<Longrightarrow> of_type v t \<Longrightarrow> of_type v t'"
      and of_type_Inf: "(\<And> t. t \<in> ts \<Longrightarrow> of_type v t) \<Longrightarrow> of_type v (\<Sqinter> ts)"

begin

definition principal_type :: "'val \<Rightarrow> 'typ" where "principal_type v = \<Sqinter> {t. of_type v t}"

theorem principal_type_is_principal: "of_type v t \<longleftrightarrow> principal_type v \<le> t"
proof
  fix v t
  assume "of_type v t"
  then show "principal_type v \<le> t" by (simp add: Inf_lower principal_type_def)
next
  fix v t
  assume 0: "principal_type v \<le> t"
  then show "of_type v t" using of_type_Inf of_type_mono principal_type_def 0 by fastforce
qed

lemma principal_type_elim[elim]: "principal_type v \<le> t \<Longrightarrow> of_type v t"
  using principal_type_is_principal by fast

theorem Sup_principal_type: "\<Squnion>(principal_type ` V) = \<Sqinter>{t. \<forall>v \<in> V. of_type v t}"
proof -
  have "\<Squnion>(principal_type ` V) = \<Sqinter>{t. \<forall> v \<in> V. principal_type v \<le> t}" by (simp add: Sup_eq_Inf)
  also have "... = \<Sqinter>{t. \<forall> v \<in> V. of_type v t}" using principal_type_is_principal by simp
  finally show ?thesis .
qed

interpretation typing_self: typing
  where of_type = \<open>(\<le>)::('typ::{complete_lattice} \<Rightarrow> 'typ \<Rightarrow> bool)\<close>
  by (auto intro!: typing.intro simp: Inf_greatest)
end

section \<open>Typing judgments\<close>

datatype 't judg = Of 't | Empty

instantiation judg :: (ord) ord begin

definition less_eq_judg where
"x \<le> y \<equiv> case x of Empty \<Rightarrow> True | Of x \<Rightarrow> (case y of Empty \<Rightarrow> False | Of y \<Rightarrow> x \<le> y)"

definition
  "(x::'a judg) < y \<equiv> x \<le> y \<and> x \<noteq> y"

lemma less_eq_empty: "Empty \<le> x" by (auto simp add: less_eq_judg_def)
lemma less_eq_judg_Of: "x \<le> y \<longleftrightarrow> Of x \<le> Of y" by (auto simp add: less_eq_judg_def)

instance ..

end

instantiation judg :: (order) order begin

instance
  by standard (auto simp add: less_eq_judg_def less_judg_def intro: order_trans split: judg.splits)

end

instantiation judg :: (bounded_lattice) bounded_lattice begin
definition sup_judg where
"a \<squnion> b \<equiv> case a of Empty \<Rightarrow> b 
  | Of x \<Rightarrow> (case b of Empty \<Rightarrow> Of x | Of y \<Rightarrow> Of (x \<squnion> y))"
definition inf_judg where
"a \<sqinter> b \<equiv> case a of Empty \<Rightarrow> Empty 
  | Of x \<Rightarrow> (case b of Empty \<Rightarrow> Empty | Of y \<Rightarrow> Of (x \<sqinter> y))"
definition top_judg where "\<top> = Of \<top>"
definition bot_judg where "\<bottom> = Empty"

instance
  by standard
    (auto simp add:
        sup_judg_def inf_judg_def top_judg_def bot_judg_def less_eq_judg_def
    split: judg.splits)

end

type_synonym 'v model_function = "'v list \<Rightarrow> 'v option"

type_synonym 't judgment_function = "'t list \<Rightarrow> 't judg"

context typing begin

primrec judges_type where
  "judges_type v (Of t) = of_type v t"
| "judges_type v Empty = False"

context fixes mf :: "'val model_function" begin
context fixes ts :: "'typ list" begin

abbreviation of_typeAll where "of_typeAll \<equiv> list_all2 of_type"

definition fn_value_set :: "'val set" where 
  "fn_value_set \<equiv> { v | vs v. of_typeAll vs ts \<and> mf vs = Some v }"

abbreviation sup_type where "sup_type \<equiv> \<Squnion>(principal_type ` fn_value_set)"
abbreviation min_common_type where "min_common_type \<equiv>  \<Sqinter>{t. \<forall> v \<in> fn_value_set. of_type v t}"

lemma sup_type_eq_min_common_type: "sup_type = min_common_type"
  by (rule Sup_principal_type)

definition fn_type_judgment :: "'typ judg" where
  "fn_type_judgment \<equiv> if (fn_value_set = {}) then Empty else Of min_common_type"

lemma fn_type_judgment_Empty: "fn_type_judgment = Empty \<longleftrightarrow> fn_value_set = {}"
  using fn_type_judgment_def
  by (cases "fn_value_set = {}") auto

lemma fn_type_judgment_Of: "fn_value_set \<noteq> {} \<Longrightarrow>
  fn_type_judgment = Of min_common_type"
  using fn_type_judgment_def
  by auto

definition sound_judgment :: "'typ judg \<Rightarrow> bool"
  where "sound_judgment t \<equiv> \<forall> v \<in> fn_value_set. judges_type v t"

lemma min_common_type_is_common: assumes "v \<in> fn_value_set"
  shows "of_type v min_common_type"
  using of_type_Inf assms by fastforce (* huh wow *)

theorem fn_type_judgment_sound: "sound_judgment fn_type_judgment"
  unfolding sound_judgment_def
  using fn_type_judgment_Of min_common_type_is_common by fastforce

lemma sound_nonempty: assumes "fn_value_set \<noteq> {}" and "sound_judgment t"
  obtains t0 where "t = Of t0"
  using assms by (cases t) (simp_all add: sound_judgment_def)

theorem fn_type_judgment_minimal: "sound_judgment t \<Longrightarrow> fn_type_judgment \<le> t"
proof (cases "fn_value_set = {}")
  case True
  then show ?thesis using fn_type_judgment_Empty less_eq_empty by auto
next
  case nonempty: False
  with nonempty have judged: "fn_type_judgment = Of min_common_type"
    using fn_type_judgment_Of by fast
  assume sound: "sound_judgment t"
  with nonempty obtain t0 where t0_def: "t = Of t0" using sound_nonempty by blast
  from sound t0_def have "\<forall> v \<in> fn_value_set. of_type v t0"
    using sound_judgment_def judges_type_def by simp
  then have "t0 \<in> {t. \<forall> v \<in> fn_value_set. of_type v t}" by blast
  then have "min_common_type \<le> t0" by (simp add: Inf_lower)
  with judged t0_def show ?thesis using less_eq_judg_def by fastforce
qed

abbreviation leqAll where "leqAll xs ys \<equiv> list_all2 (\<le>) xs ys"

lemma of_types_mono: \<open>of_typeAll vs ts \<Longrightarrow> leqAll ts ts' \<Longrightarrow> of_typeAll vs ts'\<close>
  by (rule list_all2_trans[where ?bs = ts and ?P1.0=of_type and ?P2.0=less_eq])
    (auto intro: of_type_mono)

end

context
  fixes ts :: "'typ list" and ts'
  assumes ts_leq: "leqAll ts ts'"
begin

lemma fn_value_set_mono: "fn_value_set ts \<subseteq> fn_value_set ts'"
  unfolding fn_value_set_def using ts_leq of_types_mono by auto

lemma sound_judgment_mono1: "sound_judgment ts' t \<Longrightarrow> sound_judgment ts t"
  unfolding sound_judgment_def using fn_value_set_mono by fast

theorem type_judgment_mono: "(fn_type_judgment ts) \<le> (fn_type_judgment ts')"
  using fn_type_judgment_sound fn_type_judgment_minimal sound_judgment_mono1
  by auto

end

definition arity where "arity n \<equiv> \<exists>vs. length vs = n \<and> mf vs \<noteq> None"

definition max_arity where "max_arity \<equiv> Max {n. arity n}"

definition signature_ith where
  \<open>signature_ith i \<equiv> \<Sqinter>{t. \<forall>vs. length vs \<ge> Suc i \<and> mf vs \<noteq> None \<longrightarrow> of_type (vs ! i) t}\<close>

definition signature where
  \<open>signature = map signature_ith [0..<max_arity]\<close>

end \<comment> \<open>mf\<close>
end \<comment> \<open>typing\<close>
end \<comment> \<open>theory\<close>