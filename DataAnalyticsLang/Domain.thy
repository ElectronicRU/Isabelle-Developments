theory Domain imports Main Typing
  "~~/src/HOL/Library/Disjoint_Sets"
  abbrevs ".>" = "\<rightharpoonup>" and "><" = "\<Join>" 
begin

lemma map_restrict_self_dom: "m |` dom m = m" 
  by (simp add: ext domIff restrict_map_def)

lemma map_restrict_dom_inter: "m |` A = m |` (A \<inter> dom m)"
  by (simp add: ext domIff restrict_map_def)

lemma map_restrict_dom_subset:
  fixes m:: "'col \<rightharpoonup> 'val"
  fixes s:: "'col set"
  assumes "dom m \<subseteq> s"
  shows "m |` s = m"
  using assms map_restrict_self_dom map_restrict_dom_inter[of m s]
  by (metis inf.absorb_iff2)

lemma map_restrict_le: "m |` A \<subseteq>\<^sub>m m" by (metis restrict_in domIff restrict_out map_le_def)

lemma map_concat_restrict_dom:
  fixes m:: "'col \<rightharpoonup> 'val"
  and n:: "'col \<rightharpoonup> 'val"
  and h:: "'col set"
  assumes "dom m \<inter> h = {}"
  shows "(m ++ n) |` h = n |` h"
  using assms disjoint_iff
    Map.restrict_in[of _ h] Map.restrict_out[of _ h]
    Map.map_add_dom_app_simps[of _ m n]
    ext
  by (metis (no_types, lifting))

lemma map_restrict_union:
  fixes m:: "'col \<rightharpoonup> 'val"
  and s1:: "'col set"
  and s2:: "'col set"
shows "m |` (s1 \<union> s2) = m |` s1 ++ m |` s2"
proof
  let ?m1 = "m |` s1"
  let ?m2 = "m |` s2"
  fix x
  show "(m |` (s1 \<union> s2)) x = (?m1 ++ ?m2) x"
  proof (cases "x \<in> dom ?m2")
    case True
    then show ?thesis by (simp add: Map.map_add_dom_app_simps)
  next
    case not_in: False
    then have "(?m1 ++ ?m2) x = ?m1 x" by (simp add: Map.map_add_dom_app_simps)
    also have "... = (m |` (s1 \<union> s2)) x"  by (metis not_in restrict_out restrict_in Un_iff domIff)
    finally show ?thesis ..
  qed
qed

abbreviation "nil \<equiv> Map.empty"

lemma disjoint_family_on_subset: fixes A B S shows
  "disjoint_family_on A S \<Longrightarrow> \<forall> x \<in> S. B x \<subseteq> A x \<Longrightarrow> disjoint_family_on B S"
  by (force simp add: disjoint_family_on_def)

locale unrestricted_rows =
  fixes
  table_of :: "'col \<Rightarrow> 'tab"
  and table_columns :: "'tab \<Rightarrow> 'col set"
  and data :: "'tab \<Rightarrow> ('col \<rightharpoonup> 'val) set"
defines
  table_columns_def: "table_columns t \<equiv> {c. table_of c = t}"
assumes 
  data_dom: "\<And>t. \<forall>m \<in> data t. dom m \<subseteq> table_columns t"
begin

lemma disjoint_tables: "disjoint_family table_columns"
proof -
  have "table_columns t1 \<inter> table_columns t2 = {}" if "t1 \<noteq> t2" for t1 t2
    unfolding table_columns_def
    using that by auto
  then show ?thesis unfolding disjoint_family_on_def by auto
qed

abbreviation data' where "data' x \<equiv> insert nil (data x)"
definition choice_space where "choice_space \<equiv> (\<Pi> x \<in> UNIV. data' x)"

theorem choice_space_def': "choice_space = {g. \<forall> x. g x = nil \<or> g x \<in> data x}"
  unfolding choice_space_def
  by blast

lemma choice_space_nil: "(\<lambda>_.nil) \<in> choice_space"
  unfolding choice_space_def' by simp

abbreviation factorized :: "('tab \<Rightarrow> ('col \<rightharpoonup> 'val)) \<Rightarrow> bool"
  where "factorized g \<equiv> \<forall> t. dom (g t) \<subseteq> table_columns t"

lemma choice_space_factorized[dest]: "g \<in> choice_space \<Longrightarrow> factorized g"
  unfolding choice_space_def' using data_dom by force

definition product :: "('tab \<Rightarrow> ('col \<rightharpoonup> 'val)) \<Rightarrow> ('col \<rightharpoonup> 'val)"
  where "product g c \<equiv> g (table_of c) c"

definition factor :: "('col \<rightharpoonup> 'val) \<Rightarrow> ('tab \<Rightarrow> ('col \<rightharpoonup> 'val))"
  where "factor m t c \<equiv> if table_of c = t then m c else None"

lemma prod_inv_factor: "product (factor m) = m" for m
  unfolding product_def factor_def by auto

lemma factor_inv_prod: assumes "factorized g" shows "factor (product g) = g"
proof (rule, rule)
  fix t :: 'tab and c
  have "dom (g t) \<subseteq> table_columns t" using assms by simp
  also have "... = {c. table_of c = t}" using table_columns_def by simp
  finally have "table_of c \<noteq> t \<Longrightarrow> g t c = None" using table_columns_def by blast
  then have "g t c = (if table_of c = t then g t c else None)" by simp
  also have "... = (if table_of c = t then g (table_of c) c else None)" by simp
  also have "... = (if table_of c = t then product g c else None)"
    using product_def by simp
  also have "... = factor (product g) t c" using factor_def by simp
  finally show "factor (product g) t c = g t c" ..
qed

theorem prod_inj: assumes "\<And>x. x \<in> S \<Longrightarrow> factorized x" shows "inj_on product S"
  by (rule inj_on_inverseI[of _ factor]) (simp add: assms factor_inv_prod)

corollary prod_inj_choice_space: "inj_on product choice_space"
  using prod_inj choice_space_factorized by blast

theorem factor_inj: "inj factor"
  by (rule inj_on_inverseI[of _ product])
    (simp add: pointfree_idE prod_inv_factor)

abbreviation lim_table where "lim_table t m \<equiv> m |` table_columns t"

lemma factor_lim_table: "lim_table t m = factor m t"
  using factor_def table_columns_def by auto

corollary factorized_factor: "factorized (factor m)"
proof (rule, rule)
  fix t :: 'tab and c :: 'col
  assume "c \<in> dom (factor m t)"
  also have "factor m t = lim_table t m" using factor_lim_table by simp
  finally show "c \<in> table_columns t" by simp
qed

corollary factorized_factor_set: "g \<in> factor ` S \<Longrightarrow> factorized g" for g
  using factorized_factor by auto

corollary lim_table_prod: assumes "factorized g" shows "lim_table t (product g) = g t"
  using assms factor_lim_table factor_inv_prod by simp

definition support :: "('a \<Rightarrow> ('col \<rightharpoonup> 'val)) \<Rightarrow> 'a set"
  where "support g \<equiv> {t. g t \<noteq> nil}"

definition limit :: "'a set \<Rightarrow> ('a \<Rightarrow> ('col \<rightharpoonup> 'val)) \<Rightarrow> ('a \<Rightarrow> ('col \<rightharpoonup> 'val))"
  where "limit T g t \<equiv> if t \<in> T then g t else nil"

lemma support_limit: "support (limit T g) = support g \<inter> T" for T g
  unfolding support_def limit_def
  by (rule set_eqI) simp

lemma limit_support: "support g \<subseteq> T \<Longrightarrow> limit T g = g" for T g
  unfolding support_def limit_def
  by force

lemma limit_choice_space: "g \<in> choice_space \<Longrightarrow> limit T g \<in> choice_space" for T g
  unfolding choice_space_def' limit_def
  by simp

lemma limit_limit: "limit T \<circ> limit S = limit (T \<inter> S)" for T S
  unfolding limit_def
  by fastforce

lemma support_factor: "t \<in> support (factor m) \<longleftrightarrow> dom m \<inter> table_columns t \<noteq> {}" for t
proof
  assume "t \<in> support (factor m)"
  then have "factor m t \<noteq> nil" using support_def by fast
  then have "lim_table t m \<noteq> nil" using factor_lim_table by simp
  then have "{} \<noteq> dom (lim_table t m)" by blast
  also have "dom (lim_table t m) = dom m \<inter> table_columns t" using Map.dom_restrict by simp
  finally show "dom m \<inter> table_columns t \<noteq> {}" ..
next
  assume "dom m \<inter> table_columns t \<noteq> {}"
  then obtain c where "c \<in> dom m \<inter> table_columns t" by blast
  then have "m c \<noteq> None" and "table_of c = t" using table_columns_def by auto
  then have "factor m t c \<noteq> None" using factor_def by simp
  then have "factor m t \<noteq> nil" by auto
  then show "t \<in> support (factor m)" using support_def by fast
qed

definition subspace where "subspace U \<equiv> {g \<in> choice_space. support g \<subseteq> U}"

definition restricted_universe where
"restricted_universe U = product ` subspace U"

lemma choice_space_subspace: "choice_space = subspace UNIV"
  unfolding subspace_def by simp

theorem subspace_eq_factor: "subspace U = factor ` restricted_universe U" for U
proof -
  have ss_f: "g \<in> subspace U \<Longrightarrow> factorized g" for g
    using subspace_def choice_space_factorized by simp
  have ru_f: "g \<in> factor ` restricted_universe U \<Longrightarrow> factorized g" for g
    using factorized_factor_set by simp
  from ss_f ru_f have inj_on_Un: "inj_on product (subspace U \<union> (factor ` restricted_universe U))"
    using prod_inj by fastforce
  thm inj_on_Un_image_eq_iff

  have "product ` subspace U = restricted_universe U"
    unfolding subspace_def restricted_universe_def by presburger
  also have "... = product ` factor ` restricted_universe U"
    by (subst image_comp) (simp add: prod_inv_factor)
  finally show "subspace U = factor ` restricted_universe U"
    using inj_on_Un_image_eq_iff inj_on_Un by metis
qed

lemma subspace_limit_def: "subspace S = limit S ` choice_space"
proof (rule; rule subsetI)
  fix x assume "x \<in> subspace S"
  then have cs: "x \<in> choice_space" and supp: "support x \<subseteq> S"
    using subspace_def by simp_all
  from supp have "limit S x = x" by (rule limit_support)
  with cs show "x \<in> limit S ` choice_space" by force
next
  fix x assume "x \<in> limit S ` choice_space"
  then obtain y where y_def:"y \<in> choice_space" "x = limit S y" by blast
  then have 1: "support x \<subseteq> S" using support_limit by fast
  from y_def have 2: "x \<in> choice_space" using limit_choice_space by simp
  from 1 2 show "x \<in> subspace S" unfolding subspace_def by simp
qed

lemma limit_subspace: "limit S ` subspace T = subspace (S \<inter> T)"
  using subspace_limit_def image_comp limit_limit by metis

lemma restricted_universe_factor_support:
  assumes "m \<in> restricted_universe T"
  shows "support (factor m) \<subseteq> T"
proof -
  from assms obtain g where "m = product g" and "g \<in> choice_space"
    and sub_t: "support g \<subseteq> T"
    using restricted_universe_def subspace_def by auto
  then have "factor m = g" using factor_inv_prod by auto
  with sub_t show ?thesis by simp
qed

definition "limit_tables T m \<equiv> m |` (table_of -`  T)"

lemma limit_tables_factor: "limit_tables T = product \<circ> (limit T) \<circ> factor"
  unfolding limit_tables_def factor_def product_def limit_def
  by (intro ext) simp

lemma limit_tables_restricted:
  "limit_tables S ` restricted_universe T = restricted_universe (S \<inter> T)"
proof -
  have "limit_tables S ` (restricted_universe T) =
        (product \<circ> (limit S) \<circ> factor) ` restricted_universe T"
    using limit_tables_factor by simp
  also have "... = product ` limit S ` factor ` restricted_universe T"
    using image_comp by metis
  also have "factor ` restricted_universe T = subspace T" by (fact subspace_eq_factor[symmetric])
  also have "limit S ` subspace T = subspace (S \<inter> T)" by (fact limit_subspace)
  also have "product ` subspace (S \<inter> T) = restricted_universe (S \<inter> T)"
    using restricted_universe_def by presburger
  finally show ?thesis .
qed

lemma subspace_mono: "S \<subseteq> T \<Longrightarrow> subspace S \<subseteq> subspace T" unfolding subspace_def by auto

lemma restricted_universe_mono: "S \<subseteq> T \<Longrightarrow> restricted_universe S \<subseteq> restricted_universe T"
  unfolding restricted_universe_def using subspace_mono by blast

lemma factor_subspace_mem: "factor m \<in> subspace T \<Longrightarrow> m \<in> restricted_universe T"
  unfolding subspace_eq_factor
  by (simp add: factor_inj inj_image_mem_iff)

definition universe where "universe \<equiv> product ` choice_space"

lemma universe_restricted: "universe = restricted_universe UNIV"
  unfolding universe_def restricted_universe_def
  using choice_space_subspace by simp

corollary restricted_universe_limit: "limit_tables S ` universe = restricted_universe S"
  using limit_tables_restricted universe_restricted by simp

corollary factor_universe: "factor ` universe = choice_space"
  using universe_restricted subspace_eq_factor choice_space_subspace by simp

corollary subset_universe: "restricted_universe S \<subseteq> universe" for S
  unfolding universe_restricted using restricted_universe_mono by simp

lemma universe_nil: "nil \<in> universe" proof -
  have "nil = product (\<lambda>_. nil)" using product_def by auto
  also have "... \<in> universe" using choice_space_nil universe_def by auto
  finally show ?thesis.
qed

definition tables_of :: "('col \<rightharpoonup> 'val) \<Rightarrow> 'tab set"
  where "tables_of m = table_of ` (dom m)"

lemma tables_of_support: "tables_of m = support (factor m)"
proof -
  have "tables_of m = table_of ` (dom m)" using tables_of_def by simp
  also have "... = {table_of c | c. m c \<noteq> None}" by blast
  also have "... = {table_of c | c. factor m (table_of c) c \<noteq> None}" using factor_def by simp
  also have "... = {t. \<exists>c. factor m t c \<noteq> None}" using factor_def by auto
  also have "... = {t. factor m t \<noteq> nil}" by auto
  also have "... = support (factor m)" using support_def by metis
  finally show ?thesis .
qed

lemma limit_tables_subset: assumes "tables_of m \<subseteq> S" shows "limit_tables S m = m" proof -
  have "limit_tables S m = product (limit S (factor m))"
    using limit_tables_factor by auto
  also have "limit S (factor m) = factor m" using limit_support tables_of_support assms by auto
  also have "product ... = m" by (rule prod_inv_factor)
  finally show ?thesis .
qed

lemma support_restricted_universe_mem: "g \<in> universe \<Longrightarrow> g \<in> restricted_universe (tables_of g)"
proof -
  define T where "T = tables_of g"
  then have T_eq: "T = support (factor g)" using tables_of_support by simp

  assume "g \<in> universe"
  then have "factor g \<in> choice_space" using factor_universe by auto
  with T_eq have "factor g \<in> subspace T" using subspace_def by simp
  then show "g \<in> restricted_universe T" by (rule factor_subspace_mem)
qed

lemma restricted_universe_tables_of: "m \<in> restricted_universe S \<Longrightarrow> tables_of m \<subseteq> S" for m S
  using restricted_universe_factor_support tables_of_support by simp

lemma restricted_universe_nil: "nil \<in> restricted_universe T" for T
proof
  have "tables_of nil = {}" using tables_of_def by fast
  then show "nil \<in> restricted_universe {}"
    using support_restricted_universe_mem universe_nil by metis
  show "restricted_universe {} \<subseteq> restricted_universe T"
    using restricted_universe_mono by simp
qed

definition extended_universe where
"extended_universe \<equiv> {m'. \<exists>m \<in> universe. m' \<subseteq>\<^sub>m m}"

abbreviation project where "project C m \<equiv> m |` C"

theorem project_project: "project A (project B m) = project (A \<inter> B) m" for A B m
  unfolding Map.restrict_map_def by fastforce

lemma extended_universe_mem: "universe \<subseteq> extended_universe"
  unfolding extended_universe_def by force

lemma extended_universe_mono:
  "m \<in> extended_universe \<Longrightarrow> m' \<subseteq>\<^sub>m m \<Longrightarrow> m' \<in> extended_universe"
  unfolding extended_universe_def using map_le_trans by blast

section \<open>Additional definitions\<close>

abbreviation "universe_of cols \<equiv> restricted_universe (table_of ` cols)"

abbreviation is_key :: "'col set \<Rightarrow> bool"
  where "is_key cols \<equiv> inj_on (project cols) (universe_of cols)"

abbreviation "table_cols_of cols \<equiv> table_of -` table_of ` cols"

abbreviation "key_limit cols \<equiv> project (table_cols_of cols)"

lemma key_limit_tables: "key_limit cols m = limit_tables (table_of ` cols) m" 
  by (simp add: limit_tables_def)

corollary key_limit_universe_of: "m \<in> universe \<Longrightarrow> key_limit cols m \<in> universe_of cols"
  unfolding key_limit_tables
  using restricted_universe_limit
  by blast


subsection \<open>Facts about table_cols_of as an automorphism of set algebra\<close>

lemma table_cols_tables: "table_of ` (table_cols_of cols) = table_of ` cols"
  by blast

corollary table_cols_of_idem: "table_cols_of (table_cols_of cols) = table_cols_of cols"
  using table_cols_tables by blast

lemma table_cols_of_union: "table_cols_of A \<union> table_cols_of B = table_cols_of (A \<union> B)"
  by auto

lemma table_cols_of_superset: "cols \<subseteq> table_cols_of cols" by blast

abbreviation "agrees A x y \<equiv> x |` A = y |` A"

lemma agrees_iff: "agrees A x y \<longleftrightarrow> (\<forall>a \<in> A. x a = y a)"
proof -
  have "agrees A x y \<longleftrightarrow> (\<forall>a. (x |` A) a = (y |` A) a)" by auto
  also have "... = (\<forall>a \<in> A. (x |` A) a = (y |` A) a) \<and> (\<forall>a. a \<notin> A \<longrightarrow> (x |` A) a = (y |` A) a)"
    by fastforce
  also have "(\<forall>a. a \<notin> A \<longrightarrow> (x |` A) a = (y |` A) a) \<longleftrightarrow> True" by simp
  also have "(\<forall>a \<in> A. (x |` A) a = (y |` A) a) \<longleftrightarrow> (\<forall>a \<in> A. x a = y a)" by simp
  finally show ?thesis by simp
qed

lemma agrees_union_iff[iff]: "agrees A x y \<and> agrees B x y \<longleftrightarrow> agrees (A \<union> B) x y"
  unfolding agrees_iff by blast

lemma agrees_mono: "A \<subseteq> B \<Longrightarrow> agrees B x y \<Longrightarrow> agrees A x y"
  unfolding agrees_iff by blast

abbreviation is_key_universal :: "'col set \<Rightarrow> prop"
  where "is_key_universal cols \<equiv> (\<And>x y. x \<in> universe \<Longrightarrow> y \<in> universe \<Longrightarrow>
    agrees cols x y \<Longrightarrow>
      agrees (table_cols_of cols) x y)"

lemma key_limit_project_project: "project cols (key_limit cols m) = project cols m"
  using project_project table_cols_of_superset by (simp add: inf.absorb_iff2)


theorem is_key_universalD[dest?]: "is_key cols \<Longrightarrow> PROP is_key_universal cols" proof -
  assume inj_1: "is_key cols"
  fix x y
  assume x: "x \<in> universe" and y: "y \<in> universe"
  assume proj_eq: "project cols x = project cols y"
  let ?x1 = "key_limit cols x" and ?y1 = "key_limit cols y"
  from x have x1: "?x1 \<in> universe_of cols" by (rule key_limit_universe_of)
  from y have y1: "?y1 \<in> universe_of cols" by (rule key_limit_universe_of)
  have "project cols ?x1 = project cols x" by (rule key_limit_project_project)
  also have "... = project cols y" by (fact proj_eq)
  also have "... = project cols ?y1" by (rule key_limit_project_project[symmetric])
  finally show "?x1 = ?y1" using x1 y1 inj_1 inj_onD by metis
qed

lemma is_key_universalI[intro?]: "PROP is_key_universal cols \<Longrightarrow> is_key cols" proof (rule inj_onI)
  assume inj_2: "x \<in> universe \<Longrightarrow> y \<in> universe \<Longrightarrow> project cols x = project cols y \<Longrightarrow>
    key_limit cols x = key_limit cols y" for x y
  fix x y
  assume x: "x \<in> universe_of cols" and y: "y \<in> universe_of cols"
  have conv: "z \<in> universe \<and> key_limit cols z = z" (is "?prop z") if "z \<in> universe_of cols" for z
    using subset_universe limit_tables_subset restricted_universe_tables_of that
    key_limit_tables subsetD by metis

  from x have x1: "?prop x" by (rule conv)
  from y have y1: "?prop y" by (rule conv)

  assume "project cols x = project cols y"
  with inj_2 x1 y1 show "x = y" by metis
qed

thm agrees_union_iff

theorem is_key_union: "is_key A \<Longrightarrow> is_key B \<Longrightarrow> is_key (A \<union> B)"
proof (rule is_key_universalI)
  assume "is_key A" then have aprop: "PROP is_key_universal A" by (rule is_key_universalD)
  assume "is_key B" then have bprop: "PROP is_key_universal B" by (rule is_key_universalD)
  fix x y assume x: "x \<in> universe" and y: "y \<in> universe"
  assume congrU: "agrees (A \<union> B) x y"
  then have "agrees A x y \<and> agrees B x y" by simp
  then have congrA: "agrees A x y" and congrB: "agrees B x y"
    by (satx+)
  from x y congrA have klA: "agrees (table_cols_of A) x y" by (rule aprop)
  from x y congrB have klB: "agrees (table_cols_of B) x y" by (rule bprop)
  from klA klB have "agrees (table_cols_of A \<union> table_cols_of B) x y" using agrees_union_iff by fast
  then show "agrees (table_cols_of (A \<union> B)) x y" using table_cols_of_union by simp
qed

end
end