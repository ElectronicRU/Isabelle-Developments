theory Split_Semantics
  imports Expr_Combinators SplitPD
begin

default_sort type

section \<open>Semantics over split datasets\<close>

text \<open>The rigid semantics reads a dataset's definite rows, as a lower powerdomain.  The
  \<^emph>\<open>extended\<close> semantics reads a split dataset, definite rows and possible keys, and is defined
  combinator by combinator.  Its law is soundness against the rigid one: what it says is below
  what the rigid semantics says on the definite rows of every compact dataset above it.  It need
  not be exact there.\<close>

subsection \<open>Rows of compact split datasets\<close>

lemma lower_mem_Abs_pd_basis:
  assumes "finite S" "S \<noteq> {}"
  shows "x \<in>\<flat> lower_principal (Abs_pd_basis S) \<longleftrightarrow> (\<exists>s\<in>S. x \<sqsubseteq> Rep_compact_basis s)"
  using assms
proof (induct S rule: finite_ne_induct)
  case (singleton a)
  show ?case
    unfolding Abs_pd_basis_singleton lower_unit_Rep_compact_basis [symmetric] lower_mem_principal by simp
next
  case (insert a S)
  have eq: "Abs_pd_basis (insert a S) = PDPlus (PDUnit a) (Abs_pd_basis S)"
    unfolding PDPlus_def Rep_PDUnit using insert by (simp add: Abs_pd_basis_inverse pd_basis_def)
  show ?case
    unfolding eq lower_plus_principal [symmetric] lower_unit_Rep_compact_basis [symmetric] lower_mem_union lower_mem_principal
    using insert by simp
qed

lemma split_rows_mem_principal:
  "split_rows\<cdot>(split_principal t) = up\<cdot>data \<Longrightarrow> x \<in>\<flat> data \<longleftrightarrow> (\<exists>s\<in>srows t. x \<sqsubseteq> Rep_compact_basis s)"
proof (cases "srows t = {}")
  case False
  assume "split_rows\<cdot>(split_principal t) = up\<cdot>data"
  then have "data = lower_principal (Abs_pd_basis (srows t))" using False by (simp add: srows_lower_def)
  then show ?thesis by (simp add: lower_mem_Abs_pd_basis [OF finite_srows False])
qed (simp add: srows_lower_def)

lemma split_definite_rows_mem: "split_definite x xs \<Longrightarrow> split_rows\<cdot>xs = up\<cdot>data \<Longrightarrow> x \<in>\<flat> data"
  unfolding split_definite_def lower_mem_equiv
  by (drule monofun_cfun_arg [of _ _ split_rows]) simp

text \<open>The maximal rows of a compact dataset are among its generators.\<close>

lemma split_maximal_row_generator:
  assumes d: "split_rows\<cdot>(split_principal t) = up\<cdot>data" and m: "x \<in> lower_maximal data"
  shows "\<exists>s\<in>srows t. x = Rep_compact_basis s"
proof -
  have "x \<in>\<flat> data" using m by (simp add: lower_maximal_def)
  then obtain s where s: "s \<in> srows t" "x \<sqsubseteq> Rep_compact_basis s" using split_rows_mem_principal [OF d] by blast
  have "Rep_compact_basis s \<in>\<flat> data" using split_rows_mem_principal [OF d] s(1) by blast
  then have "Rep_compact_basis s = x" using m s(2) by (simp add: lower_maximal_def)
  then show ?thesis using s(1) by blast
qed

text \<open>Possibility is antitone: a key possible in a dataset is possible below it.\<close>

lemma split_possible_below: "split_possible k ys \<Longrightarrow> xs \<sqsubseteq> ys \<Longrightarrow> split_possible k xs"
  unfolding split_possible_keys by (erule below_trans [rotated], erule monofun_cfun_arg)


subsection \<open>Expressions with an extended semantics\<close>

text \<open>An extended expression is an expression with a semantics over split datasets as well.\<close>

record ('k::"domain", 'f::type, 'r::"{bifinite, distributive_cpo}", 'v::bifinite) expr_ext = "('k, 'f, 'r, 'v) expr" +
  sem_ext :: "('r, 'k) split_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'v option_pd"

hide_const (open) expr_ext.truncate

text \<open>An expression extended by a semantics over split datasets.\<close>

definition with_ext :: "('k::domain, 'f, 'r::{bifinite, distributive_cpo}, 'v::bifinite) expr \<Rightarrow>
    (('r, 'k) split_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'v option_pd) \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext" where
  "with_ext E s = expr.extend E (expr_ext.fields s)"

lemma with_ext_simps [simp]:
  "emind (with_ext E s) = emind E" "eguards (with_ext E s) = eguards E" "evalues (with_ext E s) = evalues E"
  
  "esem (with_ext E s) = esem E" "csem (with_ext E s) = csem E" "sem_ext (with_ext E s) = s"
  by (simp_all add: with_ext_def expr.defs expr_ext.defs)


text \<open>The row key of split datasets is the keying's.\<close>

locale split_dataspace = dataspace slicing rules keying + split_keyed keying
  for slicing :: "('f, 'k::{domain, lod_domain}) slicer_ops"
    and rules :: "'r::{domain, lod_domain} schema_rules" and keying :: "('r, 'k) keying"
begin

text \<open>\<^emph>\<open>Soundness\<close>: below a compact dataset whose definite rows are \<open>data\<close>, conforming
  relative to the expression's value entries, the extended semantics is below the rigid semantics
  of \<open>data\<close>, at every key of the key LOD.  Compact datasets with definite rows are where the rigid
  semantics is meant: it reads no possible keys, and its datasets cannot be empty.  An
  \<^emph>\<open>extended-lawful\<close> expression is moreover semilawful.\<close>

definition ext_sound :: "('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> bool" where
  "ext_sound X \<longleftrightarrow> (\<forall>D D' data F k. D \<sqsubseteq> D' \<longrightarrow> compact D' \<longrightarrow> split_rows\<cdot>D' = up\<cdot>data \<longrightarrow>
     fconf (evalues X) data F \<longrightarrow> proj (kd X F)\<cdot>k = k \<longrightarrow>
     sem_ext X D F k \<sqsubseteq> esem X data F k)"

lemma ext_soundI:
  "(\<And>D D' data F k. D \<sqsubseteq> D' \<Longrightarrow> compact D' \<Longrightarrow> split_rows\<cdot>D' = up\<cdot>data \<Longrightarrow>
     fconf (evalues X) data F \<Longrightarrow> proj (kd X F)\<cdot>k = k \<Longrightarrow>
     sem_ext X D F k \<sqsubseteq> esem X data F k) \<Longrightarrow> ext_sound X"
  unfolding ext_sound_def by blast

lemma ext_soundD:
  "ext_sound X \<Longrightarrow> D \<sqsubseteq> D' \<Longrightarrow> compact D' \<Longrightarrow> split_rows\<cdot>D' = up\<cdot>data \<Longrightarrow>
     fconf (evalues X) data F \<Longrightarrow> proj (kd X F)\<cdot>k = k \<Longrightarrow>
     sem_ext X D F k \<sqsubseteq> esem X data F k"
  unfolding ext_sound_def by blast

lemma semilawful_with_ext [simp]: "semilawful (with_ext E s) \<longleftrightarrow> semilawful E"
  by (simp add: semilawful_def cstrict_def)

definition ext_lawful :: "('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> bool" where
  "ext_lawful X \<longleftrightarrow> semilawful X \<and> ext_sound X"


subsection \<open>Keys\<close>

text \<open>The key at an LOD \<open>c\<close> is present where some definite row has it.  Where the key is
  maximal at \<open>c\<close> it stays present; where it is partial the row may still move up, so it is
  present or absent, present with that key.  Where no definite row has the key, it is absent if no
  possible key projects to it, and undecided otherwise.\<close>

abbreviation key_at_sem :: "'k semi_factor \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> 'k \<Rightarrow> 'k option_pd" where
  "key_at_sem c D k \<equiv> if \<exists>y. split_definite y D \<and> rproj c y = proj c\<cdot>k
     then (if maximal_at c (proj c\<cdot>k) then Present\<cdot>(proj c\<cdot>k) else Present\<cdot>(proj c\<cdot>k) + Absent)
     else if \<exists>u. split_possible u D \<and> proj c\<cdot>u = proj c\<cdot>k then \<bottom> else Absent"

definition key_at_ext :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'k) expr_ext" where
  "key_at_ext c = with_ext (key_at c) (\<lambda>D F k. key_at_sem c D k)"

lemma key_at_ext_simps [simp]:
  "semilawful (key_at_ext c) \<longleftrightarrow> semilawful (key_at c)"
  "emind (key_at_ext c) = emind (key_at c)" "eguards (key_at_ext c) = eguards (key_at c)" "evalues (key_at_ext c) = evalues (key_at c)"
  "esem (key_at_ext c) = esem (key_at c)" "csem (key_at_ext c) = csem (key_at c)"
  "sem_ext (key_at_ext c) D F k = key_at_sem c D k"
  by (simp_all add: key_at_ext_def)

text \<open>Below a compact dataset, a definite row at a key maximal at \<open>c\<close> lies below a data point with
  that key, and a key no possible key projects to has no data point.\<close>

lemma definite_maximal_point:
  assumes DD: "D \<sqsubseteq> D'" and d: "split_rows\<cdot>D' = up\<cdot>data" and y: "split_definite y D"
    and mx: "maximal_at c (rproj c y)"
  obtains m where "m \<in> lower_maximal data" "y \<sqsubseteq> m" "rproj c m = rproj c y"
proof -
  have "y \<in>\<flat> data" by (rule split_definite_rows_mem [OF split_definite_mono [OF y DD] d])
  then obtain m where m: "m \<in> lower_maximal data" "y \<sqsubseteq> m" by (rule lower_mem_maximal_above)
  have "rproj c y \<sqsubseteq> rproj c m" by (intro monofun_cfun_arg m(2))
  then have "rproj c m = rproj c y" by (rule maximal_at_eq [OF mx proj_idem])
  with m that show ?thesis by blast
qed

lemma impossible_no_point:
  assumes DD: "D \<sqsubseteq> D'" and cD: "compact D'" and d: "split_rows\<cdot>D' = up\<cdot>data"
    and m: "m \<in> lower_maximal data"
  shows "split_possible (rkey\<cdot>m) D"
proof -
  obtain t where t: "D' = split_principal t" using split_pd.compact_imp_principal [OF cD] by blast
  obtain s where s: "s \<in> srows t" "m = Rep_compact_basis s"
    using split_maximal_row_generator [OF d [unfolded t] m] by blast
  obtain u where u: "u \<in> skeys t" "Rep_compact_basis u \<sqsubseteq> rkey\<cdot>m"
    using split_basis_consistentD [OF s(1)] unfolding split_key_rkey s(2) by blast
  have "split_possible (Rep_compact_basis u) D'" unfolding t using u(1) by (auto simp: split_possible_principal)
  then have "split_possible (rkey\<cdot>m) D'" by (rule split_possible_up [OF _ u(2)])
  then show ?thesis by (rule split_possible_below [OF _ DD])
qed

theorem ext_sound_key_at: "ext_sound (key_at_ext c)"
proof (rule ext_soundI, simp only: key_at_ext_simps)
  fix D D' :: "('r, 'k) split_pd" and data F k
  assume DD: "D \<sqsubseteq> D'" and cD: "compact D'" and d: "split_rows\<cdot>D' = up\<cdot>data"
  have fib: "fiber data c c F k = {m \<in> lower_maximal data. rproj c m = proj c\<cdot>k}"
    by (simp add: fiber_def join_meet_self)
  have esem: "esem (key_at c) data F k = (if fiber data c c F k = {} then Absent else Present\<cdot>(proj c\<cdot>k))"
    by simp
  show "key_at_sem c D k \<sqsubseteq> esem (key_at c) data F k"
  proof (cases "\<exists>y. split_definite y D \<and> rproj c y = proj c\<cdot>k")
    case True
    then obtain y where y: "split_definite y D" "rproj c y = proj c\<cdot>k" by blast
    show ?thesis
    proof (cases "maximal_at c (proj c\<cdot>k)")
      case mx: True
      have mx': "maximal_at c (rproj c y)" using mx y(2) by simp
      obtain m where m: "m \<in> lower_maximal data" "rproj c m = rproj c y"
        using definite_maximal_point [OF DD d y(1) mx'] by blast
      have "fiber data c c F k \<noteq> {}" using fib m y(2) by auto
      then show ?thesis using True mx by simp
    next
      case False
      have "Present\<cdot>(proj c\<cdot>k) + Absent \<sqsubseteq> esem (key_at c) data F k"
        unfolding esem by (simp add: plus_option_pd_below1 plus_option_pd_below2)
      then show ?thesis using True False by simp
    qed
  next
    case nP: False
    show ?thesis
    proof (cases "\<exists>u. split_possible u D \<and> proj c\<cdot>u = proj c\<cdot>k")
      case True
      show ?thesis by (simp only: if_not_P [OF nP] if_P [OF True] minimal)
    next
      case nA: False
      have "fiber data c c F k = {}"
      proof (rule ccontr)
        assume "fiber data c c F k \<noteq> {}"
        then obtain m where m: "m \<in> lower_maximal data" "rproj c m = proj c\<cdot>k" using fib by blast
        have "split_possible (rkey\<cdot>m) D" by (rule impossible_no_point [OF DD cD d m(1)])
        then show False using nA m(2) by blast
      qed
      then show ?thesis by (simp only: if_not_P [OF nP] if_not_P [OF nA] esem) simp
    qed
  qed
qed

theorem ext_lawful_key_at: "ext_lawful (key_at_ext c)"
  unfolding ext_lawful_def by (simp add: semilawful_key_at ext_sound_key_at)


subsection \<open>Table columns\<close>

text \<open>A column at a key maximal at its key part \<open>a\<close> where some definite row has that key is
  present, with the column function of the join of the sections of the definite rows there: in a
  conforming dataset above, the rows at the key carry one section, above all of them.  At a partial
  key the value is not determined: a row there may move up, and another row may come to the key with
  an unrelated section, so it is undecided.  It is absent where no possible key projects to the key.\<close>

definition col_sections :: "'r semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> 'k \<Rightarrow> 'r set" where
  "col_sections c a D k = {y \<downharpoonright> c | y. split_definite y D \<and> rproj a y = proj a\<cdot>k}"

abbreviation column_sem :: "'r semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('r \<rightarrow> 'w::bifinite) \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> 'k \<Rightarrow> 'w option_pd" where
  "column_sem c a v D k \<equiv> if maximal_at a (proj a\<cdot>k) \<and> col_sections c a D k \<noteq> {}
     then Present\<cdot>(v\<cdot>(lub (col_sections c a D k)))
     else if \<exists>u. split_possible u D \<and> proj a\<cdot>u = proj a\<cdot>k then \<bottom> else Absent"

definition column_ext :: "'r semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('r \<rightarrow> 'w::bifinite) \<Rightarrow> ('k, 'f, 'r, 'w) expr_ext" where
  "column_ext c a v = with_ext (column c a v) (\<lambda>D F k. column_sem c a v D k)"

lemma column_ext_simps [simp]:
  "semilawful (column_ext c a v) \<longleftrightarrow> semilawful (column c a v)"
  "emind (column_ext c a v) = emind (column c a v)" "eguards (column_ext c a v) = eguards (column c a v)"
  "evalues (column_ext c a v) = evalues (column c a v)"
  "esem (column_ext c a v) = esem (column c a v)" "csem (column_ext c a v) = csem (column c a v)"
  "sem_ext (column_ext c a v) D F k = column_sem c a v D k"
  by (simp_all add: column_ext_def)

theorem ext_sound_column: "ext_sound (column_ext c a v)"
proof (rule ext_soundI, simp only: column_ext_simps)
  fix D D' :: "('r, 'k) split_pd" and data F k
  assume DD: "D \<sqsubseteq> D'" and cD: "compact D'" and d: "split_rows\<cdot>D' = up\<cdot>data"
    and conf: "fconf (evalues (column c a v)) data F"
  let ?e = "mk_value (sel a a) c a"
  have cf: "entry_conf ?e data F" using conf by (simp add: fconf_def)
  have fib: "fiber data a a F k = {m \<in> lower_maximal data. rproj a m = proj a\<cdot>k}"
    by (simp add: fiber_def join_meet_self)
  show "column_sem c a v D k \<sqsubseteq> esem (column c a v) data F k"
  proof (cases "maximal_at a (proj a\<cdot>k) \<and> col_sections c a D k \<noteq> {}")
    case True
    then have mx: "maximal_at a (proj a\<cdot>k)" and ne: "col_sections c a D k \<noteq> {}" by simp_all
    have point: "\<exists>m. m \<in> fiber data a a F k \<and> y \<sqsubseteq> m"
      if y: "split_definite y D" "rproj a y = proj a\<cdot>k" for y
    proof -
      have "maximal_at a (rproj a y)" using mx y(2) by simp
      then obtain m where "m \<in> lower_maximal data" "y \<sqsubseteq> m" "rproj a m = rproj a y"
        using definite_maximal_point [OF DD d y(1)] by blast
      then show ?thesis using fib y(2) by auto
    qed
    obtain y0 where y0: "split_definite y0 D" "rproj a y0 = proj a\<cdot>k"
      using ne by (auto simp: col_sections_def)
    obtain m where m: "m \<in> fiber data a a F k" "y0 \<sqsubseteq> m" using point [OF y0] by blast
    have ub: "col_sections c a D k <| m \<downharpoonright> c"
    proof (rule is_ubI)
      fix z assume "z \<in> col_sections c a D k"
      then obtain y where y: "split_definite y D" "rproj a y = proj a\<cdot>k" "z = y \<downharpoonright> c"
        by (auto simp: col_sections_def)
      obtain m' where m': "m' \<in> fiber data a a F k" "y \<sqsubseteq> m'" using point [OF y(1,2)] by blast
      have "y \<downharpoonright> c \<sqsubseteq> m' \<downharpoonright> c" by (intro monofun_cfun_arg m'(2))
      also have "\<dots> = m \<downharpoonright> c" by (rule column_fiber_section [OF cf m(1) m'(1)])
      finally show "z \<sqsubseteq> m \<downharpoonright> c" by (simp only: y(3))
    qed
    have "(\<lambda>y. v\<cdot>(y \<downharpoonright> c)) ` fiber data a a F k = (\<lambda>_. v\<cdot>(m \<downharpoonright> c)) ` fiber data a a F k"
      by (rule image_cong [OF refl]) (simp add: column_fiber_section [OF cf m(1)])
    then have V: "(\<lambda>y. v\<cdot>(y \<downharpoonright> c)) ` fiber data a a F k = {v\<cdot>(m \<downharpoonright> c)}"
      using m(1) by (auto simp: image_constant_conv)
    have "fiber data a a F k \<noteq> {}" using m(1) by blast
    then have esem: "esem (column c a v) data F k = Present\<cdot>(v\<cdot>(m \<downharpoonright> c))" by (simp add: V)
    have "lub (col_sections c a D k) \<sqsubseteq> m \<downharpoonright> c" by (rule lub_belowI [OF ne ub])
    then have "Present\<cdot>(v\<cdot>(lub (col_sections c a D k))) \<sqsubseteq> esem (column c a v) data F k"
      unfolding esem by (simp add: monofun_cfun_arg)
    then show ?thesis using True by simp
  next
    case nP: False
    show ?thesis
    proof (cases "\<exists>u. split_possible u D \<and> proj a\<cdot>u = proj a\<cdot>k")
      case True
      show ?thesis by (simp only: if_not_P [OF nP] if_P [OF True] minimal)
    next
      case nA: False
      have "fiber data a a F k = {}"
      proof (rule ccontr)
        assume "fiber data a a F k \<noteq> {}"
        then obtain m where m: "m \<in> lower_maximal data" "rproj a m = proj a\<cdot>k" using fib by blast
        have "split_possible (rkey\<cdot>m) D" by (rule impossible_no_point [OF DD cD d m(1)])
        then show False using nA m(2) by blast
      qed
      then show ?thesis by (simp only: if_not_P [OF nP] if_not_P [OF nA] column_simps) simp
    qed
  qed
qed

theorem ext_lawful_column:
  "universally (\<lambda>P. vfd P (\<bottom>, a) (c, \<bottom>)) \<Longrightarrow> ext_lawful (column_ext c a v)"
  unfolding ext_lawful_def by (simp add: semilawful_column ext_sound_column)


subsection \<open>Constants and maps\<close>

definition const_ext :: "'v::bifinite \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext" where
  "const_ext v = with_ext (const_expr v) (\<lambda>D F k. Present\<cdot>v)"

lemma const_ext_simps [simp]:
  "semilawful (const_ext v) \<longleftrightarrow> semilawful (const_expr v)"
  "emind (const_ext v) = emind (const_expr v)" "eguards (const_ext v) = eguards (const_expr v)" "evalues (const_ext v) = evalues (const_expr v)"
  "esem (const_ext v) = esem (const_expr v)" "csem (const_ext v) = csem (const_expr v)"
  "sem_ext (const_ext v) D F k = Present\<cdot>v"
  by (simp_all add: const_ext_def)

theorem ext_lawful_const: "ext_lawful (const_ext v)"
  unfolding ext_lawful_def by (auto simp: semilawful_const_expr intro: ext_soundI)

definition smap_ext :: "('v::bifinite \<rightarrow> 'w::bifinite) \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext \<Rightarrow> ('k, 'f, 'r, 'w) expr_ext" where
  "smap_ext g X = with_ext (smap g X) (\<lambda>D F k. map_option_pd g\<cdot>(sem_ext X D F k))"

lemma smap_ext_simps [simp]:
  "semilawful (smap_ext g X) \<longleftrightarrow> semilawful (smap g X)"
  "emind (smap_ext g X) = emind (smap g X)" "eguards (smap_ext g X) = eguards (smap g X)" "evalues (smap_ext g X) = evalues (smap g X)"
  "esem (smap_ext g X) = esem (smap g X)" "csem (smap_ext g X) = csem (smap g X)"
  "sem_ext (smap_ext g X) D F k = map_option_pd g\<cdot>(sem_ext X D F k)"
  by (simp_all add: smap_ext_def)

theorem ext_sound_smap: "ext_sound X \<Longrightarrow> ext_sound (smap_ext g X)"
  by (rule ext_soundI) (simp add: monofun_cfun_arg ext_soundD)

theorem ext_lawful_smap: "ext_lawful X \<Longrightarrow> ext_lawful (smap_ext g X)"
  unfolding ext_lawful_def by (simp add: semilawful_smap ext_sound_smap)

abbreviation value_at_ext :: "'k semi_factor \<Rightarrow> ('k \<rightarrow> 'v::bifinite) \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext" where
  "value_at_ext c g \<equiv> smap_ext g (key_at_ext c)"


subsection \<open>Frame transformers\<close>

definition restrict_ext :: "'r guard \<Rightarrow> ('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext" where
  "restrict_ext \<gamma> X = with_ext (restrict \<gamma> X) (\<lambda>D F. sem_ext X D (frestrict \<gamma> F))"

lemma restrict_ext_simps [simp]:
  "semilawful (restrict_ext \<gamma> X) \<longleftrightarrow> semilawful (restrict \<gamma> X)"
  "emind (restrict_ext \<gamma> X) = emind (restrict \<gamma> X)" "eguards (restrict_ext \<gamma> X) = eguards (restrict \<gamma> X)" "evalues (restrict_ext \<gamma> X) = evalues (restrict \<gamma> X)"
  "esem (restrict_ext \<gamma> X) = esem (restrict \<gamma> X)" "csem (restrict_ext \<gamma> X) = csem (restrict \<gamma> X)"
  "sem_ext (restrict_ext \<gamma> X) D F = sem_ext X D (frestrict \<gamma> F)"
  by (simp_all add: restrict_ext_def)

theorem ext_sound_restrict: "ext_sound X \<Longrightarrow> ext_sound (restrict_ext \<gamma> X)"
  by (rule ext_soundI) (simp add: ext_soundD fconf_frestrict)

theorem ext_lawful_restrict: "ext_lawful X \<Longrightarrow> ext_lawful (restrict_ext \<gamma> X)"
  unfolding ext_lawful_def by (simp add: semilawful_restrict ext_sound_restrict)

definition filtfor_ext :: "'k semi_factor \<Rightarrow> 'f \<Rightarrow> ('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext" where
  "filtfor_ext \<tau> G X = with_ext (filtfor \<tau> G X) (\<lambda>D F k. sem_ext X D (ffor \<tau> G F) (proj (emind X \<squnion> flod (ffor \<tau> G F))\<cdot>k))"

lemma filtfor_ext_simps [simp]:
  "semilawful (filtfor_ext \<tau> G X) \<longleftrightarrow> semilawful (filtfor \<tau> G X)"
  "emind (filtfor_ext \<tau> G X) = emind (filtfor \<tau> G X)" "eguards (filtfor_ext \<tau> G X) = eguards (filtfor \<tau> G X)" "evalues (filtfor_ext \<tau> G X) = evalues (filtfor \<tau> G X)"
  "esem (filtfor_ext \<tau> G X) = esem (filtfor \<tau> G X)" "csem (filtfor_ext \<tau> G X) = csem (filtfor \<tau> G X)"
  "sem_ext (filtfor_ext \<tau> G X) D F k = sem_ext X D (ffor \<tau> G F) (proj (emind X \<squnion> flod (ffor \<tau> G F))\<cdot>k)"
  by (simp_all add: filtfor_ext_def)

theorem ext_sound_filtfor: "ext_sound X \<Longrightarrow> ext_sound (filtfor_ext \<tau> G X)"
proof (rule ext_soundI, simp only: filtfor_ext_simps filtfor_simps)
  fix D D' :: "('r, 'k) split_pd" and data F k
  assume X: "ext_sound X" and DD: "D \<sqsubseteq> D'" and cD: "compact D'" and nD: "split_rows\<cdot>D' = up\<cdot>data"
    and d: "fconf (map (for_value \<tau>) (evalues X)) data F"
  have d': "fconf (evalues X) data (ffor \<tau> G F)" using d by (simp only: fconf_filtfor [of _ _ _ _ G])
  show "sem_ext X D (ffor \<tau> G F) (proj (emind X \<squnion> flod (ffor \<tau> G F))\<cdot>k)
      \<sqsubseteq> esem X data (ffor \<tau> G F) (proj (emind X \<squnion> flod (ffor \<tau> G F))\<cdot>k)"
    by (rule ext_soundD [OF X DD cD nD d' proj_idem])
qed

theorem ext_lawful_filtfor: "ext_lawful X \<Longrightarrow> ext_lawful (filtfor_ext \<tau> G X)"
  unfolding ext_lawful_def by (simp add: semilawful_filtfor ext_sound_filtfor)

text \<open>Including dimensions raises the frame LOD; the key LOD of a semilawful inner expression in
  the raised frame covers the outer one.\<close>

lemma include_dims_kd_below:
  assumes ES: "semilawful E"
  shows "kd (include_dims M E) F \<sqsubseteq> kd E (finclude M F)"
proof -
  let ?n = "fold (\<squnion>) (map (\<lambda>S. lower_part (include_sel M S)) (esels E)) \<bottom>"
  have le: "?n \<sqsubseteq> emind E \<squnion> M"
  proof (rule fold_join_least)
    fix x assume "x \<in> set (map (\<lambda>S. lower_part (include_sel M S)) (esels E))"
    then obtain S where S: "S \<in> set (esels E)" and x: "x = lower_part (include_sel M S)" by auto
    show "x \<sqsubseteq> emind E \<squnion> M" unfolding x include_sel_simps
      by (rule lattice_join_mono [OF lower_below_mind [OF ES S] truncate_below])
  qed simp
  have "?n \<squnion> flod F \<sqsubseteq> (emind E \<squnion> M) \<squnion> flod F" by (rule lattice_join_mono [OF le below_refl])
  also have "\<dots> = emind E \<squnion> flod (finclude M F)" unfolding flod_finclude by (simp only: lattice_join_ac)
  finally show ?thesis by simp
qed

definition include_dims_ext :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext" where
  "include_dims_ext M X = with_ext (include_dims M X) (\<lambda>D F. sem_ext X D (finclude M F))"

lemma include_dims_ext_simps [simp]:
  "semilawful (include_dims_ext M X) \<longleftrightarrow> semilawful (include_dims M X)"
  "emind (include_dims_ext M X) = emind (include_dims M X)" "eguards (include_dims_ext M X) = eguards (include_dims M X)" "evalues (include_dims_ext M X) = evalues (include_dims M X)"
  "esem (include_dims_ext M X) = esem (include_dims M X)" "csem (include_dims_ext M X) = csem (include_dims M X)"
  "sem_ext (include_dims_ext M X) D F = sem_ext X D (finclude M F)"
  by (simp_all add: include_dims_ext_def)

theorem ext_sound_include_dims:
  assumes ES: "semilawful X" and X: "ext_sound X"
  shows "ext_sound (include_dims_ext M X)"
proof (rule ext_soundI, simp only: include_dims_ext_simps include_dims_simps(3,4))
  fix D D' :: "('r, 'k) split_pd" and data F k
  assume DD: "D \<sqsubseteq> D'" and cD: "compact D'" and nD: "split_rows\<cdot>D' = up\<cdot>data"
    and d: "fconf (map (include_entry M) (evalues X)) data F"
    and k: "proj (kd (include_dims M X) F)\<cdot>k = k"
  have d': "fconf (evalues X) data (finclude M F)" using d by (simp only: fconf_include)
  have k': "proj (kd X (finclude M F))\<cdot>k = k" by (rule proj_fix_mono [OF include_dims_kd_below [OF ES] k])
  show "sem_ext X D (finclude M F) k \<sqsubseteq> esem X data (finclude M F) k"
    by (rule ext_soundD [OF X DD cD nD d' k'])
qed

theorem ext_lawful_include_dims: "ext_lawful X \<Longrightarrow> ext_lawful (include_dims_ext M X)"
  unfolding ext_lawful_def by (simp add: semilawful_include_dims ext_sound_include_dims)


subsection \<open>Combining\<close>

definition combine_ext :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<Rightarrow> ('k, 'f, 'r, 'a::bifinite) expr_ext \<Rightarrow> ('k, 'f, 'r, 'b::bifinite) expr_ext \<Rightarrow>
    ('k, 'f, 'r, 'c::bifinite) expr_ext" where
  "combine_ext f X\<^sub>1 X\<^sub>2 = with_ext (combine f X\<^sub>1 X\<^sub>2) (\<lambda>D F k. lift2_option_pd f\<cdot>(sem_ext X\<^sub>1 D F (proj (kd X\<^sub>1 F)\<cdot>k))\<cdot>(sem_ext X\<^sub>2 D F (proj (kd X\<^sub>2 F)\<cdot>k)))"

lemma combine_ext_simps [simp]:
  "semilawful (combine_ext f X\<^sub>1 X\<^sub>2) \<longleftrightarrow> semilawful (combine f X\<^sub>1 X\<^sub>2)"
  "emind (combine_ext f X\<^sub>1 X\<^sub>2) = emind (combine f X\<^sub>1 X\<^sub>2)" "eguards (combine_ext f X\<^sub>1 X\<^sub>2) = eguards (combine f X\<^sub>1 X\<^sub>2)" "evalues (combine_ext f X\<^sub>1 X\<^sub>2) = evalues (combine f X\<^sub>1 X\<^sub>2)"
  "esem (combine_ext f X\<^sub>1 X\<^sub>2) = esem (combine f X\<^sub>1 X\<^sub>2)" "csem (combine_ext f X\<^sub>1 X\<^sub>2) = csem (combine f X\<^sub>1 X\<^sub>2)"
  "sem_ext (combine_ext f X\<^sub>1 X\<^sub>2) D F k =
     lift2_option_pd f\<cdot>(sem_ext X\<^sub>1 D F (proj (kd X\<^sub>1 F)\<cdot>k))\<cdot>(sem_ext X\<^sub>2 D F (proj (kd X\<^sub>2 F)\<cdot>k))"
  by (simp_all add: combine_ext_def)

theorem ext_sound_combine:
  assumes X\<^sub>1: "ext_sound X\<^sub>1" and X\<^sub>2: "ext_sound X\<^sub>2"
  shows "ext_sound (combine_ext f X\<^sub>1 X\<^sub>2)"
proof (rule ext_soundI, simp only: combine_ext_simps combine_simps)
  fix D D' :: "('r, 'k) split_pd" and data F k
  assume DD: "D \<sqsubseteq> D'" and cD: "compact D'" and nD: "split_rows\<cdot>D' = up\<cdot>data"
    and d: "fconf (evalues X\<^sub>1 @ evalues X\<^sub>2) data F"
  have d1: "fconf (evalues X\<^sub>1) data F" and d2: "fconf (evalues X\<^sub>2) data F"
    using d by (simp_all add: fconf_def)
  show "lift2_option_pd f\<cdot>(sem_ext X\<^sub>1 D F (proj (kd X\<^sub>1 F)\<cdot>k))\<cdot>(sem_ext X\<^sub>2 D F (proj (kd X\<^sub>2 F)\<cdot>k))
      \<sqsubseteq> lift2_option_pd f\<cdot>(esem X\<^sub>1 data F (proj (kd X\<^sub>1 F)\<cdot>k))\<cdot>
          (esem X\<^sub>2 data F (proj (kd X\<^sub>2 F)\<cdot>k))"
    by (rule monofun_cfun [OF monofun_cfun_arg ext_soundD [OF X\<^sub>2 DD cD nD d2 proj_idem]],
        rule ext_soundD [OF X\<^sub>1 DD cD nD d1 proj_idem])
qed

theorem ext_lawful_combine: "ext_lawful X\<^sub>1 \<Longrightarrow> ext_lawful X\<^sub>2 \<Longrightarrow> ext_lawful (combine_ext f X\<^sub>1 X\<^sub>2)"
  unfolding ext_lawful_def by (simp add: semilawful_combine ext_sound_combine)

end

end
