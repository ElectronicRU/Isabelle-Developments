theory Ast_Semantics
  imports Ast Aggregate
begin

section \<open>Levels of expressions\<close>

text \<open>Two levels are read off the dims.  A \<^emph>\<open>row-level\<close> expression (an attribute) reads every
  content at most at its lower part, so all rows of a group agree on the section and each
  content has at most one key.  A \<^emph>\<open>total-level\<close> expression (an aggregation) has no minimal
  LOD.  Constants are both; the remaining expressions are aggregations with explicit grouping.
  Row level is preserved by maps and by collecting, since collecting only widens lower parts.\<close>

context dataspace
begin

definition row_level :: "('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> bool" where
  "row_level E \<longleftrightarrow> (\<forall>e\<in>set (edims E). row_entry e)"

definition total_level :: "('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> bool" where
  "total_level E \<longleftrightarrow> emind E = \<bottom>"

lemma row_level_value_at: "row_level (value_at c g)"
  by (simp add: row_level_def row_entry_def)

lemma row_level_column: "row_level (column c a v)"
  by (simp add: row_level_def row_entry_def)

lemma total_level_value_at_bot: "total_level (value_at \<bottom> g)"
  by (simp add: total_level_def)

lemma row_level_smap: "row_level (smap g E) \<longleftrightarrow> row_level E"
  by (simp add: row_level_def)

lemma row_level_collect: "(\<And>E. E \<in> set Es \<Longrightarrow> row_level E) \<Longrightarrow> row_level (collect Es)"
  unfolding row_level_def collect_simps by fastforce

lemma total_level_aggregate: "total_level (aggregate M f E)"
  by (simp add: total_level_def)

text \<open>The content graphs of a semilawful row-level expression have at most one element: the rows
  of a group agree on the key at the lower part, which determines the view.\<close>

lemma row_level_content_single:
  assumes E: "semilawful E" and r: "row_level E" and d: "conforms data" and e: "e \<in> set (edims E)"
    and u: "u \<in> cgraph data e F k" and u': "u' \<in> cgraph data e F k"
  shows "u = u'"
proof -
  let ?G = "elower e \<squnion> (eupper e \<sqinter> flod F)"
  obtain x where x: "x \<in> group data (elower e) (eupper e) F k" using u by (auto simp: cgraph_def efiber_def)
  have "cgraph data e F k = (if ofun (eguard e)\<cdot>x = TT then {cpair e x} else {})"
    unfolding cgraph_def efiber_def
  proof (rule row_entry_image[OF semilawful_wf[OF E e] _ d _ x lattice_join_ge1[of "elower e" "eupper e \<sqinter> flod F"]])
    show "row_entry e" using r e by (simp add: row_level_def)
    show "group data (elower e) (eupper e) F k \<subseteq> lower_maximal data" by (auto simp: group_def)
    show "rproj ?G y = rproj ?G x" if "y \<in> group data (elower e) (eupper e) F k" for y
      using that x by (simp add: group_def)
  qed
  then show ?thesis using u u' by (simp split: if_splits)
qed

end

section \<open>Semantics\<close>

text \<open>The symbol tables: dimensions and tabled function symbols as in the key language; each
  table column reads a section of the row, and an oracle names the dimension determining it in
  every conforming dataset; tabled function symbols admit some numbers of arguments; aggregation
  symbols are commutative and associative.  The slicer is the one of conditions; a cut's
  condition is a slice of one conjunct.\<close>

locale ast_space = key_language dim_lod dim_val key_dims fn_other + keyed_schema rules keying
  for dim_lod :: "'d \<Rightarrow> 'k::{domain, lod_domain} semi_factor"
    and dim_val :: "'d \<Rightarrow> 'k \<rightarrow> scalar with_na" and key_dims :: "'k \<Rightarrow> 'd list"
    and fn_other :: "'fn \<Rightarrow> scalar datum ltuple \<rightarrow> scalar datum"
    and rules :: "'r::{domain, lod_domain} schema_rules" and keying :: "('r, 'k) keying" +
  fixes col_sec :: "'c \<Rightarrow> 'r semi_factor" and col_dim :: "'c \<Rightarrow> 'd" and col_val :: "'c \<Rightarrow> 'r \<rightarrow> scalar datum"
    and fn_arity :: "'fn \<Rightarrow> nat \<Rightarrow> bool"
    and ag_sem :: "'ag \<Rightarrow> scalar datum \<rightarrow> scalar datum \<rightarrow> scalar datum"
  assumes col_reads: "col_val c\<cdot>(x \<downharpoonright> col_sec c) = col_val c\<cdot>x"
    and col_fd: "universally (\<lambda>P. vfd P (\<bottom>, dim_lod (col_dim c)) (col_sec c, \<bottom>))"
    and ag_abel: "abel_semigroup (\<lambda>a b. ag_sem g\<cdot>a\<cdot>b)"
begin

sublocale dataspace "ast_slicing :: (('d, 'c, 'fn, 'ag) slice, 'k) slicer_ops" rules keying
  by (simp add: dataspace_def slicer_ast_slicing keyed_schema_axioms)

text \<open>The \<^emph>\<open>requested\<close> dimensions of an expression: \<open>GROUP BY\<close> raises them, an aggregation
  consumes those of its argument and requests none itself; cuts and filters leave them alone.\<close>

fun requested :: "('d, 'c, 'fn, 'ag) ast \<Rightarrow> 'k semi_factor" where
  "requested (Dim d) = \<bottom>"
| "requested (Col c) = \<bottom>"
| "requested (Lit v) = \<bottom>"
| "requested (Call fn es) = fold (\<squnion>) (map requested es) \<bottom>"
| "requested (Aggr g e) = \<bottom>"
| "requested (GroupBy ds e) = lod ds \<squnion> requested e"
| "requested (For ds C e) = requested e"
| "requested (Where C e) = requested e"

text \<open>Row-level expressions read the parts of their views directly: dimensions the key part,
  columns their sections, calls their arguments' parts.  Their view joins the views of the
  dimensions and columns they read.  (A reading of row-level conditions apart from the expression
  semantics, until the latter gives continuous functions of the view parts itself.)\<close>

fun pval :: "('d, 'c, 'fn, 'ag) ast \<Rightarrow> 'r \<times> 'k \<rightarrow> scalar datum" where
  "pval (Dim d) = key_datum oo dim_val d oo csnd"
| "pval (Col c) = col_val c oo cfst"
| "pval (Lit v) = (\<Lambda> _. v)"
| "pval (Call fn es) = fsym_sem fn_other fn oo tuple_cfun (map pval es)"
| "pval _ = \<bottom>"

fun rview :: "('d, 'c, 'fn, 'ag) ast \<Rightarrow> ('r, 'k) view" where
  "rview (Dim d) = (\<bottom>, dim_lod d)"
| "rview (Col c) = (col_sec c, dim_lod (col_dim c))"
| "rview (Lit v) = \<bottom>"
| "rview (Call fn es) = fold (\<squnion>) (map rview es) \<bottom>"
| "rview _ = \<bottom>"

fun row_ast :: "('d, 'c, 'fn, 'ag) ast \<Rightarrow> bool" where
  "row_ast (Dim d) \<longleftrightarrow> True"
| "row_ast (Col c) \<longleftrightarrow> True"
| "row_ast (Lit v) \<longleftrightarrow> True"
| "row_ast (Call fn es) \<longleftrightarrow> fsym_arity fn_arity fn (length es) \<and> (\<forall>e\<in>set es. row_ast e)"
| "row_ast _ \<longleftrightarrow> False"

text \<open>A row-level condition is a guard through its truth value.\<close>

definition row_guard :: "('d, 'c, 'fn, 'ag) ast \<Rightarrow> ('r, 'k) guard" where
  "row_guard C = \<lparr>vfun = truth_d oo pval C, oview = rview C\<rparr>"

lemma row_guard_view [simp]: "oview (row_guard C) = rview C"
  by (simp add: row_guard_def)

text \<open>The views of row-level expressions are keyed.\<close>

lemma keyed_view_bot: "keyed_view (\<bottom> :: ('r, 'k) view)"
  unfolding inst_prod_pcpo by (rule keyed_view_key)

lemma keyed_view_fold:
  "(\<And>v. v \<in> set vs \<Longrightarrow> keyed_view v) \<Longrightarrow> keyed_view b \<Longrightarrow> keyed_view (fold (\<squnion>) vs b)"
  by (induct vs arbitrary: b) (simp_all add: keyed_view_sup)

lemma keyed_view_rview: "row_ast e \<Longrightarrow> keyed_view (rview e)"
proof (induct e rule: row_ast.induct)
  case (4 fn es)
  then show ?case unfolding rview.simps by (intro keyed_view_fold keyed_view_bot) auto
qed (simp_all add: keyed_view_key keyed_view_columns[OF col_fd] keyed_view_bot)

lemma supported_row_guard: "row_ast C \<Longrightarrow> supported (row_guard C)"
  by (simp add: supported_def keyed_view_rview)

fun asem :: "('d, 'c, 'fn, 'ag) ast \<Rightarrow> ('k, ('d, 'c, 'fn, 'ag) slice, 'r, scalar datum) expr" where
  "asem (Dim d) = value_at (dim_lod d) (key_datum oo dim_val d)"
| "asem (Col c) = column (col_sec c) (dim_lod (col_dim c)) (col_val c)"
| "asem (Lit v) = value_at \<bottom> (\<Lambda> _. v)"
| "asem (Call fn es) = smap (fsym_sem fn_other fn) (collect (map asem es))"
| "asem (Aggr g e) = aggregate (requested e) (ag_sem g) (gate (asem e))"
| "asem (GroupBy ds e) = asem e"
| "asem (For ds C e) = filtfor (lod ds) {|C|} (asem e)"
| "asem (Where C e) = restrict (row_guard C) (asem e)"

text \<open>Well-formedness: every call has a number of arguments its symbol admits.\<close>

fun wf :: "('d, 'c, 'fn, 'ag) ast \<Rightarrow> bool" where
  "wf (Dim d) \<longleftrightarrow> True"
| "wf (Col c) \<longleftrightarrow> True"
| "wf (Lit v) \<longleftrightarrow> True"
| "wf (Call fn es) \<longleftrightarrow> fsym_arity fn_arity fn (length es) \<and> (\<forall>e\<in>set es. wf e)"
| "wf (Aggr g e) \<longleftrightarrow> wf e"
| "wf (GroupBy ds e) \<longleftrightarrow> wf e"
| "wf (For ds C e) \<longleftrightarrow> wf e"
| "wf (Where C e) \<longleftrightarrow> row_ast C \<and> wf e"

text \<open>The semantics is semilawful; gating it at the top gives the lawful expression.\<close>

theorem semilawful_asem: "wf e \<Longrightarrow> semilawful (asem e)"
proof (induct e rule: wf.induct)
  case (4 fn es)
  then show ?case by (auto intro!: semilawful_smap semilawful_collect)
next
  case (5 g e)
  then show ?case by (simp add: lawful_semilawful lawful_aggregate[OF lawful_gate ag_abel])
next
  case (8 C e)
  then show ?case by (simp add: semilawful_restrict supported_row_guard)
qed (simp_all add: semilawful_value_at semilawful_column[OF col_fd] semilawful_filtfor)

corollary lawful_gate_asem: "wf e \<Longrightarrow> lawful (gate (asem e))"
  by (rule lawful_gate[OF semilawful_asem])

text \<open>References to dimensions and columns and literals are row level, literals and aggregations
  total level; calls of row-level arguments are row level.\<close>

lemma row_level_Dim: "row_level (asem (Dim d))" and row_level_Col: "row_level (asem (Col c))"
  and row_level_Lit: "row_level (asem (Lit v))"
  and total_level_Lit: "total_level (asem (Lit v))" and total_level_Aggr: "total_level (asem (Aggr g e))"
  by (simp_all add: row_level_value_at row_level_column total_level_value_at_bot total_level_aggregate)

lemma row_level_Call: "(\<And>e. e \<in> set es \<Longrightarrow> row_level (asem e)) \<Longrightarrow> row_level (asem (Call fn es))"
  unfolding asem.simps row_level_smap by (rule row_level_collect) auto

end

end
