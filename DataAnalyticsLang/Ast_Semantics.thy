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
  "row_level E \<longleftrightarrow> (\<forall>e\<in>set (eguards E). row_guard_entry e) \<and> (\<forall>e\<in>set (evalues E). row_entry e)"

definition total_level :: "('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> bool" where
  "total_level E \<longleftrightarrow> emind E = \<bottom>"

lemma row_level_value_at: "row_level (value_at c g)"
  by (simp add: row_level_def row_entry_def row_guard_entry_def guard_keyed_gtrue)

lemma row_level_column: "row_level (column c a v)"
  by (simp add: row_level_def row_entry_def row_guard_entry_def guard_keyed_gtrue)

lemma total_level_value_at_bot: "total_level (value_at \<bottom> g)"
  by (simp add: total_level_def)

lemma row_level_smap: "row_level (smap g E) \<longleftrightarrow> row_level E"
  by (simp add: row_level_def)

lemma row_level_collect: "(\<And>E. E \<in> set Es \<Longrightarrow> row_level E) \<Longrightarrow> row_level (collect Es)"
  unfolding row_level_def collect_simps by auto

lemma total_level_aggregate: "total_level (aggregate f E)"
  by (simp add: total_level_def)

text \<open>The content graphs of a semilawful row-level expression have at most one element: the rows
  of a fiber agree on the key at the lower part, which determines the view.\<close>

lemma row_level_content_single:
  assumes E: "semilawful E" and r: "row_level E" and d: "conforms data" and e: "e \<in> set (evalues E)"
    and u: "u \<in> cgraph data e F k" and u': "u' \<in> cgraph data e F k"
  shows "u = u'"
proof -
  let ?G = "sel_at (esel e) (flod F)" and ?Y = "vfiber data e F k"
  obtain x where x: "x \<in> ?Y" using u by (auto simp: cgraph_def)
  have "cgraph data e F k = {cpair e x}"
    unfolding cgraph_def
  proof (rule row_entry_image[OF semilawful_wf[OF E e] _ d _ x lattice_join_ge1[of "elower e" "eupper e \<sqinter> flod F"]])
    show "row_entry e" using r e by (simp add: row_level_def)
    show "?Y \<subseteq> lower_maximal data" by (auto simp: vfiber_def fiber_def)
    show "rproj ?G y = rproj ?G x" if "y \<in> ?Y" for y
      using that x by (simp add: vfiber_def fiber_def)
  qed
  then show ?thesis using u u' by simp
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
    and fn_other :: "'fn \<Rightarrow> scalar datum list \<rightarrow> scalar datum"
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

definition row_guard :: "('d, 'c, 'fn, 'ag) ast \<Rightarrow> 'r guard" where
  "row_guard C = truth_d oo pval C oo vproj (rview C)"

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


fun asem :: "('d, 'c, 'fn, 'ag) ast \<Rightarrow> ('k, ('d, 'c, 'fn, 'ag) slice, 'r, scalar datum) expr" where
  "asem (Dim d) = value_at (dim_lod d) (key_datum oo dim_val d)"
| "asem (Col c) = column (col_sec c) (dim_lod (col_dim c)) (col_val c)"
| "asem (Lit v) = value_at \<bottom> (\<Lambda> _. v)"
| "asem (Call fn es) = smap (fsym_sem fn_other fn) (collect (map asem es))"
| "asem (Aggr g e) = aggregate (ag_sem g) (gate (requested e) (asem e))"
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
  then show ?case by (simp add: semilawful_restrict)
qed (simp_all add: semilawful_value_at semilawful_column[OF col_fd] semilawful_filtfor)

corollary lawful_gate_asem: "wf e \<Longrightarrow> lawful (gate \<bottom> (asem e))"
  by (rule lawful_gate[OF semilawful_asem])

text \<open>References to dimensions and columns and literals are row level, literals and aggregations
  total level; calls of row-level arguments are row level.\<close>

lemma row_level_Dim: "row_level (asem (Dim d))" and row_level_Col: "row_level (asem (Col c))"
  and row_level_Lit: "row_level (asem (Lit v))"
  and total_level_Lit: "total_level (asem (Lit v))" and total_level_Aggr: "total_level (asem (Aggr g e))"
  by (simp_all add: row_level_value_at row_level_column total_level_value_at_bot total_level_aggregate)

lemma row_level_Call: "(\<And>e. e \<in> set es \<Longrightarrow> row_level (asem e)) \<Longrightarrow> row_level (asem (Call fn es))"
  unfolding asem.simps row_level_smap by (rule row_level_collect) auto

section \<open>Row-level values from the content semantics\<close>

text \<open>On the point family of a row and a key, the content semantics of a row-level expression is
  its reading on the parts of that pair: the structural row reading is the content semantics at one
  row.  Key-level expressions, which read no columns, are read off the key alone.\<close>

lemma those_map_Some: "those (map Some xs) = Some xs"
  by (induct xs) simp_all

theorem csem_point: "row_ast e \<Longrightarrow> csem (asem e) (gpoint (eguards (asem e)) p)\<cdot>(point (evalues (asem e)) p) = Some (pval e\<cdot>p)"
proof (induct e rule: row_ast.induct)
  case (1 d)
  show ?case by (cases p) (simp add: dim_reads)
next
  case (2 c)
  show ?case by (cases p) (simp add: col_reads)
next
  case (4 fn es)
  let ?Es = "map asem es" and ?Q = "\<lambda>E. gpoint (eguards E) p" and ?P = "\<lambda>E. point (evalues E) p"
  have IH: "csem (asem e) (?Q (asem e))\<cdot>(?P (asem e)) = Some (pval e\<cdot>p)" if "e \<in> set es" for e
    using 4 that by simp
  have bg: "blocks (map (\<lambda>E. length (eguards E)) ?Es) (gpoint (concat (map eguards ?Es)) p) = map ?Q ?Es"
    unfolding gpoint_concat map_map comp_def
    using blocks_concat[of "\<lambda>E. gpoint (eguards E) p" ?Es] by (simp add: comp_def)
  have b: "blocks (map (\<lambda>E. length (evalues E)) ?Es) (point (concat (map evalues ?Es)) p) = map ?P ?Es"
    unfolding point_concat map_map comp_def
    using blocks_concat[of "\<lambda>E. point (evalues E) p" ?Es] by (simp add: comp_def)
  have z: "map2 (\<lambda>q Ys. csem (fst q) (snd q)\<cdot>Ys) (zip (map asem xs) (map (\<lambda>x. ?Q (asem x)) xs)) (map (\<lambda>x. ?P (asem x)) xs)
      = map (\<lambda>x. csem (asem x) (?Q (asem x))\<cdot>(?P (asem x))) xs" for xs
    by (induct xs) simp_all
  have m: "map2 (\<lambda>q Ys. csem (fst q) (snd q)\<cdot>Ys) (zip ?Es (map ?Q ?Es)) (map ?P ?Es) = map (\<lambda>e. Some (pval e\<cdot>p)) es"
    unfolding map_map comp_def z using IH by simp
  show ?case
    by (simp only: asem.simps smap_simps collect_simps collect_csem_def bg b m)
      (simp add: those_map_Some[of "map (\<lambda>e. pval e\<cdot>p) es", unfolded map_map comp_def] tuple_cfun_apply map_map comp_def)
qed simp_all

text \<open>Key-level expressions: dimensions, literals and calls, no columns.\<close>

fun key_ast :: "('d, 'c, 'fn, 'ag) ast \<Rightarrow> bool" where
  "key_ast (Dim d) \<longleftrightarrow> True"
| "key_ast (Lit v) \<longleftrightarrow> True"
| "key_ast (Call fn es) \<longleftrightarrow> fsym_arity fn_arity fn (length es) \<and> (\<forall>e\<in>set es. key_ast e)"
| "key_ast _ \<longleftrightarrow> False"

lemma key_ast_row_ast: "key_ast e \<Longrightarrow> row_ast e"
  by (induct e rule: key_ast.induct) auto

lemma pval_kval: "key_ast e \<Longrightarrow> pval e\<cdot>(r, k) = kval e\<cdot>k"
proof (induct e rule: key_ast.induct)
  case (3 fn es)
  then have m: "map (\<lambda>e. pval e\<cdot>(r, k)) es = map (\<lambda>e. kval e\<cdot>k) es" by simp
  show ?case by (simp only: pval.simps kval.simps cfcomp2 tuple_cfun_apply map_map comp_def m)
qed simp_all

text \<open>On data: at a key realised by a row of the frame, a row-level expression has the row
  reading of that row.  Its entries are row entries with no guard, so each content is the point
  content of the row.\<close>

lemma row_ast_wf: "row_ast e \<Longrightarrow> wf e"
  by (induct e rule: row_ast.induct) auto

lemma row_ast_row_level: "row_ast e \<Longrightarrow> row_level (asem e)"
  by (induct e rule: row_ast.induct) (auto simp: row_level_value_at row_level_column row_level_smap intro!: row_level_collect)

lemma row_ast_gtrue: "row_ast e \<Longrightarrow> e' \<in> set (eguards (asem e)) \<Longrightarrow> eguard e' = gtrue"
  by (induct e arbitrary: e' rule: row_ast.induct) auto

theorem esem_row_ast:
  assumes e: "row_ast e" and d: "conforms data" and xm: "x \<in> lower_maximal data" and xF: "frows F x"
    and kx: "k = rproj (kd (asem e) F) x"
  shows "esem (asem e) data F k = Some (pval e\<cdot>(x, rkey\<cdot>x))"
proof -
  have ES: "semilawful (asem e)" by (rule semilawful_asem[OF row_ast_wf[OF e]])
  have k: "proj (kd (asem e) F)\<cdot>k = k" by (simp add: kx)
  have g: "gcontents data (eguards (asem e)) F k = gpoint (eguards (asem e)) (x, rkey\<cdot>x)"
    unfolding gpoint_def
  proof (rule map_cong[OF refl])
    fix e' assume e': "e' \<in> set (eguards (asem e))"
    let ?G = "sel_at (esel e') (flod F)" and ?Y = "group data (elower e') (eupper e') F k"
    have Gk: "proj ?G\<cdot>k = rproj ?G x" unfolding kx by (rule proj_le[OF group_below_kd[OF ES esels_guardI[OF e']]])
    have xY: "x \<in> ?Y" using xm xF Gk by (simp add: group_def frows_def holds_coarsen)
    have r: "row_guard_entry e'" using row_ast_row_level[OF e] e' by (simp add: row_level_def)
    have "(\<lambda>y. rproj (ekeys e') y) ` {y \<in> ?Y. eguard e'\<cdot>y = TT} = (if eguard e'\<cdot>x = TT then {rproj (ekeys e') x} else {})"
      by (rule row_guard_entry_image[OF r d _ xY lattice_join_ge1]) (auto simp: group_def Gk)
    then show "gcontent data e' F k = {proj (ekeys e')\<cdot>(snd (x, rkey\<cdot>x))}"
      by (simp add: gcontent_def gfiber_def row_ast_gtrue[OF e e'])
  qed
  have "contents data (evalues (asem e)) F k = point (evalues (asem e)) (x, rkey\<cdot>x)"
    unfolding point_def
  proof (rule map_cong[OF refl])
    fix e' assume e': "e' \<in> set (evalues (asem e))"
    let ?G = "sel_at (esel e') (flod F)" and ?Y = "vfiber data e' F k"
    have Gk: "proj ?G\<cdot>k = rproj ?G x" unfolding kx by (rule proj_le[OF group_below_kd[OF ES esels_valueI[OF e']]])
    have xY: "x \<in> ?Y" using xm Gk by (simp add: vfiber_def fiber_def)
    have r: "row_entry e'" using row_ast_row_level[OF e] e' by (simp add: row_level_def)
    have "cpair e' ` ?Y = {cpair e' x}"
      by (rule row_entry_image[OF semilawful_wf[OF ES e'] r d _ xY lattice_join_ge1])
        (auto simp: vfiber_def fiber_def Gk)
    then show "content data e' F k = [proj (ekeys e')\<cdot>(snd (x, rkey\<cdot>x)) \<mapsto> fst (x, rkey\<cdot>x) \<downharpoonright> ecols e']"
      by (simp add: content_def cgraph_def cpair_def)
  qed
  then show ?thesis by (simp only: semilawful_csem[OF ES d k] g csem_point[OF e])
qed

corollary csem_point_key: "key_ast e \<Longrightarrow> csem (asem e) (gpoint (eguards (asem e)) (r, k))\<cdot>(point (evalues (asem e)) (r, k)) = Some (kval e\<cdot>k)"
  by (simp only: csem_point[OF key_ast_row_ast] pval_kval)

end

end
