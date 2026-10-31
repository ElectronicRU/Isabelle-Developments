theory Ast_Split_Semantics
  imports Ast_Semantics Split_Semantics
begin

section \<open>The extended semantics of the query language\<close>

text \<open>An AST space whose row keys are the split datasets' keys.  Each AST node denotes the
  extended combinator over the extended denotations of its children: its rigid part is the rigid
  denotation, and it is lawful in the extended sense on well-formed ASTs.\<close>

locale ast_split_space = ast_space dim_lod dim_val key_dims fn_other rules keying col_sec col_dim col_val fn_arity ag_sem
  + split_keyed keying
  for dim_lod :: "'d \<Rightarrow> 'k::{domain, lod_domain} semi_factor"
    and dim_val :: "'d \<Rightarrow> 'k \<rightarrow> scalar datum" and key_dims :: "'k \<Rightarrow> 'd list"
    and fn_other :: "'fn \<Rightarrow> scalar datum list \<rightarrow> scalar datum"
    and rules :: "'r::{domain, lod_domain} schema_rules" and keying :: "('r, 'k) keying"
    and col_sec :: "'c \<Rightarrow> 'r semi_factor" and col_dim :: "'c \<Rightarrow> 'd" and col_val :: "'c \<Rightarrow> 'r \<rightarrow> scalar datum"
    and fn_arity :: "'fn \<Rightarrow> nat \<Rightarrow> bool"
    and ag_sem :: "'ag \<Rightarrow> scalar datum \<rightarrow> scalar datum \<rightarrow> scalar datum"
begin

sublocale split_dataspace "ast_slicing :: (('d, 'c, 'fn, 'ag) slice, 'k) slicer_ops" rules keying
  by unfold_locales

fun asem_ext :: "('d, 'c, 'fn, 'ag) ast \<Rightarrow> ('k, ('d, 'c, 'fn, 'ag) slice, 'r, scalar datum) expr_ext" where
  "asem_ext (Dim d) = value_at_ext (dim_lod d) (dim_val d)"
| "asem_ext (Col c) = column_ext (col_sec c) (dim_lod (col_dim c)) (col_val c)"
| "asem_ext (Lit v) = value_at_ext \<bottom> (\<Lambda> _. v)"
| "asem_ext (Call fn es) = smap_ext (fup\<cdot>(fsym_sem fn_other fn)) (tuple_ext (map asem_ext es))"
| "asem_ext (Aggr g e) = aggregate_ext (ag_sem g) (asem_ext e)"
| "asem_ext (GroupBy ds e) = include_dims_ext (lod ds) (asem_ext e)"
| "asem_ext (For ds C e) = filtfor_ext (lod ds) {|C|} (asem_ext e)"
| "asem_ext (Where C e) = restrict_ext (row_guard C) (asem_ext e)"

text \<open>The rigid part is the rigid denotation.\<close>

theorem truncate_asem_ext: "expr.truncate (asem_ext e) = asem e"
proof (induct e rule: asem_ext.induct)
  case (4 fn es)
  have m: "map (expr.truncate \<circ> asem_ext) es = map asem es" by (rule map_cong [OF refl]) (simp add: 4)
  show ?case unfolding asem_ext.simps asem.simps truncate_ext_simps truncate_tuple_ext map_map m ..
qed (simp_all add: truncate_ext_simps value_at_def)

theorem ext_lawful_asem: "wf e \<Longrightarrow> ext_lawful (asem_ext e)"
proof (induct e rule: wf.induct)
  case (4 fn es)
  then show ?case by (auto intro!: ext_lawful_smap ext_lawful_tuple)
next
  case (5 g e)
  then have "semilawful (asem_ext e)" "ext_sound (asem_ext e)" by (simp_all add: ext_lawful_def)
  then show ?case unfolding asem_ext.simps by (rule ext_lawful_aggregate [OF _ _ ag_abel])
next
  case (6 ds e)
  then show ?case by (simp add: ext_lawful_include_dims)
next
  case (7 ds C e)
  then show ?case by (simp add: ext_lawful_filtfor)
next
  case (8 C e)
  then show ?case by (simp add: ext_lawful_restrict)
qed (simp_all add: ext_lawful_smap ext_lawful_key_at ext_lawful_column [OF col_fd])

corollary ext_lawful_present_asem: "wf e \<Longrightarrow> ext_lawful (present_at_ext \<bottom> \<top> (asem_ext e))"
  by (rule ext_lawful_present_at [OF ext_lawful_asem])

end

end
