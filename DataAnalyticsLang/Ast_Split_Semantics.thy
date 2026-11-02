theory Ast_Split_Semantics
  imports Ast_Semantics Split_Exact
begin

section \<open>The extended semantics of the query language\<close>

text \<open>An AST space whose row keys are the split datasets' keys.  Each AST node denotes the
  extended combinator over the extended denotations of its children: its rigid part is the rigid
  denotation, and it is lawful in the extended sense on well-formed ASTs.\<close>

locale ast_split_space = ast_space dim_lod dim_val key_dims fn_other col_sec col_dim col_val fn_arity ag_sem
  + split_keyed
  for dim_lod :: "'d \<Rightarrow> 'k::{domain, lod_domain} semi_factor"
    and dim_val :: "'d \<Rightarrow> 'k \<rightarrow> scalar datum" and key_dims :: "'k \<Rightarrow> 'd list"
    and fn_other :: "'fn \<Rightarrow> scalar datum list \<rightarrow> scalar datum"
    and col_sec :: "'c \<Rightarrow> 'r::{domain, lod_domain, schema} semi_factor" and col_dim :: "'c \<Rightarrow> 'd" and col_val :: "'c \<Rightarrow> 'r \<rightarrow> scalar datum"
    and fn_arity :: "'fn \<Rightarrow> nat \<Rightarrow> bool"
    and ag_sem :: "'ag \<Rightarrow> scalar datum \<rightarrow> scalar datum \<rightarrow> scalar datum"
begin

sublocale split_dataspace "ast_slicing :: (('d, 'c, 'fn, 'ag) slice, 'k) slicer_ops"
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
  then show ?case by (simp add: ext_lawful_include_dims lod_small_compact compact_lod)
next
  case (7 ds C e)
  then show ?case by (simp add: ext_lawful_filtfor)
next
  case (8 C e)
  then show ?case by (simp add: ext_lawful_restrict)
qed (simp_all add: ext_lawful_smap ext_lawful_key_at ext_lawful_column [OF col_fd lod_small_compact [OF dim_compact] col_small] lod_small_compact dim_compact)

text \<open>Without \<open>WHERE\<close>, the extended denotation is exact: row guards are the one construct
  that only confirms presence.\<close>

fun where_free :: "('d, 'c, 'fn, 'ag) ast \<Rightarrow> bool" where
  "where_free (Call fn es) \<longleftrightarrow> (\<forall>e\<in>set es. where_free e)"
| "where_free (Aggr g e) \<longleftrightarrow> where_free e"
| "where_free (GroupBy ds e) \<longleftrightarrow> where_free e"
| "where_free (For ds C e) \<longleftrightarrow> where_free e"
| "where_free (Where C e) \<longleftrightarrow> False"
| "where_free _ \<longleftrightarrow> True"

theorem ext_exact_asem: "wf e \<Longrightarrow> where_free e \<Longrightarrow> ext_exact (asem_ext e)"
proof (induct e rule: wf.induct)
  case (4 fn es)
  then show ?case by (auto intro!: ext_exact_smap ext_exact_tuple)
next
  case (5 g e)
  then have s: "semilawful (asem_ext e)" and so: "ext_sound (asem_ext e)" and ex: "ext_exact (asem_ext e)"
    using ext_lawful_asem [of e] by (simp_all add: ext_lawful_def)
  show ?case unfolding asem_ext.simps by (rule ext_exact_aggregate [OF ag_abel s ex so])
next
  case (6 ds e)
  then show ?case using ext_lawful_asem [of e] by (simp add: ext_lawful_def ext_exact_include_dims)
next
  case (7 ds C e)
  then show ?case using ext_lawful_asem [of e] by (simp add: ext_lawful_def ext_exact_filtfor)
next
  case (8 C e)
  then show ?case by simp
qed (simp_all add: ext_exact_smap ext_exact_key_at ext_exact_column)

corollary ext_lawful_present_asem: "wf e \<Longrightarrow> ext_lawful (present_at_ext \<bottom> \<top> (asem_ext e))"
  by (rule ext_lawful_present_at [OF ext_lawful_asem lod_small_bot])

text \<open>The minimal LODs of the denotations are small: dimensions and columns have compact LODs,
  and the combinators join, keep, or drop them, or raise them by small dimensions.\<close>

lemma lod_small_include_dims:
  assumes E: "semilawful E" and M: "lod_small M" and s: "lod_small (emind E)"
  shows "lod_small (emind (include_dims M E))"
proof -
  have "fold (\<squnion>) (map (\<lambda>S. lower_part (include_sel M S)) (esels E)) \<bottom> \<sqsubseteq> emind E \<squnion> M"
  proof (rule fold_join_least)
    fix x assume "x \<in> set (map (\<lambda>S. lower_part (include_sel M S)) (esels E))"
    then obtain S where S: "S \<in> set (esels E)" and x: "x = lower_part (include_sel M S)" by auto
    show "x \<sqsubseteq> emind E \<squnion> M" unfolding x include_sel_simps
      by (rule lattice_join_mono [OF lower_below_mind [OF E S] truncate_below])
  qed simp
  then show ?thesis by (simp only: include_dims_simps) (rule lod_small_below [OF lod_small_sup [OF s M]])
qed

lemma lod_small_tuple: "(\<And>E. E \<in> set Es \<Longrightarrow> lod_small (emind E)) \<Longrightarrow> lod_small (emind (tuple Es))"
  by (induct Es) (simp_all add: lod_small_sup lod_small_compact)

theorem lod_small_asem: "wf e \<Longrightarrow> lod_small (emind (asem e))"
proof (induct e rule: wf.induct)
  case (4 fn es)
  then show ?case by (auto intro!: lod_small_tuple)
next
  case (6 ds e)
  then show ?case by (simp only: asem.simps) (rule lod_small_include_dims [OF semilawful_asem lod_small_compact [OF compact_lod]], simp_all)
qed (simp_all add: lod_small_compact dim_compact)

theorem ext_cont_asem: "wf e \<Longrightarrow> ext_cont (asem_ext e)"
proof (induct e rule: wf.induct)
  case (1 d)
  show ?case by (simp add: ext_cont_smap ext_cont_key_at lod_small_compact dim_compact)
next
  case (2 c)
  show ?case by (simp add: ext_cont_column [OF col_fd lod_small_compact [OF dim_compact]])
next
  case (3 v)
  show ?case by (simp add: ext_cont_smap ext_cont_key_at lod_small_compact)
next
  case (4 fn es)
  then show ?case by (auto intro!: ext_cont_smap ext_cont_tuple)
next
  case (5 g e)
  have we: "wf e" using 5(2) by simp
  have s: "lod_small (emind (asem_ext e))"
    using lod_small_asem [OF we] arg_cong [OF truncate_asem_ext [of e], of emind] by simp
  show ?case unfolding asem_ext.simps by (rule ext_cont_aggregate [OF ag_abel 5(1) [OF we] s])
next
  case (6 ds e)
  then show ?case by (simp add: ext_cont_include_dims lod_small_compact compact_lod)
next
  case (7 ds C e)
  then show ?case by (simp add: ext_cont_filtfor)
next
  case (8 C e)
  then show ?case by (simp add: ext_cont_restrict)
qed

corollary ext_cont_present_asem: "wf e \<Longrightarrow> ext_cont (present_at_ext \<bottom> \<top> (asem_ext e))"
proof -
  assume e: "wf e"
  have "lod_small (emind (asem_ext e) \<squnion> \<bottom>)"
    using lod_small_asem [OF e] arg_cong [OF truncate_asem_ext [of e], of emind] by simp
  then show ?thesis by (rule ext_cont_present_at [OF _ ext_cont_asem [OF e]])
qed

end

end
