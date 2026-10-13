theory SList
  imports "HOLCF-extra.Domain_Order_Derive"
begin

section \<open>Strict lists: a recursive test case for instance derivation\<close>

domain ('v::"domain") slist = SNil | SCons 'v "'v slist"

text \<open>Both fields are strict, so recursion and the element type both pass through \<open>\<otimes>\<close>: the element
  type must itself be separated for distributivity.  Only the package's
  @{thm [source] slist_map_def}, @{thm [source] slist.iso_rews} and @{thm [source] slist_map_ID}
  are used.  The map rules are registered in @{attribute domain_category_map}, so types nesting
  @{typ "'v slist"} can use them.  The classes are derived in dependency order: distributivity
  of \<open>\<otimes>\<close> needs the recursive occurrence bounded complete and separated, so those two instances
  come first.\<close>

lemma bounded_complete_defl_slist_map [domain_category_map]:
  "bounded_complete_defl v \<Longrightarrow> bounded_complete_defl (slist_map\<cdot>v)"
  by (domain_category_map_rule map_def: slist_map_def iso_rews: slist.iso_rews)

lemma filter_sum_defl_slist_map [domain_category_map]:
  "filter_sum_defl v \<Longrightarrow> filter_sum_defl (slist_map\<cdot>v)"
  by (domain_category_map_rule map_def: slist_map_def iso_rews: slist.iso_rews)

instance slist :: ("{domain, bounded_complete}") bounded_complete
  by (domain_category_instance map_ID: slist_map_ID)

instance slist :: ("{domain, filter_sum}") filter_sum
  by (domain_category_instance map_ID: slist_map_ID)

lemma separated_sum_defl_slist_map [domain_category_map]:
  "separated_sum_defl v \<Longrightarrow> separated_sum_defl (slist_map\<cdot>v)"
  by (domain_category_map_rule map_def: slist_map_def iso_rews: slist.iso_rews)

instance slist :: ("{domain, separated_sum}") separated_sum
  by (domain_category_instance map_ID: slist_map_ID)

lemma distributive_defl_slist_map [domain_category_map]:
  "distributive_defl (v :: 'v::{domain, bounded_complete, filter_sum} \<rightarrow> 'v) \<Longrightarrow>
    distributive_defl (slist_map\<cdot>v)"
  by (domain_category_map_rule map_def: slist_map_def iso_rews: slist.iso_rews)

instance slist :: ("{domain, distributive_cpo, filter_sum}") distributive_cpo
  by (domain_category_instance map_ID: slist_map_ID)

subsection \<open>Lazy streams\<close>

domain ('v::"domain") lstream = LSCons (lazy 'v) (lazy "'v lstream")

text \<open>Recursion only through lazy fields, i.e. under \<open>u_map\<close>: no separation needed for \<open>\<otimes>\<close>.\<close>

lemma bounded_complete_defl_lstream_map [domain_category_map]:
  "bounded_complete_defl v \<Longrightarrow> bounded_complete_defl (lstream_map\<cdot>v)"
  by (domain_category_map_rule map_def: lstream_map_def iso_rews: lstream.iso_rews)

lemma filter_sum_defl_lstream_map [domain_category_map]:
  "deflation v \<Longrightarrow> filter_sum_defl (lstream_map\<cdot>v)"
  by (domain_category_map_rule map_def: lstream_map_def iso_rews: lstream.iso_rews)

instance lstream :: ("{domain, bounded_complete}") bounded_complete
  by (domain_category_instance map_ID: lstream_map_ID)

instance lstream :: ("domain") filter_sum
  by (domain_category_instance map_ID: lstream_map_ID)

lemma separated_sum_defl_lstream_map [domain_category_map]:
  "deflation v \<Longrightarrow> separated_sum_defl (lstream_map\<cdot>v)"
  by (domain_category_map_rule map_def: lstream_map_def iso_rews: lstream.iso_rews)

instance lstream :: ("domain") separated_sum
  by (domain_category_instance map_ID: lstream_map_ID)

lemma distributive_defl_lstream_map [domain_category_map]:
  "distributive_defl v \<Longrightarrow> distributive_defl (lstream_map\<cdot>v)"
  by (domain_category_map_rule map_def: lstream_map_def iso_rews: lstream.iso_rews)

instance lstream :: ("{domain, distributive_cpo}") distributive_cpo
  by (domain_category_instance map_ID: lstream_map_ID)

end
