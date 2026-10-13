theory Derive_Examples
  imports SList
begin

section \<open>More derivations: several parameters, nested recursion\<close>

subsection \<open>Two parameters\<close>

text \<open>Recursion through \<open>\<otimes>\<close> (strict fields), so separation is derived first.\<close>

domain ('a::"domain", 'b::"domain") tree2 =
  Leaf (lazy 'a) | Node (lazy 'b) "('a, 'b) tree2" "('a, 'b) tree2"

lemma bounded_complete_defl_tree2_map [domain_category_map]:
  "bounded_complete_defl v \<Longrightarrow> bounded_complete_defl w \<Longrightarrow> bounded_complete_defl (tree2_map\<cdot>v\<cdot>w)"
  by (domain_category_map_rule map_def: tree2_map_def iso_rews: tree2.iso_rews)

lemma separated_defl_tree2_map [domain_category_map]:
  "deflation v \<Longrightarrow> deflation w \<Longrightarrow> separated_defl (tree2_map\<cdot>v\<cdot>w)"
  by (domain_category_map_rule map_def: tree2_map_def iso_rews: tree2.iso_rews)

lemma separating_defl_tree2_map [domain_category_map]:
  "deflation v \<Longrightarrow> deflation w \<Longrightarrow> separating_defl (tree2_map\<cdot>v\<cdot>w)"
  by (domain_category_map_rule map_def: tree2_map_def iso_rews: tree2.iso_rews)

lemma distributive_defl_tree2_map [domain_category_map]:
  "distributive_defl v \<Longrightarrow> distributive_defl w \<Longrightarrow> distributive_defl (tree2_map\<cdot>v\<cdot>w)"
  by (domain_category_map_rule map_def: tree2_map_def iso_rews: tree2.iso_rews
      fix_facts: separating_defl_tree2_map)

instance tree2 :: ("{domain, bounded_complete}", "{domain, bounded_complete}") bounded_complete
  by (domain_category_instance map_ID: tree2_map_ID)

instance tree2 :: ("domain", "domain") separated_po
  by (domain_category_instance map_ID: tree2_map_ID)

instance tree2 :: ("{domain, distributive_cpo}", "{domain, distributive_cpo}") distributive_cpo
  by (domain_category_instance map_ID: tree2_map_ID)

subsection \<open>No parameters\<close>

text \<open>The package still defines \<open>nat2_map \<equiv> \<mu> f. \<dots>\<close>, with no \<open>\<Lambda>\<close> to reduce.\<close>

domain nat2 = Z | S (lazy "one") nat2

lemma bounded_complete_defl_nat2_map [domain_category_map]: "bounded_complete_defl nat2_map"
  by (domain_category_map_rule map_def: nat2_map_def iso_rews: nat2.iso_rews)

lemma separating_defl_nat2_map [domain_category_map]: "separating_defl nat2_map"
  by (domain_category_map_rule map_def: nat2_map_def iso_rews: nat2.iso_rews)

lemma distributive_defl_nat2_map [domain_category_map]: "distributive_defl nat2_map"
  by (domain_category_map_rule map_def: nat2_map_def iso_rews: nat2.iso_rews
      fix_facts: separating_defl_nat2_map)

instance nat2 :: bounded_complete
  by (domain_category_instance map_ID: nat2_map_ID)

instance nat2 :: distributive_cpo
  by (domain_category_instance map_ID: nat2_map_ID)

subsection \<open>Nested recursion\<close>

text \<open>The recursive occurrence sits under @{typ "'v slist"}; the map rules registered for
  \<open>slist\<close> carry the derivation through it.\<close>

domain ('a::"domain") rose = Rose (lazy 'a) "'a rose slist"

lemma bounded_complete_defl_rose_map [domain_category_map]:
  "bounded_complete_defl v \<Longrightarrow> bounded_complete_defl (rose_map\<cdot>v)"
  by (domain_category_map_rule map_def: rose_map_def iso_rews: rose.iso_rews)

lemma separated_defl_rose_map [domain_category_map]:
  "deflation v \<Longrightarrow> separated_defl (rose_map\<cdot>v)"
  by (domain_category_map_rule map_def: rose_map_def iso_rews: rose.iso_rews)

lemma separating_defl_rose_map [domain_category_map]:
  "deflation v \<Longrightarrow> separating_defl (rose_map\<cdot>v)"
  by (domain_category_map_rule map_def: rose_map_def iso_rews: rose.iso_rews)

lemma distributive_defl_rose_map [domain_category_map]:
  "distributive_defl v \<Longrightarrow> distributive_defl (rose_map\<cdot>v)"
  by (domain_category_map_rule map_def: rose_map_def iso_rews: rose.iso_rews)

instance rose :: ("{domain, bounded_complete}") bounded_complete
  by (domain_category_instance map_ID: rose_map_ID)

instance rose :: ("domain") separated_po
  by (domain_category_instance map_ID: rose_map_ID)

instance rose :: ("{domain, distributive_cpo}") distributive_cpo
  by (domain_category_instance map_ID: rose_map_ID)

end

