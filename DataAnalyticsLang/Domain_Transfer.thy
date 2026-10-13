theory Domain_Transfer
  imports LOD_Factor "HOLCF-extra.Domain_Order_Derive"
begin

section \<open>Transferring the classes along domain isomorphisms\<close>

text \<open>The domain package presents each domain as isomorphic, through \<open>abs\<close> and \<open>rep\<close> satisfying
  the laws of @{locale iso}, to a combination of its constructor arguments.  The order-theoretic
  transfer (bounds, lubs, meets; @{text bounded_complete_iso}, @{text distributive_cpo_iso}) is in
  \<open>HOLCF-extra.Domain_Order\<close>; levels of detail transfer by conjugation with the isomorphism
  (@{thm [source] semi_factor_defl_iso}, @{thm [source] finitary_iso} in \<open>LOD_Factor\<close>).\<close>

lemma locally_finitely_detailed_iso:
  fixes abs :: "'r::locally_finitely_detailed \<rightarrow> 't::{bifinite, distributive_cpo}" and rep
  assumes "iso abs rep" shows "OFCLASS('t, locally_finitely_detailed_class)"
proof intro_classes
  interpret iso abs rep by fact
  fix k :: 't assume "compact k"
  then have "compact (rep\<cdot>k)" by (rule compact_rep)
  from compact_level[OF this, unfolded ex_finitary_semi_factor_iff] obtain e
    where e: "semi_factor_defl e" "finitary e" "e\<cdot>(rep\<cdot>k) = rep\<cdot>k" by blast
  show "\<exists>F. finitary_semi_factor F \<and> k \<downharpoonright> F = k"
    unfolding ex_finitary_semi_factor_iff
    using e by (intro exI[of _ "abs oo e oo rep"])
      (simp add: semi_factor_defl_iso[OF abs_iso rep_iso] finitary_iso[OF abs_iso rep_iso])
qed

section \<open>Example: a non-recursive domain\<close>

text \<open>A lazy binary sum is represented by \<open>'a u \<oplus> 'b u\<close>; every class transfers from the
  combinator instances.\<close>

domain ('a::"domain", 'b::"domain") either = L (lazy 'a) | R (lazy 'b)

lemma either_iso: "iso either_abs either_rep"
  by unfold_locales (rule either.abs_iso, rule either.rep_iso)

text \<open>Finitary levels are not admissible, but \<open>either\<close> is not recursive, so the map rule goes
  through without fixed-point induction.\<close>

lemma finitary_either_map [domain_category_map]:
  "finitary v \<Longrightarrow> finitary w \<Longrightarrow> finitary (either_map\<cdot>v\<cdot>w)"
  by (domain_category_map_rule map_def: either_map_def iso_rews: either.iso_rews)

instance either :: ("{domain, bounded_complete}", "{domain, bounded_complete}") bounded_complete
  by (rule bounded_complete_iso[OF either_iso])

instance either :: ("{domain, distributive_cpo}", "{domain, distributive_cpo}") distributive_cpo
  by (rule distributive_cpo_iso[OF either_iso])

instance either :: ("{domain, locally_finitely_detailed}", "{domain, locally_finitely_detailed}")
  locally_finitely_detailed
  by (rule locally_finitely_detailed_iso[OF either_iso])

section \<open>Example: a recursive domain\<close>

text \<open>Strict lists recurse through \<open>\<otimes>\<close>.  The classes are derived in dependency order; local
  finite detail needs the components of the smash product, here the element type and the
  recursive occurrence, to be separated sums.\<close>

domain ('a::"domain") sseq = SNil | SCons 'a "'a sseq"

lemma bounded_complete_defl_sseq_map [domain_category_map]:
  "bounded_complete_defl v \<Longrightarrow> bounded_complete_defl (sseq_map\<cdot>v)"
  by (domain_category_map_rule map_def: sseq_map_def iso_rews: sseq.iso_rews)

lemma filter_sum_defl_sseq_map [domain_category_map]:
  "filter_sum_defl v \<Longrightarrow> filter_sum_defl (sseq_map\<cdot>v)"
  by (domain_category_map_rule map_def: sseq_map_def iso_rews: sseq.iso_rews)

lemma separated_sum_defl_sseq_map [domain_category_map]:
  "separated_sum_defl v \<Longrightarrow> separated_sum_defl (sseq_map\<cdot>v)"
  by (domain_category_map_rule map_def: sseq_map_def iso_rews: sseq.iso_rews)

instance sseq :: ("{domain, bounded_complete}") bounded_complete
  by (domain_category_instance map_ID: sseq_map_ID)

instance sseq :: ("{domain, filter_sum}") filter_sum
  by (domain_category_instance map_ID: sseq_map_ID)

instance sseq :: ("{domain, separated_sum}") separated_sum
  by (domain_category_instance map_ID: sseq_map_ID)

lemma distributive_defl_sseq_map [domain_category_map]:
  "distributive_defl (v :: 'a::{domain, bounded_complete, filter_sum} \<rightarrow> 'a) \<Longrightarrow>
    distributive_defl (sseq_map\<cdot>v)"
  by (domain_category_map_rule map_def: sseq_map_def iso_rews: sseq.iso_rews)

instance sseq :: ("{domain, distributive_cpo, filter_sum}") distributive_cpo
  by (domain_category_instance map_ID: sseq_map_ID)

lemma locally_finitely_detailed_defl_sseq_map [domain_category_map]:
  "locally_finitely_detailed_defl (v :: 'a::{domain, distributive_cpo, separated_sum} \<rightarrow> 'a) \<Longrightarrow>
    locally_finitely_detailed_defl (sseq_map\<cdot>v)"
  by (domain_category_map_rule map_def: sseq_map_def iso_rews: sseq.iso_rews)

instance sseq :: ("{domain, separated_sum, locally_finitely_detailed}") locally_finitely_detailed
  by (domain_category_instance map_ID: sseq_map_ID)


end
