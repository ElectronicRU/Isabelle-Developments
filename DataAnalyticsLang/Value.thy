theory Value
  imports LOD "HOLCF-extra.Domain_Order_Derive"
begin

section \<open>Transferring the classes along domain isomorphisms\<close>

text \<open>The domain package presents each domain as isomorphic, through \<open>abs\<close> and \<open>rep\<close> satisfying
  the laws of @{locale iso}, to a combination of its constructor arguments.  The order-theoretic
  transfer (bounds, lubs, meets; @{text bounded_complete_iso}, @{text distributive_cpo_iso}) is in
  \<open>HOLCF-extra.Domain_Order\<close>; levels of detail transfer by conjugation with the isomorphism
  (@{thm [source] semi_factor_defl_iso}, @{thm [source] finitary_iso} in \<open>LOD\<close>).\<close>

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

section \<open>Values\<close>

text \<open>Bottom is a data-quality lapse or divergence: a dangling foreign key, a failed cast, a
  short row.  Missing values that are not lapses live at three levels.
  \<^item> \<^emph>\<open>Data\<close> (records and record-level expressions), @{text "'v datum"}: \<open>NA\<close> (not
    applicable; joins through it give \<open>NA\<close>), \<open>Val\<cdot>Null\<close> (present but unknown; joins
    through it give \<open>\<bottom>\<close>), or a known value.  Source nulls map to one of the two per column.
  \<^item> \<^emph>\<open>Keys\<close> (dimensions), @{text "'v with_na"}: nulls become \<open>NA\<close>, which can be pinned
    (@{text to_key}).
  \<^item> \<^emph>\<open>Measures\<close>, @{text "'v with_null"}: \<open>NA\<close> becomes \<open>\<bottom>\<close>, i.e.\ no entry
    (@{text from_na}); aggregations treat \<open>\<bottom>\<close> and \<open>NA\<close> alike.
  A record-level function is \<^emph>\<open>NA-blind\<close> when it commutes with @{text squash}, the
  projection forgetting \<open>NA\<close>; lifted operators are, coalescing is not.\<close>

subsection \<open>Scalars\<close>

text \<open>Scalars have strict fields, so there are no per-type roots: @{text scalar} is flat.\<close>

domain scalar = SBool tr | SInt "int lift"

lemma bounded_complete_defl_scalar_map [domain_category_map]: "bounded_complete_defl scalar_map"
  by (domain_category_map_rule map_def: scalar_map_def iso_rews: scalar.iso_rews)

lemma separated_sum_defl_scalar_map [domain_category_map]: "separated_sum_defl scalar_map"
  by (domain_category_map_rule map_def: scalar_map_def iso_rews: scalar.iso_rews)

instance scalar :: bounded_complete
  by (domain_category_instance map_ID: scalar_map_ID)

instance scalar :: separated_sum
  by (domain_category_instance map_ID: scalar_map_ID)

lemma distributive_defl_scalar_map [domain_category_map]: "distributive_defl scalar_map"
  by (domain_category_map_rule map_def: scalar_map_def iso_rews: scalar.iso_rews)

instance scalar :: distributive_cpo
  by (domain_category_instance map_ID: scalar_map_ID)

lemma locally_finitely_detailed_defl_scalar_map [domain_category_map]:
  "locally_finitely_detailed_defl scalar_map"
  by (domain_category_map_rule map_def: scalar_map_def iso_rews: scalar.iso_rews)

instance scalar :: locally_finitely_detailed
  by (domain_category_instance map_ID: scalar_map_ID)

subsection \<open>Measures: values with nulls\<close>

domain ('v::"domain") with_null = Null | Known 'v

lemma bounded_complete_defl_with_null_map [domain_category_map]:
  "bounded_complete_defl v \<Longrightarrow> bounded_complete_defl (with_null_map\<cdot>v)"
  by (domain_category_map_rule map_def: with_null_map_def iso_rews: with_null.iso_rews)

lemma separated_sum_defl_with_null_map [domain_category_map]:
  "separated_sum_defl v \<Longrightarrow> separated_sum_defl (with_null_map\<cdot>v)"
  by (domain_category_map_rule map_def: with_null_map_def iso_rews: with_null.iso_rews)

instance with_null :: ("{domain, bounded_complete}") bounded_complete
  by (domain_category_instance map_ID: with_null_map_ID)

instance with_null :: ("{domain, separated_sum}") separated_sum
  by (domain_category_instance map_ID: with_null_map_ID)

lemma distributive_defl_with_null_map [domain_category_map]:
  "distributive_defl (v :: 'a::{domain, bounded_complete} \<rightarrow> 'a) \<Longrightarrow>
    distributive_defl (with_null_map\<cdot>v)"
  by (domain_category_map_rule map_def: with_null_map_def iso_rews: with_null.iso_rews)

instance with_null :: ("{domain, distributive_cpo}") distributive_cpo
  by (domain_category_instance map_ID: with_null_map_ID)

lemma locally_finitely_detailed_defl_with_null_map [domain_category_map]:
  "locally_finitely_detailed_defl (v :: 'a::{domain, distributive_cpo, separated_sum} \<rightarrow> 'a) \<Longrightarrow>
    locally_finitely_detailed_defl (with_null_map\<cdot>v)"
  by (domain_category_map_rule map_def: with_null_map_def iso_rews: with_null.iso_rews)

instance with_null :: ("{domain, separated_sum, locally_finitely_detailed}") locally_finitely_detailed
  by (domain_category_instance map_ID: with_null_map_ID)

subsection \<open>Keys: values with NA\<close>

text \<open>The lazy root \<open>Val\<cdot>\<bottom>\<close> is ``not \<open>NA\<close>, value not observed'': it gives the not-null
  level of detail.  Keys from data are maximal and never take that value.\<close>

domain ('a::"domain") with_na = NA | Val (lazy 'a)

lemma bounded_complete_defl_with_na_map [domain_category_map]:
  "bounded_complete_defl v \<Longrightarrow> bounded_complete_defl (with_na_map\<cdot>v)"
  by (domain_category_map_rule map_def: with_na_map_def iso_rews: with_na.iso_rews)

lemma filter_sum_defl_with_na_map [domain_category_map]:
  "filter_sum_defl v \<Longrightarrow> filter_sum_defl (with_na_map\<cdot>v)"
  by (domain_category_map_rule map_def: with_na_map_def iso_rews: with_na.iso_rews)

lemma separated_sum_defl_with_na_map [domain_category_map]:
  "deflation v \<Longrightarrow> separated_sum_defl (with_na_map\<cdot>v)"
  by (domain_category_map_rule map_def: with_na_map_def iso_rews: with_na.iso_rews)

instance with_na :: ("{domain, bounded_complete}") bounded_complete
  by (domain_category_instance map_ID: with_na_map_ID)

instance with_na :: ("domain") separated_sum
  by (domain_category_instance map_ID: with_na_map_ID)

lemma distributive_defl_with_na_map [domain_category_map]:
  "distributive_defl (v :: 'a::{domain, bounded_complete} \<rightarrow> 'a) \<Longrightarrow>
    distributive_defl (with_na_map\<cdot>v)"
  by (domain_category_map_rule map_def: with_na_map_def iso_rews: with_na.iso_rews)

instance with_na :: ("{domain, distributive_cpo}") distributive_cpo
  by (domain_category_instance map_ID: with_na_map_ID)

lemma locally_finitely_detailed_defl_with_na_map [domain_category_map]:
  "locally_finitely_detailed_defl v \<Longrightarrow> locally_finitely_detailed_defl (with_na_map\<cdot>v)"
  by (domain_category_map_rule map_def: with_na_map_def iso_rews: with_na.iso_rews)

instance with_na :: ("{domain, locally_finitely_detailed}") locally_finitely_detailed
  by (domain_category_instance map_ID: with_na_map_ID)

subsection \<open>Data\<close>

text \<open>A datum is \<open>NA\<close>, \<open>Val\<cdot>Null\<close>, or a known value.\<close>

type_synonym 'v datum = "'v with_null with_na"

section \<open>Coercions between the levels\<close>

text \<open>Binding through \<open>NA\<close>: \<open>NA\<close> propagates, a value is passed on.  A join through a
  relation that may be inapplicable is a bind.\<close>

fixrec na_bind :: "('a::domain \<rightarrow> 'b::domain with_na) \<rightarrow> 'a with_na \<rightarrow> 'b with_na" where
  "na_bind\<cdot>f\<cdot>NA = NA"
| "na_bind\<cdot>f\<cdot>(Val\<cdot>x) = f\<cdot>x"

lemma na_bind_strict [simp]: "na_bind\<cdot>f\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

text \<open>Measures: \<open>NA\<close> becomes \<open>\<bottom>\<close> (no entry).\<close>

fixrec from_na :: "'a::domain with_na \<rightarrow> 'a" where
  "from_na\<cdot>NA = \<bottom>"
| "from_na\<cdot>(Val\<cdot>x) = x"

lemma from_na_strict [simp]: "from_na\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

text \<open>Measures embed back strictly: @{text na_emb} and @{const from_na} form an
  embedding-projection pair.  Their composition @{text squash} is the projection that forgets
  \<open>NA\<close> (and the not-null root, which data never takes).\<close>

definition na_emb :: "'a::domain \<rightarrow> 'a with_na" where
  "na_emb = strictify\<cdot>Val"

lemma na_emb_strict [simp]: "na_emb\<cdot>\<bottom> = \<bottom>"
  by (simp add: na_emb_def)

lemma na_emb_defined [simp]: "x \<noteq> \<bottom> \<Longrightarrow> na_emb\<cdot>x = Val\<cdot>x"
  by (simp add: na_emb_def strictify_conv_if)

lemma ep_pair_na: "ep_pair na_emb from_na"
proof
  fix x :: 'a show "from_na\<cdot>(na_emb\<cdot>x) = x" by (cases "x = \<bottom>") simp_all
next
  fix y :: "'a with_na" show "na_emb\<cdot>(from_na\<cdot>y) \<sqsubseteq> y"
    by (cases y) (simp_all add: na_emb_def strictify_conv_if)
qed

lemma from_na_na_emb [simp]: "from_na\<cdot>(na_emb\<cdot>x) = x"
  by (rule ep_pair.e_inverse[OF ep_pair_na])

definition squash :: "'a::domain with_na \<rightarrow> 'a with_na" where
  "squash = na_emb oo from_na"

lemma squash_simps [simp]: "squash\<cdot>\<bottom> = \<bottom>" "squash\<cdot>NA = \<bottom>" "squash\<cdot>(Val\<cdot>x) = na_emb\<cdot>x"
  by (simp_all add: squash_def)

lemma squash_na_emb [simp]: "squash\<cdot>(na_emb\<cdot>x) = na_emb\<cdot>x"
  unfolding squash_def by (simp add: ep_pair.e_inverse[OF ep_pair_na])

lemma deflation_squash: "deflation squash"
  unfolding squash_def by (rule ep_pair.deflation_e_p[OF ep_pair_na])

lemma from_na_squash [simp]: "from_na\<cdot>(squash\<cdot>x) = from_na\<cdot>x"
  unfolding squash_def by (simp add: ep_pair.e_inverse[OF ep_pair_na])

text \<open>Keys: nulls become \<open>NA\<close>.\<close>

fixrec null_na :: "'v::domain with_null \<rightarrow> 'v with_na" where
  "null_na\<cdot>Null = NA"
| "v \<noteq> \<bottom> \<Longrightarrow> null_na\<cdot>(Known\<cdot>v) = Val\<cdot>v"

lemma null_na_strict [simp]: "null_na\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

definition to_key :: "'v::domain datum \<rightarrow> 'v with_na" where
  "to_key = na_bind\<cdot>null_na"

text \<open>Measures project to plain values, \<open>Null\<close> becoming \<open>\<bottom>\<close>.  @{const Known} is strict,
  so it is the embedding itself.\<close>

fixrec from_null :: "'v::domain with_null \<rightarrow> 'v" where
  "from_null\<cdot>Null = \<bottom>"
| "v \<noteq> \<bottom> \<Longrightarrow> from_null\<cdot>(Known\<cdot>v) = v"

lemma from_null_strict [simp]: "from_null\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

lemma ep_pair_null: "ep_pair (Known :: 'v::domain \<rightarrow> 'v with_null) from_null"
proof
  fix x :: 'v show "from_null\<cdot>(Known\<cdot>x) = x" by (cases "x = \<bottom>") simp_all
next
  fix y :: "'v with_null" show "Known\<cdot>(from_null\<cdot>y) \<sqsubseteq> y" by (cases y) simp_all
qed

lemma from_null_Known [simp]: "from_null\<cdot>(Known\<cdot>x) = x"
  by (rule ep_pair.e_inverse[OF ep_pair_null])

text \<open>The plain value of a datum: every missing value becomes \<open>\<bottom>\<close>.\<close>

definition plain :: "'v::domain datum \<rightarrow> 'v" where
  "plain = from_null oo from_na"

lemma plain_simps [simp]:
  "plain\<cdot>\<bottom> = \<bottom>" "plain\<cdot>NA = \<bottom>" "plain\<cdot>(Val\<cdot>x) = from_null\<cdot>x"
  by (simp_all add: plain_def)

lemma plain_na_emb [simp]: "plain\<cdot>(na_emb\<cdot>x) = from_null\<cdot>x"
  by (simp add: plain_def)

section \<open>Record-level operators\<close>

text \<open>Operators are lifted layer by layer, each layer's missing value infectious.  The outer
  layer is checked first, so \<open>NA\<close> wins over \<open>Null\<close>; NA-blindness forces that choice.\<close>

fixrec na_lift2 :: "('a::domain \<rightarrow> 'b::domain \<rightarrow> 'c::domain) \<rightarrow> 'a with_na \<rightarrow> 'b with_na \<rightarrow> 'c with_na"
  where
  "na_lift2\<cdot>f\<cdot>NA\<cdot>NA = NA"
| "na_lift2\<cdot>f\<cdot>NA\<cdot>(Val\<cdot>y) = NA"
| "na_lift2\<cdot>f\<cdot>(Val\<cdot>x)\<cdot>NA = NA"
| "na_lift2\<cdot>f\<cdot>(Val\<cdot>x)\<cdot>(Val\<cdot>y) = na_emb\<cdot>(f\<cdot>x\<cdot>y)"

fixrec null_lift2 ::
  "('a::domain \<rightarrow> 'b::domain \<rightarrow> 'c::domain) \<rightarrow> 'a with_null \<rightarrow> 'b with_null \<rightarrow> 'c with_null"
  where
  "null_lift2\<cdot>f\<cdot>Null\<cdot>Null = Null"
| "y \<noteq> \<bottom> \<Longrightarrow> null_lift2\<cdot>f\<cdot>Null\<cdot>(Known\<cdot>y) = Null"
| "x \<noteq> \<bottom> \<Longrightarrow> null_lift2\<cdot>f\<cdot>(Known\<cdot>x)\<cdot>Null = Null"
| "x \<noteq> \<bottom> \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> null_lift2\<cdot>f\<cdot>(Known\<cdot>x)\<cdot>(Known\<cdot>y) = Known\<cdot>(f\<cdot>x\<cdot>y)"

fixrec na_lift1 :: "('a::domain \<rightarrow> 'b::domain) \<rightarrow> 'a with_na \<rightarrow> 'b with_na" where
  "na_lift1\<cdot>f\<cdot>NA = NA"
| "na_lift1\<cdot>f\<cdot>(Val\<cdot>x) = na_emb\<cdot>(f\<cdot>x)"

fixrec null_lift1 :: "('a::domain \<rightarrow> 'b::domain) \<rightarrow> 'a with_null \<rightarrow> 'b with_null" where
  "null_lift1\<cdot>f\<cdot>Null = Null"
| "x \<noteq> \<bottom> \<Longrightarrow> null_lift1\<cdot>f\<cdot>(Known\<cdot>x) = Known\<cdot>(f\<cdot>x)"

abbreviation dlift1 :: "('a::domain \<rightarrow> 'b::domain) \<rightarrow> 'a datum \<rightarrow> 'b datum" where
  "dlift1 \<equiv> na_lift1 oo null_lift1"

lemma na_lift1_strict [simp]: "na_lift1\<cdot>f\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

lemma null_lift1_strict [simp]: "null_lift1\<cdot>f\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

abbreviation dlift2 :: "('a::domain \<rightarrow> 'b::domain \<rightarrow> 'c::domain) \<rightarrow> 'a datum \<rightarrow> 'b datum \<rightarrow> 'c datum" where
  "dlift2 \<equiv> na_lift2 oo null_lift2"

lemma na_lift2_strict [simp]: "na_lift2\<cdot>f\<cdot>\<bottom>\<cdot>y = \<bottom>" "na_lift2\<cdot>f\<cdot>x\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp (cases x; fixrec_simp)

lemma null_lift2_strict [simp]: "null_lift2\<cdot>f\<cdot>\<bottom>\<cdot>y = \<bottom>" "null_lift2\<cdot>f\<cdot>x\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp (cases x; fixrec_simp)

text \<open>A record-level function is NA-blind when swapping \<open>NA\<close> for \<open>\<bottom>\<close> in its inputs does
  the same to its output.\<close>

definition na_blind1 :: "('a::domain with_na \<rightarrow> 'b::domain with_na) \<Rightarrow> bool" where
  "na_blind1 g \<longleftrightarrow> (\<forall>x. g\<cdot>(squash\<cdot>x) = squash\<cdot>(g\<cdot>x))"

definition na_blind2 ::
  "('a::domain with_na \<rightarrow> 'b::domain with_na \<rightarrow> 'c::domain with_na) \<Rightarrow> bool" where
  "na_blind2 g \<longleftrightarrow> (\<forall>x y. g\<cdot>(squash\<cdot>x)\<cdot>(squash\<cdot>y) = squash\<cdot>(g\<cdot>x\<cdot>y))"

lemma na_blind2_na_lift2:
  assumes l: "\<And>y. f\<cdot>\<bottom>\<cdot>y = \<bottom>" and r: "\<And>x. f\<cdot>x\<cdot>\<bottom> = \<bottom>"
  shows "na_blind2 (na_lift2\<cdot>f)"
  unfolding na_blind2_def
proof (intro allI)
  fix x y show "na_lift2\<cdot>f\<cdot>(squash\<cdot>x)\<cdot>(squash\<cdot>y) = squash\<cdot>(na_lift2\<cdot>f\<cdot>x\<cdot>y)"
    by (cases x; cases y) (auto simp: l r strictify_conv_if na_emb_def)
qed

text \<open>The inner layer is strict, so every lifted record-level operator is NA-blind.\<close>

lemma na_blind2_dlift2: "na_blind2 (dlift2\<cdot>f)"
  by (simp add: na_blind2_na_lift2)

text \<open>On plain values, a lifted strict operator is the operator itself.\<close>

lemma plain_dlift1:
  assumes "f\<cdot>\<bottom> = \<bottom>" shows "plain\<cdot>(na_lift1\<cdot>(null_lift1\<cdot>f)\<cdot>x) = f\<cdot>(plain\<cdot>x)"
proof (cases x)
  case (Val a) then show ?thesis using assms by (cases a) simp_all
qed (simp_all add: assms)

lemma plain_dlift2:
  assumes "\<And>y. f\<cdot>\<bottom>\<cdot>y = \<bottom>" "\<And>x. f\<cdot>x\<cdot>\<bottom> = \<bottom>"
  shows "plain\<cdot>(na_lift2\<cdot>(null_lift2\<cdot>f)\<cdot>x\<cdot>y) = f\<cdot>(plain\<cdot>x)\<cdot>(plain\<cdot>y)"
proof (cases x)
  case x: (Val a) show ?thesis
  proof (cases y)
    case y: (Val b) show ?thesis unfolding x y using assms by (cases a; cases b) simp_all
  qed (simp_all add: x assms)
qed (cases y; simp add: assms)+

subsection \<open>Equality\<close>

text \<open>Equality of flat values, strict in both arguments.  @{typ tr} is @{typ "bool lift"}, so
  this covers both fields of @{text scalar}.\<close>

definition lift_eq :: "'a lift \<rightarrow> 'a lift \<rightarrow> tr" where
  "lift_eq = (FLIFT a. FLIFT b. Def (a = b))"

lemma lift_eq_Def [simp]: "lift_eq\<cdot>(Def a)\<cdot>(Def b) = Def (a = b)"
  by (simp add: lift_eq_def)

lemma lift_eq_strict [simp]: "lift_eq\<cdot>\<bottom>\<cdot>y = \<bottom>" "lift_eq\<cdot>x\<cdot>\<bottom> = \<bottom>"
  by (simp_all add: lift_eq_def) (cases x; simp)

lemma lift_eq_defined: "x \<noteq> \<bottom> \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> lift_eq\<cdot>x\<cdot>y = Def (x = y)"
  by (cases x; cases y) simp_all

text \<open>Scalars of different types are unequal; under static typing that case does not arise.\<close>

fixrec scalar_eq :: "scalar \<rightarrow> scalar \<rightarrow> tr" where
  "a \<noteq> \<bottom> \<Longrightarrow> b \<noteq> \<bottom> \<Longrightarrow> scalar_eq\<cdot>(SBool\<cdot>a)\<cdot>(SBool\<cdot>b) = lift_eq\<cdot>a\<cdot>b"
| "m \<noteq> \<bottom> \<Longrightarrow> n \<noteq> \<bottom> \<Longrightarrow> scalar_eq\<cdot>(SInt\<cdot>m)\<cdot>(SInt\<cdot>n) = lift_eq\<cdot>m\<cdot>n"
| "a \<noteq> \<bottom> \<Longrightarrow> n \<noteq> \<bottom> \<Longrightarrow> scalar_eq\<cdot>(SBool\<cdot>a)\<cdot>(SInt\<cdot>n) = FF"
| "m \<noteq> \<bottom> \<Longrightarrow> b \<noteq> \<bottom> \<Longrightarrow> scalar_eq\<cdot>(SInt\<cdot>m)\<cdot>(SBool\<cdot>b) = FF"

lemma scalar_eq_strict [simp]: "scalar_eq\<cdot>\<bottom>\<cdot>y = \<bottom>" "scalar_eq\<cdot>x\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp (cases x; fixrec_simp)

lemma scalar_eq_defined: "x \<noteq> \<bottom> \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> scalar_eq\<cdot>x\<cdot>y = Def (x = y)"
  by (cases x; cases y) (simp_all add: lift_eq_defined FF_def)

text \<open>Record-level equality is the lifted scalar equality, hence NA-blind.\<close>

abbreviation datum_eq :: "scalar datum \<rightarrow> scalar datum \<rightarrow> tr datum" where
  "datum_eq \<equiv> dlift2\<cdot>scalar_eq"

subsection \<open>Truth\<close>

text \<open>The connectives are strict, so lifted to data they make \<open>NA\<close> and \<open>Null\<close>
  infectious (\<open>NOT NA = NA\<close>).  @{text truth_d} projects a datum to @{typ tr}, sending every
  missing value and every non-boolean to \<open>\<bottom>\<close>; it is a homomorphism for the connectives.  A
  slicer condition holds where @{text truth_d} is @{term TT}.\<close>

definition tr_and :: "tr \<rightarrow> tr \<rightarrow> tr" where
  "tr_and = (FLIFT a. FLIFT b. Def (a \<and> b))"

definition tr_or :: "tr \<rightarrow> tr \<rightarrow> tr" where
  "tr_or = (FLIFT a. FLIFT b. Def (a \<or> b))"

lemma tr_and_simps [simp]:
  "tr_and\<cdot>\<bottom>\<cdot>y = \<bottom>" "tr_and\<cdot>x\<cdot>\<bottom> = \<bottom>" "tr_and\<cdot>(Def a)\<cdot>(Def b) = Def (a \<and> b)"
  by (simp_all add: tr_and_def) (cases x rule: lift.exhaust; simp)

lemma tr_or_simps [simp]:
  "tr_or\<cdot>\<bottom>\<cdot>y = \<bottom>" "tr_or\<cdot>x\<cdot>\<bottom> = \<bottom>" "tr_or\<cdot>(Def a)\<cdot>(Def b) = Def (a \<or> b)"
  by (simp_all add: tr_or_def) (cases x rule: lift.exhaust; simp)

fixrec sbool :: "scalar \<rightarrow> tr" where
  "b \<noteq> \<bottom> \<Longrightarrow> sbool\<cdot>(SBool\<cdot>b) = b"

lemma sbool_strict [simp]: "sbool\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

fixrec snot :: "scalar \<rightarrow> scalar" where
  "a \<noteq> \<bottom> \<Longrightarrow> snot\<cdot>(SBool\<cdot>a) = SBool\<cdot>(neg\<cdot>a)"

fixrec sand :: "scalar \<rightarrow> scalar \<rightarrow> scalar" where
  "a \<noteq> \<bottom> \<Longrightarrow> b \<noteq> \<bottom> \<Longrightarrow> sand\<cdot>(SBool\<cdot>a)\<cdot>(SBool\<cdot>b) = SBool\<cdot>(tr_and\<cdot>a\<cdot>b)"

fixrec sor :: "scalar \<rightarrow> scalar \<rightarrow> scalar" where
  "a \<noteq> \<bottom> \<Longrightarrow> b \<noteq> \<bottom> \<Longrightarrow> sor\<cdot>(SBool\<cdot>a)\<cdot>(SBool\<cdot>b) = SBool\<cdot>(tr_or\<cdot>a\<cdot>b)"

text \<open>Unconditional constructor equations; ill-typed applications give \<open>\<bottom>\<close>.\<close>

lemma sbool_simps [simp]: "sbool\<cdot>(SBool\<cdot>b) = b" "sbool\<cdot>(SInt\<cdot>n) = \<bottom>"
  by (cases "b = \<bottom>"; simp) (cases "n = \<bottom>"; fixrec_simp)

lemma snot_simps [simp]: "snot\<cdot>(SBool\<cdot>a) = SBool\<cdot>(neg\<cdot>a)" "snot\<cdot>(SInt\<cdot>n) = \<bottom>"
  by (cases "a = \<bottom>"; simp; fixrec_simp) (cases "n = \<bottom>"; fixrec_simp)

lemma sand_simps [simp]:
  "sand\<cdot>(SBool\<cdot>a)\<cdot>(SBool\<cdot>b) = SBool\<cdot>(tr_and\<cdot>a\<cdot>b)"
  "sand\<cdot>(SInt\<cdot>m)\<cdot>y = \<bottom>" "sand\<cdot>x\<cdot>(SInt\<cdot>n) = \<bottom>"
    apply (cases "a = \<bottom>"; cases "b = \<bottom>"; simp; fixrec_simp)
   apply (cases "m = \<bottom>"; fixrec_simp)
  apply (cases x; cases "n = \<bottom>"; fixrec_simp)
  done

lemma sor_simps [simp]:
  "sor\<cdot>(SBool\<cdot>a)\<cdot>(SBool\<cdot>b) = SBool\<cdot>(tr_or\<cdot>a\<cdot>b)"
  "sor\<cdot>(SInt\<cdot>m)\<cdot>y = \<bottom>" "sor\<cdot>x\<cdot>(SInt\<cdot>n) = \<bottom>"
    apply (cases "a = \<bottom>"; cases "b = \<bottom>"; simp; fixrec_simp)
   apply (cases "m = \<bottom>"; fixrec_simp)
  apply (cases x; cases "n = \<bottom>"; fixrec_simp)
  done

definition truth :: "scalar with_na \<rightarrow> tr" where
  "truth = sbool oo from_na"

definition truth_d :: "scalar datum \<rightarrow> tr" where
  "truth_d = sbool oo plain"

lemma scalar_connectives_strict [simp]:
  "snot\<cdot>\<bottom> = \<bottom>" "sand\<cdot>\<bottom>\<cdot>y = \<bottom>" "sand\<cdot>x\<cdot>\<bottom> = \<bottom>" "sor\<cdot>\<bottom>\<cdot>y = \<bottom>" "sor\<cdot>x\<cdot>\<bottom> = \<bottom>"
      apply fixrec_simp
     apply fixrec_simp
    apply (cases x; fixrec_simp)
   apply fixrec_simp
  apply (cases x; fixrec_simp)
  done

lemma sbool_connectives:
  "sbool\<cdot>(snot\<cdot>s) = neg\<cdot>(sbool\<cdot>s)"
  "sbool\<cdot>(sand\<cdot>s\<cdot>t) = tr_and\<cdot>(sbool\<cdot>s)\<cdot>(sbool\<cdot>t)"
  "sbool\<cdot>(sor\<cdot>s\<cdot>t) = tr_or\<cdot>(sbool\<cdot>s)\<cdot>(sbool\<cdot>t)"
  by (cases s; simp; cases t; simp)+

lemma truth_d_not: "truth_d\<cdot>(dlift1\<cdot>snot\<cdot>x) = neg\<cdot>(truth_d\<cdot>x)"
  by (simp add: truth_d_def plain_dlift1 sbool_connectives)

lemma truth_d_and: "truth_d\<cdot>(dlift2\<cdot>sand\<cdot>x\<cdot>y) = tr_and\<cdot>(truth_d\<cdot>x)\<cdot>(truth_d\<cdot>y)"
  by (simp add: truth_d_def plain_dlift2 sbool_connectives)

lemma truth_d_or: "truth_d\<cdot>(dlift2\<cdot>sor\<cdot>x\<cdot>y) = tr_or\<cdot>(truth_d\<cdot>x)\<cdot>(truth_d\<cdot>y)"
  by (simp add: truth_d_def plain_dlift2 sbool_connectives)

section \<open>The not-null level of keys\<close>

text \<open>The atoms of @{typ "'a with_na"} are \<open>NA\<close> and \<open>Val\<cdot>\<bottom>\<close>, so its discriminator is the
  projection @{text not_null}, which observes only whether a key is \<open>NA\<close>.  It is a finitary
  semi-factor, i.e.\ a level of detail, and @{text is_na} factors through it.\<close>

fixrec is_na :: "'a::domain with_na \<rightarrow> tr" where
  "is_na\<cdot>NA = TT"
| "is_na\<cdot>(Val\<cdot>x) = FF"

lemma is_na_strict [simp]: "is_na\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

fixrec not_null :: "'a::domain with_na \<rightarrow> 'a with_na" where
  "not_null\<cdot>NA = NA"
| "not_null\<cdot>(Val\<cdot>x) = Val\<cdot>\<bottom>"

lemma not_null_strict [simp]: "not_null\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

lemma atom_NA: "atom NA"
  by (rule atomI) (simp, case_tac z, simp_all)

lemma atom_Val_bottom: "atom (Val\<cdot>\<bottom>)"
  by (rule atomI) (simp, case_tac z, simp_all)

lemma discriminator_with_na:
  "discriminator\<cdot>x = not_null\<cdot>(x :: 'a::{domain, bounded_complete} with_na)"
proof (cases x)
  case bottom then show ?thesis by simp
next
  case NA then show ?thesis by (simp add: discriminator_eq[OF atom_NA below_refl])
next
  case (Val v)
  have "Val\<cdot>\<bottom> \<sqsubseteq> x" unfolding Val by (rule monofun_cfun_arg) simp
  then show ?thesis unfolding Val by (simp add: discriminator_eq[OF atom_Val_bottom])
qed

lemma not_null_level:
  "semi_factor_defl (not_null :: 'a::{domain, distributive_cpo} with_na \<rightarrow> 'a with_na)"
  "finitary (not_null :: 'a::{domain, distributive_cpo} with_na \<rightarrow> 'a with_na)"
  using discriminator_semi_factor discriminator_finitary
  by (simp_all add: cfun_eqI[OF discriminator_with_na, symmetric])

lemma is_na_not_null: "is_na\<cdot>(not_null\<cdot>x) = is_na\<cdot>x"
  by (cases x) simp_all

end
