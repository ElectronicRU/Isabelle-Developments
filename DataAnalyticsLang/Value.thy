theory Value
  imports LOD "HOLCF-extra.Domain_Order_Derive" "HOLCF-extra.Kleene_Logic"
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

text \<open>Negation is strict, lifted layer by layer, so \<open>NOT NA = NA\<close>.  Conjunction and disjunction
  are Kleene's parallel connectives: a false conjunct makes a conjunction false whatever the others
  are, missing or undefined, and dually a true disjunct a disjunction true.  Otherwise an undefined
  argument makes them undefined, \<open>NA\<close> dominates \<open>Null\<close> as for every lifted operator, and else
  they are the connectives on truth values.  @{text truth_d} projects a datum to @{typ tr}, sending
  every missing value and every non-boolean to \<open>\<bottom>\<close>; it is a homomorphism onto the parallel
  connectives on @{typ tr}.  A slicer condition holds where @{text truth_d} is @{term TT}.\<close>

fixrec sbool :: "scalar \<rightarrow> tr" where
  "b \<noteq> \<bottom> \<Longrightarrow> sbool\<cdot>(SBool\<cdot>b) = b"

lemma sbool_strict [simp]: "sbool\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

fixrec snot :: "scalar \<rightarrow> scalar" where
  "a \<noteq> \<bottom> \<Longrightarrow> snot\<cdot>(SBool\<cdot>a) = SBool\<cdot>(neg\<cdot>a)"

text \<open>Unconditional constructor equations; ill-typed applications give \<open>\<bottom>\<close>.\<close>

lemma sbool_simps [simp]: "sbool\<cdot>(SBool\<cdot>b) = b" "sbool\<cdot>(SInt\<cdot>n) = \<bottom>"
  by (cases "b = \<bottom>"; simp) (cases "n = \<bottom>"; fixrec_simp)

lemma snot_simps [simp]: "snot\<cdot>(SBool\<cdot>a) = SBool\<cdot>(neg\<cdot>a)" "snot\<cdot>(SInt\<cdot>n) = \<bottom>"
  by (cases "a = \<bottom>"; simp; fixrec_simp) (cases "n = \<bottom>"; fixrec_simp)

lemma snot_strict [simp]: "snot\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

definition truth :: "scalar with_na \<rightarrow> tr" where
  "truth = sbool oo from_na"

definition truth_d :: "scalar datum \<rightarrow> tr" where
  "truth_d = sbool oo plain"

lemma sbool_snot: "sbool\<cdot>(snot\<cdot>s) = neg\<cdot>(sbool\<cdot>s)"
  by (cases s; simp)

lemma truth_d_not: "truth_d\<cdot>(dlift1\<cdot>snot\<cdot>x) = neg\<cdot>(truth_d\<cdot>x)"
  by (simp add: truth_d_def plain_dlift1 sbool_snot)

definition d_bool :: "tr \<rightarrow> scalar datum" where
  "d_bool = na_emb oo Known oo SBool"

lemma truth_d_bool [simp]: "truth_d\<cdot>(d_bool\<cdot>t) = t"
  by (cases t rule: trE) (simp_all add: d_bool_def truth_d_def)

text \<open>The parallel connectives see a datum only through its kind: a truth value, \<open>NA\<close>, or
  \<open>Null\<close>; the not-null root and the non-booleans have none.\<close>

datatype truth_kind = KTrue | KFalse | KNA | KNull

lemma kind_cases [case_names bottom KTrue KFalse KNA KNull]:
  obtains "x = \<bottom>" | "x = Def KTrue" | "x = Def KFalse" | "x = Def KNA" | "x = Def KNull"
  by (cases x rule: lift.exhaust) (auto, metis truth_kind.exhaust)

definition kind_scalar :: "scalar \<rightarrow> truth_kind lift" where
  "kind_scalar = (\<Lambda> s. (FLIFT b. Def (if b then KTrue else KFalse))\<cdot>(sbool\<cdot>s))"

lemma kind_scalar_simps [simp]:
  "kind_scalar\<cdot>\<bottom> = \<bottom>" "kind_scalar\<cdot>(SBool\<cdot>TT) = Def KTrue" "kind_scalar\<cdot>(SBool\<cdot>FF) = Def KFalse"
  "kind_scalar\<cdot>(SInt\<cdot>n) = \<bottom>"
  by (simp_all add: kind_scalar_def TT_def FF_def)

fixrec kind_null :: "scalar with_null \<rightarrow> truth_kind lift" where
  "kind_null\<cdot>Null = Def KNull"
| "s \<noteq> \<bottom> \<Longrightarrow> kind_null\<cdot>(Known\<cdot>s) = kind_scalar\<cdot>s"

lemma kind_null_strict [simp]: "kind_null\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

lemma kind_null_Known [simp]: "kind_null\<cdot>(Known\<cdot>s) = kind_scalar\<cdot>s"
  by (cases "s = \<bottom>") simp_all

fixrec kind :: "scalar datum \<rightarrow> truth_kind lift" where
  "kind\<cdot>NA = Def KNA"
| "kind\<cdot>(Val\<cdot>x) = kind_null\<cdot>x"

lemma kind_strict [simp]: "kind\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

definition from_kind :: "truth_kind lift \<rightarrow> scalar datum" where
  "from_kind = (FLIFT k. case k of KTrue \<Rightarrow> d_bool\<cdot>TT | KFalse \<Rightarrow> d_bool\<cdot>FF | KNA \<Rightarrow> NA | KNull \<Rightarrow> Val\<cdot>Null)"

lemma from_kind_simps [simp]:
  "from_kind\<cdot>\<bottom> = \<bottom>" "from_kind\<cdot>(Def KTrue) = d_bool\<cdot>TT" "from_kind\<cdot>(Def KFalse) = d_bool\<cdot>FF"
  "from_kind\<cdot>(Def KNA) = NA" "from_kind\<cdot>(Def KNull) = Val\<cdot>Null"
  by (simp_all add: from_kind_def)

lemma kind_from_kind [simp]: "kind\<cdot>(from_kind\<cdot>k) = k"
  by (cases k rule: kind_cases) (simp_all add: d_bool_def)

definition ktruth :: "truth_kind lift \<rightarrow> tr" where
  "ktruth = (FLIFT k. case k of KTrue \<Rightarrow> TT | KFalse \<Rightarrow> FF | KNA \<Rightarrow> \<bottom> | KNull \<Rightarrow> \<bottom>)"

lemma ktruth_simps [simp]:
  "ktruth\<cdot>\<bottom> = \<bottom>" "ktruth\<cdot>(Def KTrue) = TT" "ktruth\<cdot>(Def KFalse) = FF"
  "ktruth\<cdot>(Def KNA) = \<bottom>" "ktruth\<cdot>(Def KNull) = \<bottom>"
  by (simp_all add: ktruth_def)

lemma ktruth_kind_scalar: "ktruth\<cdot>(kind_scalar\<cdot>s) = sbool\<cdot>s"
proof (cases s)
  case (SBool b) then show ?thesis by (cases b rule: trE) simp_all
qed simp_all

lemma kind_null_not_KNA: "kind_null\<cdot>y \<noteq> Def KNA"
proof (cases y)
  case (Known s) then show ?thesis
  proof (cases s)
    case (SBool b) then show ?thesis using Known by (cases b rule: trE) simp_all
  qed (simp_all add: Known)
qed simp_all

lemma truth_d_kind: "truth_d\<cdot>x = ktruth\<cdot>(kind\<cdot>x)"
proof (cases x)
  case (Val y) then show ?thesis
    by (cases y) (simp_all add: truth_d_def ktruth_kind_scalar)
qed (simp_all add: truth_d_def)

definition kand :: "truth_kind lift \<rightarrow> truth_kind lift \<rightarrow> truth_kind lift" where
  "kand = (\<Lambda> x y. if x = Def KFalse \<or> y = Def KFalse then Def KFalse else if x = \<bottom> \<or> y = \<bottom> then \<bottom>
     else if x = Def KNA \<or> y = Def KNA then Def KNA else if x = Def KNull \<or> y = Def KNull then Def KNull
     else Def KTrue)"

definition kor :: "truth_kind lift \<rightarrow> truth_kind lift \<rightarrow> truth_kind lift" where
  "kor = (\<Lambda> x y. if x = Def KTrue \<or> y = Def KTrue then Def KTrue else if x = \<bottom> \<or> y = \<bottom> then \<bottom>
     else if x = Def KNA \<or> y = Def KNA then Def KNA else if x = Def KNull \<or> y = Def KNull then Def KNull
     else Def KFalse)"

lemma kand_apply: "kand\<cdot>x\<cdot>y = (if x = Def KFalse \<or> y = Def KFalse then Def KFalse else if x = \<bottom> \<or> y = \<bottom> then \<bottom>
     else if x = Def KNA \<or> y = Def KNA then Def KNA else if x = Def KNull \<or> y = Def KNull then Def KNull
     else Def KTrue)"
  unfolding kand_def by (rule beta_chfin2; rule monofunI; auto simp: flat_below_iff)

lemma kor_apply: "kor\<cdot>x\<cdot>y = (if x = Def KTrue \<or> y = Def KTrue then Def KTrue else if x = \<bottom> \<or> y = \<bottom> then \<bottom>
     else if x = Def KNA \<or> y = Def KNA then Def KNA else if x = Def KNull \<or> y = Def KNull then Def KNull
     else Def KFalse)"
  unfolding kor_def by (rule beta_chfin2; rule monofunI; auto simp: flat_below_iff)

lemma ktruth_kand: "ktruth\<cdot>(kand\<cdot>a\<cdot>b) = pand\<cdot>(ktruth\<cdot>a)\<cdot>(ktruth\<cdot>b)"
  and ktruth_kor: "ktruth\<cdot>(kor\<cdot>a\<cdot>b) = por\<cdot>(ktruth\<cdot>a)\<cdot>(ktruth\<cdot>b)"
  by (cases a rule: kind_cases; cases b rule: kind_cases; simp add: kand_apply kor_apply)+

definition d_and :: "scalar datum \<rightarrow> scalar datum \<rightarrow> scalar datum" where
  "d_and = (\<Lambda> x y. from_kind\<cdot>(kand\<cdot>(kind\<cdot>x)\<cdot>(kind\<cdot>y)))"

definition d_or :: "scalar datum \<rightarrow> scalar datum \<rightarrow> scalar datum" where
  "d_or = (\<Lambda> x y. from_kind\<cdot>(kor\<cdot>(kind\<cdot>x)\<cdot>(kind\<cdot>y)))"

lemma d_and_apply: "d_and\<cdot>x\<cdot>y = from_kind\<cdot>(kand\<cdot>(kind\<cdot>x)\<cdot>(kind\<cdot>y))"
  and d_or_apply: "d_or\<cdot>x\<cdot>y = from_kind\<cdot>(kor\<cdot>(kind\<cdot>x)\<cdot>(kind\<cdot>y))"
  by (simp_all add: d_and_def d_or_def)

lemma truth_d_and: "truth_d\<cdot>(d_and\<cdot>x\<cdot>y) = pand\<cdot>(truth_d\<cdot>x)\<cdot>(truth_d\<cdot>y)"
  and truth_d_or: "truth_d\<cdot>(d_or\<cdot>x\<cdot>y) = por\<cdot>(truth_d\<cdot>x)\<cdot>(truth_d\<cdot>y)"
  by (simp_all add: d_and_apply d_or_apply truth_d_kind ktruth_kand ktruth_kor)

text \<open>Forgetting \<open>NA\<close> forgets the kind \<open>NA\<close>, so the parallel connectives are NA-blind.\<close>

definition ksquash :: "truth_kind lift \<rightarrow> truth_kind lift" where
  "ksquash = (FLIFT k. if k = KNA then \<bottom> else Def k)"

lemma ksquash_simps [simp]: "ksquash\<cdot>\<bottom> = \<bottom>" "ksquash\<cdot>(Def k) = (if k = KNA then \<bottom> else Def k)"
  by (simp_all add: ksquash_def)

lemma ksquash_id: "k \<noteq> Def KNA \<Longrightarrow> ksquash\<cdot>k = k"
  by (cases k rule: kind_cases) simp_all

lemma kind_squash: "kind\<cdot>(squash\<cdot>x) = ksquash\<cdot>(kind\<cdot>x)"
proof (cases x)
  case (Val y) then show ?thesis using ksquash_id[OF kind_null_not_KNA[of y]] by (cases "y = \<bottom>") simp_all
qed simp_all

lemma squash_from_kind: "squash\<cdot>(from_kind\<cdot>k) = from_kind\<cdot>(ksquash\<cdot>k)"
  by (cases k rule: kind_cases) (simp_all add: d_bool_def)

lemma kand_ksquash: "kand\<cdot>(ksquash\<cdot>a)\<cdot>(ksquash\<cdot>b) = ksquash\<cdot>(kand\<cdot>a\<cdot>b)"
  and kor_ksquash: "kor\<cdot>(ksquash\<cdot>a)\<cdot>(ksquash\<cdot>b) = ksquash\<cdot>(kor\<cdot>a\<cdot>b)"
  by (cases a rule: kind_cases; cases b rule: kind_cases; simp add: kand_apply kor_apply)+

lemma na_blind2_d_and: "na_blind2 d_and" and na_blind2_d_or: "na_blind2 d_or"
  unfolding na_blind2_def d_and_apply d_or_apply kind_squash squash_from_kind kand_ksquash kor_ksquash
  by simp_all

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
