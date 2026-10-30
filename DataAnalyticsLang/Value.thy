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
  short row.  Keys (dimensions) and data (records and record-level expressions) share one type,
  @{text "'v with_null"}: \<open>Null\<close> (present, but unknown or empty), the lazy root \<open>Known\<cdot>\<bottom>\<close>
  (not null, the value to be filled later), or a known value.  \<open>Null\<close> is a key value like any
  other, so it can be pinned.  The absence of a value at a key is not a value: it lives in the
  results, as @{text Absent}.\<close>

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

subsection \<open>Values with nulls\<close>

text \<open>The lazy root \<open>Known\<cdot>\<bottom>\<close> gives the not-null level of detail.\<close>

domain ('a::"domain") with_null = Null | Known (lazy 'a)

lemma bounded_complete_defl_with_null_map [domain_category_map]:
  "bounded_complete_defl v \<Longrightarrow> bounded_complete_defl (with_null_map\<cdot>v)"
  by (domain_category_map_rule map_def: with_null_map_def iso_rews: with_null.iso_rews)

lemma filter_sum_defl_with_null_map [domain_category_map]:
  "filter_sum_defl v \<Longrightarrow> filter_sum_defl (with_null_map\<cdot>v)"
  by (domain_category_map_rule map_def: with_null_map_def iso_rews: with_null.iso_rews)

lemma separated_sum_defl_with_null_map [domain_category_map]:
  "deflation v \<Longrightarrow> separated_sum_defl (with_null_map\<cdot>v)"
  by (domain_category_map_rule map_def: with_null_map_def iso_rews: with_null.iso_rews)

instance with_null :: ("{domain, bounded_complete}") bounded_complete
  by (domain_category_instance map_ID: with_null_map_ID)

instance with_null :: ("domain") separated_sum
  by (domain_category_instance map_ID: with_null_map_ID)

lemma distributive_defl_with_null_map [domain_category_map]:
  "distributive_defl (v :: 'a::{domain, bounded_complete} \<rightarrow> 'a) \<Longrightarrow>
    distributive_defl (with_null_map\<cdot>v)"
  by (domain_category_map_rule map_def: with_null_map_def iso_rews: with_null.iso_rews)

instance with_null :: ("{domain, distributive_cpo}") distributive_cpo
  by (domain_category_instance map_ID: with_null_map_ID)

lemma locally_finitely_detailed_defl_with_null_map [domain_category_map]:
  "locally_finitely_detailed_defl v \<Longrightarrow> locally_finitely_detailed_defl (with_null_map\<cdot>v)"
  by (domain_category_map_rule map_def: with_null_map_def iso_rews: with_null.iso_rews)

instance with_null :: ("{domain, locally_finitely_detailed}") locally_finitely_detailed
  by (domain_category_instance map_ID: with_null_map_ID)

type_synonym 'v datum = "'v with_null"

section \<open>Coercions\<close>

text \<open>The plain value of a datum: \<open>Null\<close> becomes \<open>\<bottom>\<close>.\<close>

fixrec plain :: "'v::domain with_null \<rightarrow> 'v" where
  "plain\<cdot>Null = \<bottom>"
| "plain\<cdot>(Known\<cdot>x) = x"

lemma plain_strict [simp]: "plain\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

section \<open>Record-level operators\<close>

text \<open>Operators are lifted with \<open>Null\<close> infectious, as in SQL.  On known arguments the result
  is known, even when the operator diverges: a placeholder stays a placeholder.\<close>

fixrec null_lift2 ::
  "('a::domain \<rightarrow> 'b::domain \<rightarrow> 'c::domain) \<rightarrow> 'a with_null \<rightarrow> 'b with_null \<rightarrow> 'c with_null"
  where
  "null_lift2\<cdot>f\<cdot>Null\<cdot>Null = Null"
| "null_lift2\<cdot>f\<cdot>Null\<cdot>(Known\<cdot>y) = Null"
| "null_lift2\<cdot>f\<cdot>(Known\<cdot>x)\<cdot>Null = Null"
| "null_lift2\<cdot>f\<cdot>(Known\<cdot>x)\<cdot>(Known\<cdot>y) = Known\<cdot>(f\<cdot>x\<cdot>y)"

fixrec null_lift1 :: "('a::domain \<rightarrow> 'b::domain) \<rightarrow> 'a with_null \<rightarrow> 'b with_null" where
  "null_lift1\<cdot>f\<cdot>Null = Null"
| "null_lift1\<cdot>f\<cdot>(Known\<cdot>x) = Known\<cdot>(f\<cdot>x)"

abbreviation dlift1 :: "('a::domain \<rightarrow> 'b::domain) \<rightarrow> 'a datum \<rightarrow> 'b datum" where
  "dlift1 \<equiv> null_lift1"

abbreviation dlift2 :: "('a::domain \<rightarrow> 'b::domain \<rightarrow> 'c::domain) \<rightarrow> 'a datum \<rightarrow> 'b datum \<rightarrow> 'c datum" where
  "dlift2 \<equiv> null_lift2"

lemma null_lift1_strict [simp]: "null_lift1\<cdot>f\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

lemma null_lift2_strict [simp]: "null_lift2\<cdot>f\<cdot>\<bottom>\<cdot>y = \<bottom>" "null_lift2\<cdot>f\<cdot>x\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp (cases x; fixrec_simp)

text \<open>On plain values, a lifted strict operator is the operator itself.\<close>

lemma plain_dlift1:
  assumes "f\<cdot>\<bottom> = \<bottom>" shows "plain\<cdot>(dlift1\<cdot>f\<cdot>x) = f\<cdot>(plain\<cdot>x)"
  by (cases x) (simp_all add: assms)

lemma plain_dlift2:
  assumes "\<And>y. f\<cdot>\<bottom>\<cdot>y = \<bottom>" "\<And>x. f\<cdot>x\<cdot>\<bottom> = \<bottom>"
  shows "plain\<cdot>(dlift2\<cdot>f\<cdot>x\<cdot>y) = f\<cdot>(plain\<cdot>x)\<cdot>(plain\<cdot>y)"
  by (cases x; cases y) (simp_all add: assms)

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

text \<open>A condition's truth is three-valued, and \<open>Null\<close> is an unknown truth value.  Negation is
  lifted, so \<open>NOT NULL = NULL\<close>.  Conjunction and disjunction are Kleene's, as in SQL: a false
  conjunct makes a conjunction false whatever the others are, null or undefined, and dually a true
  disjunct a disjunction true.  @{text truth_d} projects a datum to @{typ tr}, sending \<open>Null\<close>,
  the placeholder and every non-boolean to \<open>\<bottom>\<close>; it is a homomorphism onto the parallel
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

definition truth_d :: "scalar datum \<rightarrow> tr" where
  "truth_d = sbool oo plain"

lemma truth_d_simps [simp]: "truth_d\<cdot>\<bottom> = \<bottom>" "truth_d\<cdot>Null = \<bottom>" "truth_d\<cdot>(Known\<cdot>s) = sbool\<cdot>s"
  by (simp_all add: truth_d_def)

lemma sbool_snot: "sbool\<cdot>(snot\<cdot>s) = neg\<cdot>(sbool\<cdot>s)"
  by (cases s; simp)

lemma truth_d_not: "truth_d\<cdot>(dlift1\<cdot>snot\<cdot>x) = neg\<cdot>(truth_d\<cdot>x)"
  by (cases x) (simp_all add: sbool_snot)

definition d_bool :: "tr \<rightarrow> scalar datum" where
  "d_bool = Known oo SBool"

lemma truth_d_bool [simp]: "truth_d\<cdot>(d_bool\<cdot>t) = t"
  by (simp add: d_bool_def)

fixrec is_null :: "'a::domain with_null \<rightarrow> tr" where
  "is_null\<cdot>Null = TT"
| "is_null\<cdot>(Known\<cdot>x) = FF"

lemma is_null_strict [simp]: "is_null\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

text \<open>The connectives read a datum only through whether it is null and its truth.  A boolean
  datum is \<open>\<bottom>\<close>, \<open>Null\<close>, true, false, or known but of unknown truth: the placeholder, or a
  non-boolean.\<close>

lemma datum_truth_cases [case_names bottom Null TT FF unknown]:
  obtains "x = \<bottom>" | "x = Null" | "x = d_bool\<cdot>TT" | "x = d_bool\<cdot>FF" | "is_null\<cdot>x = FF" "truth_d\<cdot>x = \<bottom>"
proof (cases x)
  case (Known s) then show ?thesis using that
  proof (cases s)
    case (SBool b) then show ?thesis using Known that by (cases b rule: trE) (simp_all add: d_bool_def)
  qed simp_all
qed (use that in simp_all)

text \<open>A conjunction is null where every conjunct is null or true and one is null; otherwise it
  is known, with the parallel conjunction of the truths, or undefined.\<close>

definition d_and :: "scalar datum \<rightarrow> scalar datum \<rightarrow> scalar datum" where
  "d_and = (\<Lambda> x y. If pand\<cdot>(pand\<cdot>(por\<cdot>(is_null\<cdot>x)\<cdot>(truth_d\<cdot>x))\<cdot>(por\<cdot>(is_null\<cdot>y)\<cdot>(truth_d\<cdot>y)))\<cdot>
     (por\<cdot>(is_null\<cdot>x)\<cdot>(is_null\<cdot>y)) then Null else Known\<cdot>(SBool\<cdot>(pand\<cdot>(truth_d\<cdot>x)\<cdot>(truth_d\<cdot>y))))"

definition d_or :: "scalar datum \<rightarrow> scalar datum \<rightarrow> scalar datum" where
  "d_or = (\<Lambda> x y. If pand\<cdot>(pand\<cdot>(por\<cdot>(is_null\<cdot>x)\<cdot>(neg\<cdot>(truth_d\<cdot>x)))\<cdot>(por\<cdot>(is_null\<cdot>y)\<cdot>(neg\<cdot>(truth_d\<cdot>y))))\<cdot>
     (por\<cdot>(is_null\<cdot>x)\<cdot>(is_null\<cdot>y)) then Null else Known\<cdot>(SBool\<cdot>(por\<cdot>(truth_d\<cdot>x)\<cdot>(truth_d\<cdot>y))))"

lemma d_and_apply: "d_and\<cdot>x\<cdot>y = (If pand\<cdot>(pand\<cdot>(por\<cdot>(is_null\<cdot>x)\<cdot>(truth_d\<cdot>x))\<cdot>(por\<cdot>(is_null\<cdot>y)\<cdot>(truth_d\<cdot>y)))\<cdot>
     (por\<cdot>(is_null\<cdot>x)\<cdot>(is_null\<cdot>y)) then Null else Known\<cdot>(SBool\<cdot>(pand\<cdot>(truth_d\<cdot>x)\<cdot>(truth_d\<cdot>y))))"
  and d_or_apply: "d_or\<cdot>x\<cdot>y = (If pand\<cdot>(pand\<cdot>(por\<cdot>(is_null\<cdot>x)\<cdot>(neg\<cdot>(truth_d\<cdot>x)))\<cdot>(por\<cdot>(is_null\<cdot>y)\<cdot>(neg\<cdot>(truth_d\<cdot>y))))\<cdot>
     (por\<cdot>(is_null\<cdot>x)\<cdot>(is_null\<cdot>y)) then Null else Known\<cdot>(SBool\<cdot>(por\<cdot>(truth_d\<cdot>x)\<cdot>(truth_d\<cdot>y))))"
  by (simp_all add: d_and_def d_or_def)

lemma truth_d_and: "truth_d\<cdot>(d_and\<cdot>x\<cdot>y) = pand\<cdot>(truth_d\<cdot>x)\<cdot>(truth_d\<cdot>y)"
  and truth_d_or: "truth_d\<cdot>(d_or\<cdot>x\<cdot>y) = por\<cdot>(truth_d\<cdot>x)\<cdot>(truth_d\<cdot>y)"
  by (cases x rule: datum_truth_cases; cases y rule: datum_truth_cases; simp add: d_and_apply d_or_apply d_bool_def)+

text \<open>SQL's tables, on the definite values.\<close>

lemma d_and_FF: "d_and\<cdot>(d_bool\<cdot>FF)\<cdot>y = d_bool\<cdot>FF" "d_and\<cdot>x\<cdot>(d_bool\<cdot>FF) = d_bool\<cdot>FF"
  by (cases y rule: datum_truth_cases; simp add: d_and_apply d_bool_def)
    (cases x rule: datum_truth_cases; simp add: d_and_apply d_bool_def)

lemma d_and_simps:
  "d_and\<cdot>(d_bool\<cdot>TT)\<cdot>(d_bool\<cdot>TT) = d_bool\<cdot>TT"
  "d_and\<cdot>(d_bool\<cdot>TT)\<cdot>Null = Null" "d_and\<cdot>Null\<cdot>(d_bool\<cdot>TT) = Null" "d_and\<cdot>Null\<cdot>Null = Null"
  by (simp_all add: d_and_apply d_bool_def)

lemma d_or_TT: "d_or\<cdot>(d_bool\<cdot>TT)\<cdot>y = d_bool\<cdot>TT" "d_or\<cdot>x\<cdot>(d_bool\<cdot>TT) = d_bool\<cdot>TT"
  by (cases y rule: datum_truth_cases; simp add: d_or_apply d_bool_def)
    (cases x rule: datum_truth_cases; simp add: d_or_apply d_bool_def)

lemma d_or_simps:
  "d_or\<cdot>(d_bool\<cdot>FF)\<cdot>(d_bool\<cdot>FF) = d_bool\<cdot>FF"
  "d_or\<cdot>(d_bool\<cdot>FF)\<cdot>Null = Null" "d_or\<cdot>Null\<cdot>(d_bool\<cdot>FF) = Null" "d_or\<cdot>Null\<cdot>Null = Null"
  by (simp_all add: d_or_apply d_bool_def)

section \<open>The not-null level of keys\<close>

text \<open>The atoms of @{typ "'a with_null"} are \<open>Null\<close> and \<open>Known\<cdot>\<bottom>\<close>, so its discriminator is the
  projection @{text not_null}, which observes only whether a key is \<open>Null\<close>.  It is a finitary
  semi-factor, i.e.\ a level of detail, and @{text is_null} factors through it.\<close>

fixrec not_null :: "'a::domain with_null \<rightarrow> 'a with_null" where
  "not_null\<cdot>Null = Null"
| "not_null\<cdot>(Known\<cdot>x) = Known\<cdot>\<bottom>"

lemma not_null_strict [simp]: "not_null\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

lemma atom_Null: "atom Null"
  by (rule atomI) (simp, case_tac z, simp_all)

lemma atom_Known_bottom: "atom (Known\<cdot>\<bottom>)"
  by (rule atomI) (simp, case_tac z, simp_all)

lemma discriminator_with_null:
  "discriminator\<cdot>x = not_null\<cdot>(x :: 'a::{domain, bounded_complete} with_null)"
proof (cases x)
  case bottom then show ?thesis by simp
next
  case Null then show ?thesis by (simp add: discriminator_eq[OF atom_Null below_refl])
next
  case (Known v)
  have "Known\<cdot>\<bottom> \<sqsubseteq> x" unfolding Known by (rule monofun_cfun_arg) simp
  then show ?thesis unfolding Known by (simp add: discriminator_eq[OF atom_Known_bottom])
qed

lemma not_null_level:
  "semi_factor_defl (not_null :: 'a::{domain, distributive_cpo} with_null \<rightarrow> 'a with_null)"
  "finitary (not_null :: 'a::{domain, distributive_cpo} with_null \<rightarrow> 'a with_null)"
  using discriminator_semi_factor discriminator_finitary
  by (simp_all add: cfun_eqI[OF discriminator_with_null, symmetric])

lemma is_null_not_null: "is_null\<cdot>(not_null\<cdot>x) = is_null\<cdot>x"
  by (cases x) simp_all

end
