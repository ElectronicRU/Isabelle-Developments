theory Ast
  imports Expr_Combinators Value
begin

section \<open>Expression syntax\<close>

text \<open>The abstract syntax of the expression language, after name resolution: references to
  dimensions and to table columns, literals, calls of function symbols, aggregations, requested
  grouping (\<open>GROUP BY\<close>), explicit cuts (\<open>FOR\<close>) and filters (\<open>WHERE\<close>).  Values are concrete:
  literals and expressions are data (@{typ "scalar datum"}), dimensions are keys
  (@{typ "scalar with_na"}).  The conditions of cuts are boolean expressions on dimensions, which
  serve as slices; filters are row-level boolean expressions, which may read columns.
  Not yet covered: \<open>DISTINCT\<close>, \<open>ISOLATE\<close>, \<open>TOTAL\<close>, and the dimension kind (which needs
  staging).\<close>

text \<open>Function symbols: the connectives, equality and the \<open>NA\<close> test are known to the language,
  for normal forms, coarsening and pins; other symbols are interpreted by a table.\<close>

datatype 'fn fsym = FAnd | FOr | FNot | FEq | FIsNA | FOther 'fn

datatype ('d, 'c, 'fn, 'ag) ast =
  Dim 'd
| Col 'c
| Lit "scalar datum"
| Call "'fn fsym" "('d, 'c, 'fn, 'ag) ast list"
| Aggr 'ag "('d, 'c, 'fn, 'ag) ast"
| GroupBy "'d list" "('d, 'c, 'fn, 'ag) ast"
| For "'d list" "('d, 'c, 'fn, 'ag) ast" "('d, 'c, 'fn, 'ag) ast"
| Where "('d, 'c, 'fn, 'ag) ast" "('d, 'c, 'fn, 'ag) ast"

section \<open>The known function symbols\<close>

text \<open>Booleans as data, and the n-ary connectives: strict, so every missing argument is
  infectious.  The empty conjunction is true, the empty disjunction false.\<close>

definition d_bool :: "tr \<rightarrow> scalar datum" where
  "d_bool = na_emb oo Known oo SBool"

text \<open>Calls take the list of their arguments' values.  Continuous functions on lists are given by
  recursion, and arguments of a fixed arity are matched by length, which is rigid.\<close>

primrec ands :: "scalar datum list \<Rightarrow> scalar datum" where
  "ands [] = d_bool\<cdot>TT"
| "ands (x # xs) = dlift2\<cdot>sand\<cdot>x\<cdot>(ands xs)"

primrec ors :: "scalar datum list \<Rightarrow> scalar datum" where
  "ors [] = d_bool\<cdot>FF"
| "ors (x # xs) = dlift2\<cdot>sor\<cdot>x\<cdot>(ors xs)"

lemma cont_ands: "cont ands" and cont_ors: "cont ors"
  by (rule list_contI[where g = "\<lambda>x xs y. dlift2\<cdot>sand\<cdot>x\<cdot>y"], simp_all)
    (rule list_contI[where g = "\<lambda>x xs y. dlift2\<cdot>sor\<cdot>x\<cdot>y"], simp_all)

definition d_ands :: "scalar datum list \<rightarrow> scalar datum" where
  "d_ands = (\<Lambda> xs. ands xs)"

definition d_ors :: "scalar datum list \<rightarrow> scalar datum" where
  "d_ors = (\<Lambda> xs. ors xs)"

lemma d_ands_simps [simp]: "d_ands\<cdot>[] = d_bool\<cdot>TT" "d_ands\<cdot>(x # xs) = dlift2\<cdot>sand\<cdot>x\<cdot>(d_ands\<cdot>xs)"
  and d_ors_simps [simp]: "d_ors\<cdot>[] = d_bool\<cdot>FF" "d_ors\<cdot>(x # xs) = dlift2\<cdot>sor\<cdot>x\<cdot>(d_ors\<cdot>xs)"
  by (simp_all add: d_ands_def d_ors_def cont_ands cont_ors)

definition arg1 :: "('a::cpo \<rightarrow> 'b::pcpo) \<Rightarrow> 'a list \<rightarrow> 'b" where
  "arg1 f = (\<Lambda> xs. if length xs = 1 then f\<cdot>(hd xs) else \<bottom>)"

definition arg2 :: "('a::cpo \<rightarrow> 'a \<rightarrow> 'b::pcpo) \<Rightarrow> 'a list \<rightarrow> 'b" where
  "arg2 f = (\<Lambda> xs. if length xs = 2 then f\<cdot>(hd xs)\<cdot>(hd (tl xs)) else \<bottom>)"

lemma arg1_beta [simp]: "arg1 f\<cdot>xs = (if length xs = 1 then f\<cdot>(hd xs) else \<bottom>)"
  unfolding arg1_def by (rule beta_cfun) (rule cont_if_rigid[OF rigid_length]; simp)

lemma arg2_beta [simp]: "arg2 f\<cdot>xs = (if length xs = 2 then f\<cdot>(hd xs)\<cdot>(hd (tl xs)) else \<bottom>)"
  unfolding arg2_def by (rule beta_cfun) (rule cont_if_rigid[OF rigid_length]; simp)


definition d_eq :: "scalar datum \<rightarrow> scalar datum \<rightarrow> scalar datum" where
  "d_eq = dlift2\<cdot>(\<Lambda> x y. SBool\<cdot>(scalar_eq\<cdot>x\<cdot>y))"

definition d_is_na :: "scalar datum \<rightarrow> scalar datum" where
  "d_is_na = (\<Lambda> x. d_bool\<cdot>(is_na\<cdot>x))"

primrec fsym_sem :: "('fn \<Rightarrow> scalar datum list \<rightarrow> scalar datum) \<Rightarrow> 'fn fsym \<Rightarrow> scalar datum list \<rightarrow> scalar datum" where
  "fsym_sem other FAnd = d_ands"
| "fsym_sem other FOr = d_ors"
| "fsym_sem other FNot = arg1 (dlift1\<cdot>snot)"
| "fsym_sem other FEq = arg2 d_eq"
| "fsym_sem other FIsNA = arg1 d_is_na"
| "fsym_sem other (FOther fn) = other fn"

primrec fsym_arity :: "('fn \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> 'fn fsym \<Rightarrow> nat \<Rightarrow> bool" where
  "fsym_arity other FAnd n \<longleftrightarrow> True"
| "fsym_arity other FOr n \<longleftrightarrow> True"
| "fsym_arity other FNot n \<longleftrightarrow> n = 1"
| "fsym_arity other FEq n \<longleftrightarrow> n = 2"
| "fsym_arity other FIsNA n \<longleftrightarrow> n = 1"
| "fsym_arity other (FOther fn) n \<longleftrightarrow> other fn n"

lemma truth_d_bool [simp]: "truth_d\<cdot>(d_bool\<cdot>t) = t"
  by (cases t rule: trE) (simp_all add: d_bool_def truth_d_def)

text \<open>Truth of the connectives: a conjunction is true where all conjuncts are; a disjunction
  where all disjuncts are defined and one is true.  Both are defined where all arguments are.\<close>

lemma tr_and_TT_iff: "tr_and\<cdot>x\<cdot>y = TT \<longleftrightarrow> x = TT \<and> y = TT"
  by (cases x rule: trE; cases y rule: trE) (simp_all add: TT_def FF_def)

lemma tr_and_bot_iff: "tr_and\<cdot>x\<cdot>y = \<bottom> \<longleftrightarrow> x = \<bottom> \<or> y = \<bottom>"
  by (cases x rule: trE; cases y rule: trE) (simp_all add: TT_def FF_def)

lemma tr_or_TT_iff: "tr_or\<cdot>x\<cdot>y = TT \<longleftrightarrow> x \<noteq> \<bottom> \<and> y \<noteq> \<bottom> \<and> (x = TT \<or> y = TT)"
  by (cases x rule: trE; cases y rule: trE) (simp_all add: TT_def FF_def)

lemma tr_or_bot_iff: "tr_or\<cdot>x\<cdot>y = \<bottom> \<longleftrightarrow> x = \<bottom> \<or> y = \<bottom>"
  by (cases x rule: trE; cases y rule: trE) (simp_all add: TT_def FF_def)

lemma truth_d_ands:
  "truth_d\<cdot>(d_ands\<cdot>xs) = TT \<longleftrightarrow> (\<forall>x\<in>set xs. truth_d\<cdot>x = TT)"
  "truth_d\<cdot>(d_ands\<cdot>xs) \<noteq> \<bottom> \<longleftrightarrow> (\<forall>x\<in>set xs. truth_d\<cdot>x \<noteq> \<bottom>)"
  by (induct xs) (simp_all add: truth_d_and[simplified] tr_and_TT_iff tr_and_bot_iff)

lemma truth_d_ors:
  "truth_d\<cdot>(d_ors\<cdot>xs) = TT \<longleftrightarrow> (\<forall>x\<in>set xs. truth_d\<cdot>x \<noteq> \<bottom>) \<and> (\<exists>x\<in>set xs. truth_d\<cdot>x = TT)"
  "truth_d\<cdot>(d_ors\<cdot>xs) \<noteq> \<bottom> \<longleftrightarrow> (\<forall>x\<in>set xs. truth_d\<cdot>x \<noteq> \<bottom>)"
  by (induct xs) (auto simp: truth_d_or[simplified] tr_or_TT_iff tr_or_bot_iff)

section \<open>Dimensions and the key reading\<close>

text \<open>Dimensions name LODs of the keys, each with a value read off the key there.  A dimension's
  value reads only its LOD, and at its LOD it is the whole information: the value orders the
  key's part at the LOD.  Nothing ties dimensions to each other: hierarchies are inclusions of
  their LODs.  Every compact key lists dimensions it lives at, possibly more than it needs (a
  year key may list the day).  Expressions on dimensions alone, with the known and the tabled
  function symbols, read keys directly.\<close>

primrec tuple_cfun :: "('r::cpo \<rightarrow> 'v::cpo) list \<Rightarrow> 'r \<rightarrow> 'v list" where
  "tuple_cfun [] = (\<Lambda> y. [])"
| "tuple_cfun (g # gs) = (\<Lambda> y. g\<cdot>y # tuple_cfun gs\<cdot>y)"

lemma tuple_cfun_apply: "tuple_cfun gs\<cdot>y = map (\<lambda>g. g\<cdot>y) gs"
  by (induct gs) simp_all

definition key_datum :: "scalar with_na \<rightarrow> scalar datum" where
  "key_datum = na_bind\<cdot>(Val oo Known)"

lemma key_datum_simps [simp]:
  "key_datum\<cdot>\<bottom> = \<bottom>" "key_datum\<cdot>NA = NA" "key_datum\<cdot>(Val\<cdot>x) = Val\<cdot>(Known\<cdot>x)"
  by (simp_all add: key_datum_def)

locale key_language =
  fixes dim_lod :: "'d \<Rightarrow> 'k::lod_domain semi_factor"
    and dim_val :: "'d \<Rightarrow> 'k \<rightarrow> scalar with_na"
    and key_dims :: "'k \<Rightarrow> 'd list"
    and fn_other :: "'fn \<Rightarrow> scalar datum list \<rightarrow> scalar datum"
  assumes dim_compact: "compact (dim_lod d)"
    and dim_reads: "dim_val d\<cdot>(proj (dim_lod d)\<cdot>k) = dim_val d\<cdot>k"
    and dim_reflects: "dim_val d\<cdot>k \<sqsubseteq> dim_val d\<cdot>k' \<Longrightarrow> proj (dim_lod d)\<cdot>k \<sqsubseteq> proj (dim_lod d)\<cdot>k'"
    and key_dims_lives: "compact K \<Longrightarrow> proj (fold (\<squnion>) (map dim_lod (key_dims K)) \<bottom>)\<cdot>K = K"
begin

definition lod :: "'d list \<Rightarrow> 'k semi_factor" where
  "lod ds = fold (\<squnion>) (map dim_lod ds) \<bottom>"

lemma dim_below_iff: "dim_val d\<cdot>k \<sqsubseteq> dim_val d\<cdot>k' \<longleftrightarrow> proj (dim_lod d)\<cdot>k \<sqsubseteq> proj (dim_lod d)\<cdot>k'"
  by (metis dim_reflects dim_reads monofun_cfun_arg)

lemma dim_eq_iff: "dim_val d\<cdot>k = dim_val d\<cdot>k' \<longleftrightarrow> proj (dim_lod d)\<cdot>k = proj (dim_lod d)\<cdot>k'"
  by (simp add: po_eq_conv dim_below_iff)

lemma fold_join_least:
  "b \<sqsubseteq> c \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> x \<sqsubseteq> c) \<Longrightarrow> fold (\<squnion>) xs b \<sqsubseteq> (c :: 'a::lattice_complete)"
  by (induct xs arbitrary: b) (simp_all add: join_belowI)

lemma lod_below_iff: "lod ds \<sqsubseteq> c \<longleftrightarrow> (\<forall>d\<in>set ds. dim_lod d \<sqsubseteq> c)"
proof
  assume "lod ds \<sqsubseteq> c"
  moreover have "dim_lod d \<sqsubseteq> lod ds" if "d \<in> set ds" for d
    unfolding lod_def by (rule fold_join_upper) (simp add: that)
  ultimately show "\<forall>d\<in>set ds. dim_lod d \<sqsubseteq> c" by (blast intro: below_trans)
qed (unfold lod_def, rule fold_join_least, auto)

lemma compact_lod: "compact (lod ds)"
  unfolding lod_def by (rule compact_fold_sup) (auto simp: dim_compact)

text \<open>A key is below another as soon as each of its listed dimensions' values is.\<close>

lemma proj_fold_below:
  assumes "proj b\<cdot>K \<sqsubseteq> k" and "\<And>d. d \<in> set ds \<Longrightarrow> proj (dim_lod d)\<cdot>K \<sqsubseteq> k"
  shows "proj (fold (\<squnion>) (map dim_lod ds) b)\<cdot>K \<sqsubseteq> k"
  using assms by (induct ds arbitrary: b) (simp_all add: proj_sup join_belowI)

lemma key_dims_below:
  assumes K: "compact K" and le: "\<And>d. d \<in> set (key_dims K) \<Longrightarrow> dim_val d\<cdot>K \<sqsubseteq> dim_val d\<cdot>k"
  shows "K \<sqsubseteq> k"
proof -
  have "proj (fold (\<squnion>) (map dim_lod (key_dims K)) \<bottom>)\<cdot>K \<sqsubseteq> k"
  proof (rule proj_fold_below)
    show "proj \<bottom>\<cdot>K \<sqsubseteq> k" by (simp add: proj_bot)
    show "proj (dim_lod d)\<cdot>K \<sqsubseteq> k" if "d \<in> set (key_dims K)" for d
      using dim_reflects[OF le[OF that]] proj_below by (rule below_trans)
  qed
  then show ?thesis by (simp only: key_dims_lives[OF K])
qed

subsection \<open>The key reading\<close>

fun kdims :: "('d, 'c, 'fn, 'ag) ast \<Rightarrow> 'd list" where
  "kdims (Dim d) = [d]"
| "kdims (Call fn es) = concat (map kdims es)"
| "kdims _ = []"

fun kval :: "('d, 'c, 'fn, 'ag) ast \<Rightarrow> 'k \<rightarrow> scalar datum" where
  "kval (Dim d) = key_datum oo dim_val d"
| "kval (Lit v) = (\<Lambda> _. v)"
| "kval (Call fn es) = fsym_sem fn_other fn oo tuple_cfun (map kval es)"
| "kval _ = \<bottom>"

definition reads_in :: "'k semi_factor \<Rightarrow> ('d, 'c, 'fn, 'ag) ast \<Rightarrow> bool" where
  "reads_in A e \<longleftrightarrow> (\<forall>d\<in>set (kdims e). dim_lod d \<sqsubseteq> A)"

lemma kval_reads: "reads_in A e \<Longrightarrow> kval e\<cdot>(proj A\<cdot>k) = kval e\<cdot>k"
proof (induct e rule: kval.induct)
  case (1 d)
  have "dim_val d\<cdot>(proj A\<cdot>k) = dim_val d\<cdot>(proj (dim_lod d)\<cdot>(proj A\<cdot>k))" by (simp only: dim_reads)
  also have "\<dots> = dim_val d\<cdot>k" using 1 by (simp add: reads_in_def proj_le dim_reads)
  finally show ?case by simp
next
  case (3 fn es)
  then have "map (\<lambda>e. kval e\<cdot>(proj A\<cdot>k)) es = map (\<lambda>e. kval e\<cdot>k) es" by (auto simp: reads_in_def)
  then show ?case by (simp only: kval.simps cfcomp2 tuple_cfun_apply map_map comp_def)
qed simp_all

definition kholds :: "('d, 'c, 'fn, 'ag) ast \<Rightarrow> 'k \<Rightarrow> bool" where
  "kholds e k \<longleftrightarrow> truth_d\<cdot>(kval e\<cdot>k) = TT"

lemma kholds_up: "kholds e k \<Longrightarrow> k \<sqsubseteq> k' \<Longrightarrow> kholds e k'"
  unfolding kholds_def by (metis TT_below_iff monofun_cfun_arg)

lemma kholds_open: "adm (\<lambda>k. \<not> kholds e k)"
  unfolding kholds_def by (simp add: compact_TT eq_commute[of _ TT])

lemma reads_in_meet: "reads_in (A \<sqinter> B) e \<longleftrightarrow> reads_in A e \<and> reads_in B e"
  unfolding reads_in_def
  by (blast intro: lattice_meet_greatest below_trans[OF _ lattice_meet_le1] below_trans[OF _ lattice_meet_le2])

subsection \<open>Coarsening conditions\<close>

text \<open>Coarsening a condition to an LOD drops what reads outside it, as in the source:
  conjunctions keep their surviving conjuncts (and vanish when none survives), disjunctions
  vanish as soon as one disjunct does, anything else survives whole or not at all.  Dropping
  only ever replaces a part in positive position by truth, so it weakens: what was true stays
  true, what was defined stays defined.  Negation is not looked into; normal forms push it to
  the literals first.\<close>

fun crs :: "'k semi_factor \<Rightarrow> ('d, 'c, 'fn, 'ag) ast \<Rightarrow> ('d, 'c, 'fn, 'ag) ast option" where
  "crs A (Call FAnd es) = (if es \<noteq> [] \<and> filter (\<lambda>r. r \<noteq> None) (map (crs A) es) = [] then None
     else Some (Call FAnd (map the (filter (\<lambda>r. r \<noteq> None) (map (crs A) es)))))"
| "crs A (Call FOr es) = (if None \<in> set (map (crs A) es) then None
     else Some (Call FOr (map the (map (crs A) es))))"
| "crs A e = (if reads_in A e then Some e else None)"

lemma set_kept: "set (map the (filter (\<lambda>r. r \<noteq> None) (map f xs))) = {y. \<exists>x\<in>set xs. f x = Some y}"
  by (induct xs) auto

lemma set_all_some:
  "None \<notin> set (map f xs) \<Longrightarrow> set (map the (map f xs)) = {y. \<exists>x\<in>set xs. f x = Some y}"
  by (induct xs) auto

lemma crs_inside: "reads_in A e \<Longrightarrow> crs A e = Some e"
proof (induct A e rule: crs.induct)
  case (1 A es)
  have "map (crs A) es = map Some es" using 1(1) 1(3) by (simp add: reads_in_def)
  then show ?case by (simp add: comp_def filter_map cong: map_cong)
next
  case (2 A es)
  have "map (crs A) es = map Some es" using 2(1) 2(3) by (simp add: reads_in_def)
  then show ?case by (simp add: comp_def cong: map_cong)
qed simp_all

lemma crs_reads: "crs A e = Some e' \<Longrightarrow> reads_in A e' \<and> set (kdims e') \<subseteq> set (kdims e)"
proof (induct A e arbitrary: e' rule: crs.induct)
  case (1 A es)
  have IH: "reads_in A c' \<and> set (kdims c') \<subseteq> set (kdims c)" if "c \<in> set es" "crs A c = Some c'" for c c'
    using 1(1)[OF that] .
  obtain es' where e': "e' = Call FAnd es'" and es': "set es' = {c'. \<exists>c\<in>set es. crs A c = Some c'}"
    using 1(3) set_kept[of "crs A" es] by (auto split: if_splits)
  show ?case unfolding e' using es' IH by (fastforce simp: reads_in_def)
next
  case (2 A es)
  have IH: "reads_in A c' \<and> set (kdims c') \<subseteq> set (kdims c)" if "c \<in> set es" "crs A c = Some c'" for c c'
    using 2(1)[OF that] .
  obtain es' where e': "e' = Call FOr es'" and es': "set es' = {c'. \<exists>c\<in>set es. crs A c = Some c'}"
    using 2(3) set_all_some[of "crs A" es] by (auto split: if_splits)
  show ?case unfolding e' using es' IH by (fastforce simp: reads_in_def)
qed (auto split: if_splits)

lemma kept_kept:
  "map the (filter (\<lambda>r. r \<noteq> None) (map g (map the (filter (\<lambda>r. r \<noteq> None) (map f xs)))))
    = map the (filter (\<lambda>r. r \<noteq> None) (map (\<lambda>x. Option.bind (f x) g) xs))"
  by (induct xs) (auto split: option.split)

lemma all_some_bind:
  "None \<notin> set (map f xs) \<Longrightarrow> map g (map the (map f xs)) = map (\<lambda>x. Option.bind (f x) g) xs"
  by (induct xs) (auto, metis option.exhaust_sel bind.simps(2))

lemma crs_bind: "Option.bind (crs B e) (crs A) = crs (A \<sqinter> B) e"
proof (induct B e arbitrary: A rule: crs.induct)
  case (1 B es)
  have IH: "map (crs (A \<sqinter> B)) es = map (\<lambda>c. Option.bind (crs B c) (crs A)) es"
    using 1(1) by simp
  show ?case
  proof (cases "es \<noteq> [] \<and> filter (\<lambda>r. r \<noteq> None) (map (crs B) es) = []")
    case True
    then have "filter (\<lambda>r. r \<noteq> None) (map (crs (A \<sqinter> B)) es) = []"
      unfolding IH by (auto simp: filter_empty_conv)
    then show ?thesis using True by simp
  next
    case False
    have kk: "map the (filter (\<lambda>r. r \<noteq> None) (map (crs A) (map the (filter (\<lambda>r. r \<noteq> None) (map (crs B) es)))))
        = map the (filter (\<lambda>r. r \<noteq> None) (map (crs (A \<sqinter> B)) es))" unfolding kept_kept IH ..
    have nil: "map the xs = [] \<longleftrightarrow> xs = []" for xs :: "'x option list" by simp
    show ?thesis
      unfolding crs.simps(1)[of B] if_not_P[OF False] bind.simps(2) crs.simps(1)[of A] crs.simps(1)[of "A \<sqinter> B"] kk
      apply (rule if_cong[OF _ refl refl])
      using False arg_cong[OF kk, of "\<lambda>xs. xs = []"] unfolding nil by (cases es) auto
  qed
next
  case (2 B es)
  have IH: "map (crs (A \<sqinter> B)) es = map (\<lambda>c. Option.bind (crs B c) (crs A)) es"
    using 2(1) by simp
  show ?case
  proof (cases "None \<in> set (map (crs B) es)")
    case True
    then have "None \<in> set (map (crs (A \<sqinter> B)) es)" unfolding IH by force
    then show ?thesis using True by simp
  next
    case False
    have "map (crs A) (map the (map (crs B) es)) = map (crs (A \<sqinter> B)) es"
      unfolding IH by (rule all_some_bind[OF False])
    then show ?thesis
      unfolding crs.simps(2)[of B] if_not_P[OF False] bind.simps(2) crs.simps(2)[of A] crs.simps(2)[of "A \<sqinter> B"]
      by simp
  qed
qed (auto simp: reads_in_meet)

lemma kval_call [simp]: "kval (Call fn es)\<cdot>k = fsym_sem fn_other fn\<cdot>(map (\<lambda>e. kval e\<cdot>k) es)"
  by (simp add: tuple_cfun_apply comp_def)

text \<open>Coarsening weakens: true stays true, defined stays defined.\<close>

lemma crs_weakens:
  "crs A e = Some e' \<Longrightarrow> (truth_d\<cdot>(kval e\<cdot>k) = TT \<longrightarrow> truth_d\<cdot>(kval e'\<cdot>k) = TT) \<and>
     (truth_d\<cdot>(kval e\<cdot>k) \<noteq> \<bottom> \<longrightarrow> truth_d\<cdot>(kval e'\<cdot>k) \<noteq> \<bottom>)"
proof (induct A e arbitrary: e' rule: crs.induct)
  case (1 A es)
  have IH: "(truth_d\<cdot>(kval c\<cdot>k) = TT \<longrightarrow> truth_d\<cdot>(kval c'\<cdot>k) = TT) \<and>
      (truth_d\<cdot>(kval c\<cdot>k) \<noteq> \<bottom> \<longrightarrow> truth_d\<cdot>(kval c'\<cdot>k) \<noteq> \<bottom>)" if "c \<in> set es" "crs A c = Some c'" for c c'
    using 1(1)[OF that] .
  obtain es' where e': "e' = Call FAnd es'" and es': "set es' = {c'. \<exists>c\<in>set es. crs A c = Some c'}"
    using 1(3) set_kept[of "crs A" es] by (auto split: if_splits)
  show ?case unfolding e' kval_call fsym_sem.simps using es' IH by (auto simp: truth_d_ands)
next
  case (2 A es)
  have IH: "(truth_d\<cdot>(kval c\<cdot>k) = TT \<longrightarrow> truth_d\<cdot>(kval c'\<cdot>k) = TT) \<and>
      (truth_d\<cdot>(kval c\<cdot>k) \<noteq> \<bottom> \<longrightarrow> truth_d\<cdot>(kval c'\<cdot>k) \<noteq> \<bottom>)" if "c \<in> set es" "crs A c = Some c'" for c c'
    using 2(1)[OF that] .
  have all: "\<exists>c'. crs A c = Some c'" if "c \<in> set es" for c
    using 2(3) that by (auto split: if_splits) (metis image_eqI option.exhaust)
  obtain es' where e': "e' = Call FOr es'" and es': "set es' = {c'. \<exists>c\<in>set es. crs A c = Some c'}"
    using 2(3) set_all_some[of "crs A" es] by (auto split: if_splits)
  have defd: "\<forall>c'\<in>set es'. truth_d\<cdot>(kval c'\<cdot>k) \<noteq> \<bottom>" if "\<forall>c\<in>set es. truth_d\<cdot>(kval c\<cdot>k) \<noteq> \<bottom>"
    using that IH unfolding es' by blast
  have T: "truth_d\<cdot>(kval (Call FOr xs)\<cdot>k) = TT \<longleftrightarrow>
      (\<forall>c\<in>set xs. truth_d\<cdot>(kval c\<cdot>k) \<noteq> \<bottom>) \<and> (\<exists>c\<in>set xs. truth_d\<cdot>(kval c\<cdot>k) = TT)"
    and D: "truth_d\<cdot>(kval (Call FOr xs)\<cdot>k) \<noteq> \<bottom> \<longleftrightarrow> (\<forall>c\<in>set xs. truth_d\<cdot>(kval c\<cdot>k) \<noteq> \<bottom>)" for xs
    unfolding kval_call fsym_sem.simps by (simp_all add: truth_d_ors)
  show ?case unfolding e' T D
  proof (rule conjI; rule impI)
    assume "(\<forall>c\<in>set es. truth_d\<cdot>(kval c\<cdot>k) \<noteq> \<bottom>) \<and> (\<exists>c\<in>set es. truth_d\<cdot>(kval c\<cdot>k) = TT)"
    then have d: "\<forall>c\<in>set es. truth_d\<cdot>(kval c\<cdot>k) \<noteq> \<bottom>" and "\<exists>c\<in>set es. truth_d\<cdot>(kval c\<cdot>k) = TT" by blast+
    then obtain c c' where c: "c \<in> set es" "truth_d\<cdot>(kval c\<cdot>k) = TT" and c': "crs A c = Some c'" using all by blast
    have "c' \<in> set es'" using c(1) c' unfolding es' by blast
    then show "(\<forall>c\<in>set es'. truth_d\<cdot>(kval c\<cdot>k) \<noteq> \<bottom>) \<and> (\<exists>c\<in>set es'. truth_d\<cdot>(kval c\<cdot>k) = TT)"
      using defd[OF d] IH[OF c(1) c'] c(2) by blast
  next
    show "\<forall>c\<in>set es'. truth_d\<cdot>(kval c\<cdot>k) \<noteq> \<bottom>" if "\<forall>c\<in>set es. truth_d\<cdot>(kval c\<cdot>k) \<noteq> \<bottom>"
      by (rule defd[OF that])
  qed
qed (auto split: if_splits)

lemma reads_in_mono: "reads_in A e \<Longrightarrow> A \<sqsubseteq> B \<Longrightarrow> reads_in B e"
  unfolding reads_in_def by (blast intro: below_trans)

lemma reads_in_lod: "reads_in (lod (kdims e)) e"
  unfolding reads_in_def using lod_below_iff[of "kdims e" "lod (kdims e)"] by simp

end

section \<open>Conditions as slices\<close>

text \<open>A slice is a finite set of conditions, read as their conjunction; it is written at the
  join of their dimensions' LODs.  Pins conjoin a test per dimension the key lists: \<open>IS NA\<close>,
  \<open>NOT IS NA\<close>, or equality with the key's value, as the value is \<open>NA\<close>, the not-null root, or a
  scalar.\<close>

type_synonym ('d, 'c, 'fn, 'ag) slice = "('d, 'c, 'fn, 'ag) ast fset"

lemma lattice_lub_empty: "lub {} = (\<bottom> :: 'a::lattice_complete)"
  by (rule bottomI) (rule lattice_lub_least, simp)

lemma lattice_lub_Un: "lub (A \<union> B) = lub A \<squnion> (lub B :: 'a::lattice_complete)"
proof (rule below_antisym)
  show "lub (A \<union> B) \<sqsubseteq> lub A \<squnion> lub B"
    by (rule lattice_lub_least, rule is_ubI)
      (auto intro: below_trans[OF lattice_lub_upper lattice_join_ge1] below_trans[OF lattice_lub_upper lattice_join_ge2])
  show "lub A \<squnion> lub B \<sqsubseteq> lub (A \<union> B)"
    by (rule join_belowI; rule lattice_lub_least, rule is_ubI, rule lattice_lub_upper) simp_all
qed

lemma lattice_lub_compact:
  "finite S \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> compact x) \<Longrightarrow> compact (lub S :: 'k::{bifinite, distributive_cpo} semi_factor)"
proof (induct rule: finite_induct)
  case empty
  then show ?case by (simp add: lattice_lub_empty)
next
  case (insert x S)
  have "lub (insert x S) = lub {x} \<squnion> lub S" using lattice_lub_Un[of "{x}" S] by simp
  moreover have "lub {x} = x" by (rule lub_singleton)
  ultimately show ?case using insert by (simp add: compact_semi_factor_sup)
qed

lemma adm_not_ball_finite:
  "finite S \<Longrightarrow> (\<And>e. e \<in> S \<Longrightarrow> adm (\<lambda>k. \<not> P e k)) \<Longrightarrow> adm (\<lambda>k. \<not> (\<forall>e\<in>S. P e k))"
  by (induct rule: finite_induct) (simp_all add: adm_disj)

context key_language
begin

definition slice_lod :: "('d, 'c, 'fn, 'ag) slice \<Rightarrow> 'k semi_factor" where
  "slice_lod S = lub ((\<lambda>e. lod (kdims e)) ` fset S)"

definition slice_open :: "('d, 'c, 'fn, 'ag) slice \<Rightarrow> 'k sel" where
  "slice_open S = Abs_sel (\<lambda>k. \<forall>e\<in>fset S. kholds e k)"

lemma selects_slice_open [simp]: "selects (slice_open S) k \<longleftrightarrow> (\<forall>e\<in>fset S. kholds e k)"
proof -
  have up: "\<forall>x y. (\<forall>e\<in>fset S. kholds e x) \<longrightarrow> x \<sqsubseteq> y \<longrightarrow> (\<forall>e\<in>fset S. kholds e y)"
    by (blast intro: kholds_up)
  have adm: "adm (\<lambda>k. \<not> (\<forall>e\<in>fset S. kholds e k))"
    by (rule adm_not_ball_finite[OF finite_fset kholds_open])
  have "(\<lambda>k. \<forall>e\<in>fset S. kholds e k) \<in> {P. (\<forall>x y. P x \<longrightarrow> x \<sqsubseteq> y \<longrightarrow> P y) \<and> adm (\<lambda>x. \<not> P x)}"
    using up adm by (simp only: mem_Collect_eq)
  then show ?thesis by (simp only: slice_open_def Abs_sel_inverse)
qed

definition slice_coarsen :: "'k semi_factor \<Rightarrow> ('d, 'c, 'fn, 'ag) slice \<Rightarrow> ('d, 'c, 'fn, 'ag) slice" where
  "slice_coarsen A S = Abs_fset {e'. \<exists>e\<in>fset S. crs A e = Some e'}"

lemma fset_slice_coarsen: "fset (slice_coarsen A S) = {e'. \<exists>e\<in>fset S. crs A e = Some e'}"
proof -
  have "finite {e'. \<exists>e\<in>fset S. crs A e = Some e'}"
    by (rule finite_subset[of _ "(\<lambda>e. the (crs A e)) ` fset S"]) (auto intro: rev_image_eqI)
  then show ?thesis unfolding slice_coarsen_def by (rule Abs_fset_inverse[simplified])
qed

definition pin_test :: "'k \<Rightarrow> 'd \<Rightarrow> ('d, 'c, 'fn, 'ag) ast list" where
  "pin_test K d = (if dim_val d\<cdot>K = \<bottom> then []
     else if dim_val d\<cdot>K = NA then [Call FIsNA [Dim d]]
     else if dim_val d\<cdot>K = Val\<cdot>\<bottom> then [Call FNot [Call FIsNA [Dim d]]]
     else [Call FEq [Dim d, Lit (key_datum\<cdot>(dim_val d\<cdot>K))]])"

definition slice_pin :: "'k \<Rightarrow> ('d, 'c, 'fn, 'ag) slice" where
  "slice_pin K = fset_of_list (concat (map (pin_test K) (key_dims K)))"

definition ast_slicing :: "(('d, 'c, 'fn, 'ag) slice, 'k) slicer_ops" where
  "ast_slicing = \<lparr>sl_conj = (|\<union>|), sl_unit = {||}, sl_lod = slice_lod, sl_open = slice_open,
     sl_coarsen = slice_coarsen, sl_pin = slice_pin\<rparr>"

subsection \<open>The slicer laws\<close>

lemma slice_lod_union: "slice_lod (S |\<union>| T) = slice_lod S \<squnion> slice_lod T"
  by (simp add: slice_lod_def image_Un lattice_lub_Un)

lemma slice_lod_empty: "slice_lod {||} = \<bottom>"
  by (simp add: slice_lod_def lattice_lub_empty)

lemma slice_open_union: "slice_open (S |\<union>| T) = inf (slice_open S) (slice_open T)"
  by (rule sel_eqI) auto

lemma slice_open_empty: "slice_open {||} = top"
  by (rule sel_eqI) simp

lemma lod_below_slice_lod: "e |\<in>| S \<Longrightarrow> lod (kdims e) \<sqsubseteq> slice_lod S"
  unfolding slice_lod_def by (rule lattice_lub_upper) simp

lemma reads_in_slice_lod: "e |\<in>| S \<Longrightarrow> reads_in (slice_lod S) e"
  by (rule reads_in_mono[OF reads_in_lod lod_below_slice_lod])

lemma slice_open_lod: "selects (slice_open S) (proj (slice_lod S)\<cdot>k) \<longleftrightarrow> selects (slice_open S) k"
  by (simp add: kholds_def kval_reads[OF reads_in_slice_lod])

lemma compact_slice_lod: "compact (slice_lod S)"
  unfolding slice_lod_def by (rule lattice_lub_compact) (auto simp: compact_lod)

lemma slice_coarsen_union: "slice_coarsen A (S |\<union>| T) = slice_coarsen A S |\<union>| slice_coarsen A T"
  by (subst fset_inject[symmetric]) (auto simp: fset_slice_coarsen)

lemma slice_coarsen_inside: "slice_lod S \<sqsubseteq> A \<Longrightarrow> slice_coarsen A S = S"
proof (subst fset_inject[symmetric])
  assume A: "slice_lod S \<sqsubseteq> A"
  have "crs A e = Some e" if "e |\<in>| S" for e
    by (rule crs_inside[OF reads_in_mono[OF reads_in_slice_lod[OF that] A]])
  then show "fset (slice_coarsen A S) = fset S" by (auto simp: fset_slice_coarsen)
qed

lemma slice_lod_coarsen: "slice_lod (slice_coarsen A S) \<sqsubseteq> slice_lod S \<sqinter> A"
  unfolding slice_lod_def
proof (rule lattice_lub_least, rule is_ubI)
  fix x assume "x \<in> (\<lambda>e. lod (kdims e)) ` fset (slice_coarsen A S)"
  then obtain e e' where e: "e |\<in>| S" and c: "crs A e = Some e'" and x: "x = lod (kdims e')"
    by (auto simp: fset_slice_coarsen)
  have r: "reads_in A e'" and sub: "set (kdims e') \<subseteq> set (kdims e)" using crs_reads[OF c] by simp_all
  have "x \<sqsubseteq> lod (kdims e)" unfolding x lod_below_iff using sub lod_below_iff[of "kdims e" "lod (kdims e)"] by auto
  then have "x \<sqsubseteq> lub ((\<lambda>e. lod (kdims e)) ` fset S)"
    using lod_below_slice_lod[OF e] unfolding slice_lod_def by (rule below_trans)
  moreover have "x \<sqsubseteq> A" unfolding x lod_below_iff using r by (simp add: reads_in_def)
  ultimately show "x \<sqsubseteq> lub ((\<lambda>e. lod (kdims e)) ` fset S) \<sqinter> A" by (rule lattice_meet_greatest)
qed

lemma slice_coarsen_cut:
  "selects (slice_open S) k \<Longrightarrow> selects (slice_open (slice_coarsen A S)) (proj A\<cdot>k)"
proof (simp only: selects_slice_open fset_slice_coarsen, intro ballI)
  fix e' assume S: "\<forall>e\<in>fset S. kholds e k" and "e' \<in> {e'. \<exists>e\<in>fset S. crs A e = Some e'}"
  then obtain e where e: "e |\<in>| S" and c: "crs A e = Some e'" by auto
  have "kholds e' k" using S e crs_weakens[OF c, of k] by (simp add: kholds_def)
  then show "kholds e' (proj A\<cdot>k)" using crs_reads[OF c] by (simp add: kholds_def kval_reads)
qed

lemma slice_coarsen_slod: "slice_coarsen A S = slice_coarsen (A \<sqinter> slice_lod S) S"
proof (subst fset_inject[symmetric])
  have "crs (A \<sqinter> slice_lod S) e = crs A e" if "e |\<in>| S" for e
    using crs_bind[of "slice_lod S" e A] crs_inside[OF reads_in_slice_lod[OF that]] by simp
  then show "fset (slice_coarsen A S) = fset (slice_coarsen (A \<sqinter> slice_lod S) S)"
    by (auto simp: fset_slice_coarsen)
qed

lemma slice_coarsen_coarsen: "slice_coarsen A (slice_coarsen B S) = slice_coarsen (A \<sqinter> B) S"
proof (subst fset_inject[symmetric])
  have "crs (A \<sqinter> B) e = Some e'' \<longleftrightarrow> (\<exists>e'. crs B e = Some e' \<and> crs A e' = Some e'')" for e e''
    by (simp only: crs_bind[symmetric] bind_eq_Some_conv)
  then show "fset (slice_coarsen A (slice_coarsen B S)) = fset (slice_coarsen (A \<sqinter> B) S)"
    unfolding fset_slice_coarsen by blast
qed

end

subsection \<open>Pins\<close>

text \<open>Scalars are flat, so a defined scalar is maximal; so are \<open>NA\<close> and a key value
  \<open>Val\<cdot>s\<close> for a defined scalar \<open>s\<close>.  The upsets of key values are therefore exactly what the
  three tests select.\<close>

lemma scalar_maximal: "s \<noteq> \<bottom> \<Longrightarrow> s \<sqsubseteq> x \<Longrightarrow> x = (s :: scalar)"
  by (cases s; cases x) (auto simp: flat_below_iff)

lemma truth_d_is_na: "truth_d\<cdot>(d_is_na\<cdot>(key_datum\<cdot>w)) = is_na\<cdot>w"
  by (cases w) (simp_all add: d_is_na_def)

lemma truth_d_eq_key:
  assumes "s \<noteq> \<bottom>"
  shows "truth_d\<cdot>(d_eq\<cdot>(key_datum\<cdot>w)\<cdot>(key_datum\<cdot>(Val\<cdot>s))) = TT \<longleftrightarrow> w = Val\<cdot>s"
proof -
  have strict: "(\<Lambda> x y. SBool\<cdot>(scalar_eq\<cdot>x\<cdot>y))\<cdot>\<bottom>\<cdot>y = \<bottom>" "(\<Lambda> x y. SBool\<cdot>(scalar_eq\<cdot>x\<cdot>y))\<cdot>x\<cdot>\<bottom> = \<bottom>" for x y
    by simp_all
  have "truth_d\<cdot>(d_eq\<cdot>a\<cdot>b) = scalar_eq\<cdot>(plain\<cdot>a)\<cdot>(plain\<cdot>b)" for a b
    unfolding d_eq_def truth_d_def by (simp add: plain_dlift2[OF strict])
  moreover have "scalar_eq\<cdot>(plain\<cdot>(key_datum\<cdot>w))\<cdot>s = TT \<longleftrightarrow> w = Val\<cdot>s"
  proof (cases w)
    case (Val x)
    then show ?thesis using assms by (cases "x = \<bottom>") (simp_all add: scalar_eq_defined TT_def)
  qed simp_all
  ultimately show ?thesis by simp
qed

context key_language
begin

lemma kholds_pin_test:
  "(\<forall>e\<in>set (pin_test K d). kholds e k) \<longleftrightarrow> dim_val d\<cdot>K \<sqsubseteq> dim_val d\<cdot>k"
proof -
  let ?v = "dim_val d\<cdot>K" and ?w = "dim_val d\<cdot>k"
  show ?thesis
  proof (cases ?v)
    case bottom
    then show ?thesis by (simp add: pin_test_def)
  next
    case NA
    have "is_na\<cdot>?w = TT \<longleftrightarrow> ?w = NA" by (cases ?w) simp_all
    moreover have "NA \<sqsubseteq> ?w \<longleftrightarrow> ?w = NA" by (cases ?w) simp_all
    ultimately show ?thesis using NA by (simp add: pin_test_def kholds_def truth_d_is_na)
  next
    case (Val s)
    show ?thesis
    proof (cases "s = \<bottom>")
      case True
      have "neg\<cdot>(is_na\<cdot>?w) = TT \<longleftrightarrow> Val\<cdot>\<bottom> \<sqsubseteq> ?w" by (cases ?w) simp_all
      then show ?thesis using Val True
        by (simp add: pin_test_def kholds_def truth_d_is_na truth_d_not[simplified])
    next
      case False
      have "Val\<cdot>s \<sqsubseteq> ?w \<longleftrightarrow> ?w = Val\<cdot>s"
        by (cases ?w) (auto dest: scalar_maximal[OF False])
      then show ?thesis using Val False
        by (simp add: pin_test_def kholds_def truth_d_eq_key[OF False, simplified])
    qed
  qed
qed

lemma selects_slice_pin:
  "compact K \<Longrightarrow> selects (slice_open (slice_pin K :: ('d, 'c, 'fn, 'ag) slice)) k \<longleftrightarrow> K \<sqsubseteq> k"
proof
  assume K: "compact K" and "selects (slice_open (slice_pin K :: ('d, 'c, 'fn, 'ag) slice)) k"
  then have "\<forall>d\<in>set (key_dims K). \<forall>e\<in>set (pin_test K d :: ('d, 'c, 'fn, 'ag) ast list). kholds e k"
    by (simp add: slice_pin_def fset_of_list.rep_eq)
  then show "K \<sqsubseteq> k" by (intro key_dims_below[OF K]) (simp add: kholds_pin_test)
next
  assume "K \<sqsubseteq> k"
  then have "dim_val d\<cdot>K \<sqsubseteq> dim_val d\<cdot>k" for d by (rule monofun_cfun_arg)
  then have "\<forall>e\<in>set (pin_test K d :: ('d, 'c, 'fn, 'ag) ast list). kholds e k" for d
    by (simp only: kholds_pin_test)
  then show "selects (slice_open (slice_pin K :: ('d, 'c, 'fn, 'ag) slice)) k"
    by (auto simp: slice_pin_def fset_of_list.rep_eq)
qed

theorem slicer_ast_slicing: "slicer (ast_slicing :: (('d, 'c, 'fn, 'ag) slice, 'k) slicer_ops)"
  by unfold_locales
    (simp_all del: selects_slice_open add: ast_slicing_def funion_ac lattice_join_ac slice_lod_union slice_lod_empty slice_open_union
      slice_open_empty slice_open_lod compact_slice_lod slice_coarsen_union slice_coarsen_inside
      slice_lod_coarsen slice_coarsen_cut slice_coarsen_slod[symmetric] slice_coarsen_coarsen selects_slice_pin)

end

end
