theory Bag_Join
  imports "HOLCF-extra.BagPD" LOD
begin

default_sort bifinite

section \<open>Outer joins of bags\<close>

text \<open>A binary outer join of two bags of rows. The sides keep their own row types; a pair of
  rows is combined by a monotone @{text c} (the pair, or the join of two disjoint blocks of a
  universal row), and an orphan is combined with bottom. Rows meet through key maps into a
  common key order: a pair is a \emph{decided match} when the keys are equal and live, which
  makes them maximal. Other keys never match: partial keys, and maximal keys that are not live
  such as a decided NULL, which pass through as orphans.

  A decided match of @{text "n\<cdot>x"} and @{text "m\<cdot>y"} gives @{text "n m"} joined rows. Besides,
  each row @{text x} of multiplicity @{text n} keeps @{text "n N(x)"} orphan copies, where
  @{text "N(x)"} bounds the partners that refinements can still bring:
  \<^item> @{text \<infinity>} on an @{text Open} side (the 1-side of an N:1 join: more referencing rows may join);
  \<^item> on a @{text Closed} side with a decided match, the undecided partner mass compatible with
    its key;
  \<^item> on a @{text Closed} side without a decided match, the largest partner mass that a live key
    above its key can collect, and at least one copy.
  Refinement only merges rows, so partner masses only shrink and the join is monotone in both
  arguments. No deduplication is involved: duplicate rows simply multiply.\<close>

subsection \<open>Sides and indices\<close>

datatype join_side = Open | Closed

text \<open>The rows of a join on the basis are indexed by joined pairs and by the orphans of either
  side.\<close>

datatype ('a, 'b) join_index =
    Joined "'a compact_basis" "'b compact_basis"
  | Left_Orphan "'a compact_basis"
  | Right_Orphan "'b compact_basis"

definition join_indices :: "'a bag_basis \<Rightarrow> 'b bag_basis \<Rightarrow> ('a, 'b) join_index set"
  where "join_indices t u =
    case_prod Joined ` (bsupp t \<times> bsupp u) \<union> (Left_Orphan ` bsupp t \<union> Right_Orphan ` bsupp u)"

lemma join_indices_iff [simp]:
  "Joined x y \<in> join_indices t u \<longleftrightarrow> x \<in> bsupp t \<and> y \<in> bsupp u"
  "Left_Orphan x \<in> join_indices t u \<longleftrightarrow> x \<in> bsupp t"
  "Right_Orphan y \<in> join_indices t u \<longleftrightarrow> y \<in> bsupp u"
  by (auto simp: join_indices_def)

lemma finite_join_indices [simp]: "finite (join_indices t u)"
  by (simp add: join_indices_def)

lemma sum_join_indices:
  "sum g (join_indices t u) = (\<Sum>x\<in>bsupp t. \<Sum>y\<in>bsupp u. g (Joined x y)) +
    ((\<Sum>x\<in>bsupp t. g (Left_Orphan x)) + (\<Sum>y\<in>bsupp u. g (Right_Orphan y)))"
proof -
  have "sum g (join_indices t u) = sum g (case_prod Joined ` (bsupp t \<times> bsupp u)) +
      (sum g (Left_Orphan ` bsupp t) + sum g (Right_Orphan ` bsupp u))"
    unfolding join_indices_def by (subst sum.union_disjoint; auto)+
  then show ?thesis
    by (simp add: sum.reindex inj_on_def sum.cartesian_product prod.case_distrib)
qed

primrec join_label ::
    "('a compact_basis \<Rightarrow> 'b compact_basis \<Rightarrow> 'c compact_basis) \<Rightarrow> ('a, 'b) join_index \<Rightarrow> 'c compact_basis"
  where
    "join_label c (Joined x y) = c x y"
  | "join_label c (Left_Orphan x) = c x compact_bot"
  | "join_label c (Right_Orphan y) = c compact_bot y"

primrec join_swap :: "('a, 'b) join_index \<Rightarrow> ('b, 'a) join_index"
  where
    "join_swap (Joined x y) = Joined y x"
  | "join_swap (Left_Orphan x) = Right_Orphan x"
  | "join_swap (Right_Orphan y) = Left_Orphan y"

lemma join_swap_swap [simp]: "join_swap (join_swap i) = i"
  by (cases i) simp_all

lemma join_swap_indices: "i \<in> join_indices t u \<Longrightarrow> join_swap i \<in> join_indices u t"
  by (cases i) simp_all

text \<open>Joined rows as pairs, and keys of basis elements.\<close>

definition pair_basis :: "'a compact_basis \<Rightarrow> 'b compact_basis \<Rightarrow> ('a \<times> 'b) compact_basis"
  where "pair_basis x y = Abs_compact_basis (Rep_compact_basis x, Rep_compact_basis y)"

lemma Rep_pair_basis [simp]:
  "Rep_compact_basis (pair_basis x y) = (Rep_compact_basis x, Rep_compact_basis y)"
  by (simp add: pair_basis_def)

lemma pair_basis_mono:
  assumes "x \<sqsubseteq> x'" and "y \<sqsubseteq> y'"
  shows "pair_basis x y \<sqsubseteq> pair_basis x' y'"
proof (rule compact_below_iff [THEN iffD2])
  show "Rep_compact_basis (pair_basis x y) \<sqsubseteq> Rep_compact_basis (pair_basis x' y')"
    using assms [THEN compact_below_iff [THEN iffD1]] by (simp only: Rep_pair_basis Pair_below_iff)
qed

abbreviation on_basis :: "('a \<rightarrow> 'k::cpo) \<Rightarrow> 'a compact_basis \<Rightarrow> 'k"
  where "on_basis f x \<equiv> f\<cdot>(Rep_compact_basis x)"

lemma monofun_on_basis: "monofun (on_basis f)"
  by (rule monofunI, rule monofun_cfun_arg, erule compact_below_iff [THEN iffD1])

subsection \<open>Partner masses\<close>

text \<open>Keys range over @{text Keys}; the live keys are maximal there.\<close>

locale bag_join_keys =
  fixes Live Keys :: "'k::cpo set"
  assumes live_maximal: "k \<in> Live \<Longrightarrow> k \<sqsubseteq> k' \<Longrightarrow> k' \<in> Keys \<Longrightarrow> k' = k"
begin

definition decided_match :: "'k \<Rightarrow> 'k \<Rightarrow> bool"
  where "decided_match k k' \<longleftrightarrow> k \<in> Live \<and> k' = k"

lemma decided_match_sym: "decided_match k k' \<longleftrightarrow> decided_match k' k"
  by (auto simp: decided_match_def)

text \<open>For a row with key @{text k} against the bag @{text u} on the other side, whose rows have
  keys @{text key}: the decided partner mass, the undecided partner mass below @{text k}, and
  the largest mass that a live key above @{text k} can collect.\<close>

definition decided_mass :: "('b compact_basis \<Rightarrow> 'k) \<Rightarrow> 'b bag_basis \<Rightarrow> 'k \<Rightarrow> enat"
  where "decided_mass key u k = bag_mass u (\<lambda>y. decided_match k (key y))"

definition undecided_mass :: "('b compact_basis \<Rightarrow> 'k) \<Rightarrow> 'b bag_basis \<Rightarrow> 'k \<Rightarrow> enat"
  where "undecided_mass key u k = bag_mass u (\<lambda>y. key y \<sqsubseteq> k \<and> key y \<noteq> k)"

definition reachable_mass :: "('b compact_basis \<Rightarrow> 'k) \<Rightarrow> 'b bag_basis \<Rightarrow> 'k \<Rightarrow> enat"
  where "reachable_mass key u k = (SUP k'\<in>{k'\<in>Live. k \<sqsubseteq> k'}. bag_mass u (\<lambda>y. key y \<sqsubseteq> k'))"

fun orphan_count :: "join_side \<Rightarrow> ('b compact_basis \<Rightarrow> 'k) \<Rightarrow> 'b bag_basis \<Rightarrow> 'k \<Rightarrow> enat"
  where
    "orphan_count Open key u k = \<infinity>"
  | "orphan_count Closed key u k =
      (if decided_mass key u k = 0 then max 1 (reachable_mass key u k) else undecided_mass key u k)"

lemma decided_mass_live: "decided_mass key u k \<noteq> 0 \<Longrightarrow> k \<in> Live"
  by (auto simp: decided_mass_def bag_mass_nonzero_iff decided_match_def)

lemma orphan_count_0: "orphan_count w key u k = 0 \<Longrightarrow> w = Closed \<and> decided_mass key u k \<noteq> 0"
  by (cases w) (auto simp: max_def split: if_split_asm)

lemma decided_undecided_mass:
  "k \<in> Live \<Longrightarrow> decided_mass key u k + undecided_mass key u k = bag_mass u (\<lambda>y. key y \<sqsubseteq> k)"
  unfolding decided_mass_def undecided_mass_def
  by (subst bag_mass_disj[symmetric]) (auto simp: decided_match_def intro: bag_mass_cong)

lemma reachable_mass_upper:
  "k' \<in> Live \<Longrightarrow> k \<sqsubseteq> k' \<Longrightarrow> bag_mass u (\<lambda>y. key y \<sqsubseteq> k') \<le> reachable_mass key u k"
  unfolding reachable_mass_def by (rule SUP_upper) simp

lemma reachable_mass_key_anti: "k \<sqsubseteq> k1 \<Longrightarrow> reachable_mass key u k1 \<le> reachable_mass key u k"
  unfolding reachable_mass_def by (rule SUP_subset_mono) (auto intro: below_trans)

text \<open>A row without a decided match holds enough copies for whatever a row above it emits.\<close>

lemma orphan_count_step:
  assumes "k \<sqsubseteq> k1" and "decided_mass key u k = 0"
  shows "decided_mass key u k1 + orphan_count w key u k1 \<le> orphan_count w key u k"
proof (cases w)
  case Open
  then show ?thesis
    by simp
next
  case Closed
  show ?thesis
  proof (cases "decided_mass key u k1 = 0")
    case True
    have "max 1 (reachable_mass key u k1) \<le> max 1 (reachable_mass key u k)"
      using reachable_mass_key_anti[OF assms(1)] by (rule max.mono[OF order_refl])
    then show ?thesis
      using Closed True assms(2) by simp
  next
    case nz: False
    then have live: "k1 \<in> Live"
      by (rule decided_mass_live)
    have "decided_mass key u k1 + orphan_count w key u k1 = bag_mass u (\<lambda>y. key y \<sqsubseteq> k1)"
      using Closed nz decided_undecided_mass[OF live] by simp
    also have "\<dots> \<le> reachable_mass key u k"
      by (rule reachable_mass_upper[OF live assms(1)])
    also have "\<dots> \<le> orphan_count w key u k"
      using Closed assms(2) by simp
    finally show ?thesis .
  qed
qed

text \<open>Refining the other side only lowers the counts.\<close>

lemma decided_mass_up:
  assumes "t \<le>\<^sub>b t'" and "monofun key" and keys: "\<And>x. key x \<in> Keys"
    and "decided_mass key t k \<noteq> 0"
  shows "decided_mass key t' k \<noteq> 0"
proof -
  obtain x where x: "x \<in> bsupp t" "decided_match k (key x)"
    using assms(4) by (auto simp: decided_mass_def bag_mass_nonzero_iff)
  obtain x' where "x' \<in> bsupp t'" "x \<sqsubseteq> x'"
    using bag_le_lower[OF assms(1) x(1)] by blast
  moreover have "decided_match k (key x')"
    using x(2) monofunE[OF assms(2) \<open>x \<sqsubseteq> x'\<close>] live_maximal keys by (auto simp: decided_match_def)
  ultimately show ?thesis
    by (auto simp: decided_mass_def bag_mass_nonzero_iff)
qed

lemma undecided_mass_anti:
  assumes "t \<le>\<^sub>b t'" and "monofun key" and keys: "\<And>x. key x \<in> Keys" and "k \<in> Live"
  shows "undecided_mass key t' k \<le> undecided_mass key t k"
  unfolding undecided_mass_def
proof (rule bag_le_mass[OF assms(1)])
  fix x x'
  assume "x \<sqsubseteq> x'" and x': "key x' \<sqsubseteq> k \<and> key x' \<noteq> k"
  have "key x \<sqsubseteq> key x'"
    using assms(2) \<open>x \<sqsubseteq> x'\<close> by (rule monofunE)
  show "key x \<sqsubseteq> k \<and> key x \<noteq> k"
  proof
    show "key x \<sqsubseteq> k"
      using \<open>key x \<sqsubseteq> key x'\<close> x' by (blast intro: below_trans)
    show "key x \<noteq> k"
      using \<open>key x \<sqsubseteq> key x'\<close> x' live_maximal[OF assms(4)] keys by blast
  qed
qed

lemma reachable_mass_anti:
  assumes "t \<le>\<^sub>b t'" and "monofun key"
  shows "reachable_mass key t' k \<le> reachable_mass key t k"
  unfolding reachable_mass_def
  by (rule SUP_subset_mono[OF order_refl], rule bag_le_mass[OF assms(1)])
    (metis assms(2) monofunE below_trans)

lemma orphan_count_anti:
  assumes "t \<le>\<^sub>b t'" and "monofun key" and "\<And>x. key x \<in> Keys"
  shows "orphan_count w key t' k \<le> orphan_count w key t k"
proof (cases w)
  case Open
  then show ?thesis
    by simp
next
  case Closed
  show ?thesis
  proof (cases "decided_mass key t k = 0")
    case nz: False
    then show ?thesis
      using Closed undecided_mass_anti[OF assms decided_mass_live[OF nz]] decided_mass_up[OF assms nz]
      by simp
  next
    case True
    show ?thesis
    proof (cases "decided_mass key t' k = 0")
      case True
      have "max 1 (reachable_mass key t' k) \<le> max 1 (reachable_mass key t k)"
        using reachable_mass_anti[OF assms(1,2)] by (rule max.mono[OF order_refl])
      then show ?thesis
        using Closed True \<open>decided_mass key t k = 0\<close> by simp
    next
      case nz: False
      then have live: "k \<in> Live"
        by (rule decided_mass_live)
      have "undecided_mass key t' k \<le> undecided_mass key t k"
        by (rule undecided_mass_anti[OF assms live])
      also have "\<dots> \<le> bag_mass t (\<lambda>x. key x \<sqsubseteq> k)"
        using decided_undecided_mass[OF live, of key t] by (metis le_iff_add add.commute)
      also have "\<dots> \<le> reachable_mass key t k"
        by (rule reachable_mass_upper[OF live below_refl])
      also have "\<dots> \<le> max 1 (reachable_mass key t k)"
        by simp
      finally show ?thesis
        using Closed nz True by simp
    qed
  qed
qed

subsection \<open>The join on the basis\<close>

primrec join_mult ::
    "join_side \<Rightarrow> join_side \<Rightarrow> ('a compact_basis \<Rightarrow> 'k) \<Rightarrow> ('b compact_basis \<Rightarrow> 'k) \<Rightarrow>
      'a bag_basis \<Rightarrow> 'b bag_basis \<Rightarrow> ('a, 'b) join_index \<Rightarrow> enat"
  where
    "join_mult wl wr lkey rkey t u (Joined x y) =
      (if decided_match (lkey x) (rkey y) then bmult t x * bmult u y else 0)"
  | "join_mult wl wr lkey rkey t u (Left_Orphan x) = bmult t x * orphan_count wl rkey u (lkey x)"
  | "join_mult wl wr lkey rkey t u (Right_Orphan y) = bmult u y * orphan_count wr lkey t (rkey y)"

lemma join_mult_nonzero: "\<exists>i\<in>join_indices t u. join_mult wl wr lkey rkey t u i \<noteq> 0"
proof -
  obtain x where x: "x \<in> bsupp t"
    using bsupp_nonempty by blast
  show ?thesis
  proof (cases "orphan_count wl rkey u (lkey x) = 0")
    case True
    then obtain y where "y \<in> bsupp u" "decided_match (lkey x) (rkey y)"
      by (auto dest!: orphan_count_0 simp: decided_mass_def bag_mass_nonzero_iff)
    then show ?thesis
      using x by (intro bexI[of _ "Joined x y"]) (simp_all add: bsupp_iff)
  next
    case False
    then show ?thesis
      using x by (intro bexI[of _ "Left_Orphan x"]) (simp_all add: bsupp_iff)
  qed
qed

definition BJoin ::
    "('a compact_basis \<Rightarrow> 'b compact_basis \<Rightarrow> 'c compact_basis) \<Rightarrow>
      join_side \<Rightarrow> join_side \<Rightarrow> ('a compact_basis \<Rightarrow> 'k) \<Rightarrow> ('b compact_basis \<Rightarrow> 'k) \<Rightarrow>
      'a bag_basis \<Rightarrow> 'b bag_basis \<Rightarrow> 'c bag_basis"
  where "BJoin c wl wr lkey rkey t u =
    BFamily (join_indices t u) (join_label c) (join_mult wl wr lkey rkey t u)"

text \<open>The join is symmetric up to swapping the sides.\<close>

lemma BJoin_swap: "BJoin c wl wr lkey rkey t u = BJoin (\<lambda>y x. c x y) wr wl rkey lkey u t"
proof -
  have bij: "bij_betw join_swap (join_indices t u) (join_indices u t)"
    by (rule bij_betw_byWitness[where f' = join_swap]) (auto intro: join_swap_indices)
  have "join_label (\<lambda>y x. c x y) (join_swap i) = join_label c i" for i
    by (cases i) simp_all
  moreover have "join_mult wr wl rkey lkey u t (join_swap i) = join_mult wl wr lkey rkey t u i" for i
    by (cases i) (simp_all add: decided_match_sym mult.commute)
  ultimately show ?thesis
    unfolding BJoin_def
    using BFamily_reindex[OF bij, of "join_label (\<lambda>y x. c x y)" "join_mult wr wl rkey lkey u t"]
    by simp
qed

subsection \<open>Monotonicity\<close>

text \<open>A plan @{text P} from @{text t} to @{text t'} lifts to the joins with @{text u}. A pair
  follows its left row. A left orphan without a decided match sends copies to the pairs that its
  refined row now matches, and the rest to the refined orphan. Right orphans stay where they
  are.\<close>

context
  fixes P :: "'a compact_basis \<Rightarrow> 'a compact_basis \<Rightarrow> enat"
    and wl wr :: join_side
    and lkey :: "'a compact_basis \<Rightarrow> 'k" and rkey :: "'b compact_basis \<Rightarrow> 'k"
    and t' :: "'a bag_basis" and u :: "'b bag_basis"
begin

fun lift_plan :: "('a, 'b) join_index \<Rightarrow> ('a, 'b) join_index \<Rightarrow> enat"
  where
    "lift_plan (Joined x y) (Joined x' y') =
      (if y' = y then if decided_match (lkey x) (rkey y) then P x x' * bmult u y else 0 else 0)"
  | "lift_plan (Left_Orphan x) (Joined x' y) =
      (if decided_mass rkey u (lkey x) = 0 \<and> decided_match (lkey x') (rkey y)
       then P x x' * bmult u y else 0)"
  | "lift_plan (Left_Orphan x) (Left_Orphan x') =
      P x x' * orphan_count wl rkey u (lkey x')"
  | "lift_plan (Right_Orphan y) (Right_Orphan y') =
      (if y' = y then bmult u y * orphan_count wr lkey t' (rkey y) else 0)"
  | "lift_plan i j = 0"

end

lemma BJoin_mono_left:
  assumes tt: "t \<le>\<^sub>b t'" and lkey: "monofun lkey" and keys: "\<And>x. lkey x \<in> Keys"
    and c: "\<And>x x' y y'. x \<sqsubseteq> x' \<Longrightarrow> y \<sqsubseteq> y' \<Longrightarrow> c x y \<sqsubseteq> c x' y'"
  shows "BJoin c wl wr lkey rkey t u \<le>\<^sub>b BJoin c wl wr lkey rkey t' u"
proof -
  obtain P where P: "bag_plan t t' P"
    using tt unfolding bag_le_def by blast
  have Pkey: "lkey x \<sqsubseteq> lkey x'" if "P x x' \<noteq> 0" for x x'
    using lkey bag_plan_below[OF P that] by (rule monofunE)
  \<comment> \<open>a decided key does not move\<close>
  have Pfix: "lkey x' = lkey x" if "P x x' \<noteq> 0" "decided_mass rkey u (lkey x) \<noteq> 0" for x x'
    using live_maximal decided_mass_live[OF that(2)] Pkey[OF that(1)] keys by blast
  let ?m = "join_mult wl wr lkey rkey t u" and ?n = "join_mult wl wr lkey rkey t' u"
  let ?p = "lift_plan P wl wr lkey rkey t' u"
  have sum_decided_mass:
    "(\<Sum>y\<in>bsupp u. if decided_match k (rkey y) then e * bmult u y else 0) = e * decided_mass rkey u k"
    for k e
    by (simp add: sum.inter_filter[symmetric] decided_mass_def bag_mass_def sum_distrib_left if_distrib)
  show ?thesis
    unfolding BJoin_def
  proof (rule BFamily_le[where p = ?p])
    show "\<exists>i\<in>join_indices t u. ?m i \<noteq> 0"
      by (rule join_mult_nonzero)
  next
    fix i j
    assume "i \<in> join_indices t u" "j \<in> join_indices t' u" "?p i j \<noteq> 0"
    then show "join_label c i \<sqsubseteq> join_label c j"
      by (cases i; cases j) (auto split: if_split_asm intro!: c dest: bag_plan_below[OF P])
  next
    fix i
    assume i: "i \<in> join_indices t u"
    show "sum (?p i) (join_indices t' u) \<le> ?m i"
    proof (cases i)
      case (Joined x y)
      then have y: "y \<in> bsupp u"
        using i by simp
      have "sum (?p i) (join_indices t' u) =
          (if decided_match (lkey x) (rkey y) then sum (P x) (bsupp t') * bmult u y else 0)"
        using y by (simp add: Joined sum_join_indices sum_distrib_right)
      then show ?thesis
        by (simp add: Joined bag_plan_row[OF P])
    next
      case (Left_Orphan x)
      have bound: "(\<Sum>y\<in>bsupp u. ?p i (Joined x' y)) + ?p i (Left_Orphan x')
          \<le> P x x' * orphan_count wl rkey u (lkey x)" for x'
      proof (cases "P x x' = 0")
        case False
        show ?thesis
        proof (cases "decided_mass rkey u (lkey x) = 0")
          case True
          have "P x x' * decided_mass rkey u (lkey x') + P x x' * orphan_count wl rkey u (lkey x')
              \<le> P x x' * orphan_count wl rkey u (lkey x)"
            using orphan_count_step[OF Pkey[OF False] True]
            by (simp add: distrib_left[symmetric] mult_left_mono)
          then show ?thesis
            using True by (simp add: Left_Orphan sum_decided_mass mult.commute)
        next
          case nz: False
          then show ?thesis
            using Pfix[OF False nz] by (simp add: Left_Orphan)
        qed
      qed (simp add: Left_Orphan)
      have "sum (?p i) (join_indices t' u) =
          (\<Sum>x'\<in>bsupp t'. (\<Sum>y\<in>bsupp u. ?p i (Joined x' y)) + ?p i (Left_Orphan x'))"
        by (simp add: Left_Orphan sum_join_indices sum.distrib)
      also have "\<dots> \<le> (\<Sum>x'\<in>bsupp t'. P x x' * orphan_count wl rkey u (lkey x))"
        by (intro sum_mono bound)
      also have "\<dots> = ?m i"
        by (simp add: Left_Orphan sum_distrib_right[symmetric] bag_plan_row[OF P])
      finally show ?thesis .
    next
      case (Right_Orphan y)
      then have y: "y \<in> bsupp u"
        using i by simp
      have "sum (?p i) (join_indices t' u) = bmult u y * orphan_count wr lkey t' (rkey y)"
        using y by (simp add: Right_Orphan sum_join_indices)
      also have "\<dots> \<le> ?m i"
        using orphan_count_anti[OF tt lkey keys] by (simp add: Right_Orphan mult_left_mono)
      finally show ?thesis .
    qed
  next
    fix j
    assume j: "j \<in> join_indices t' u"
    show "?n j \<le> (\<Sum>i\<in>join_indices t u. ?p i j)"
    proof (cases j)
      case (Joined x' y)
      then have y: "y \<in> bsupp u"
        using j by simp
      show ?thesis
      proof (cases "decided_match (lkey x') (rkey y)")
        case True
        have cover: "P x x' * bmult u y \<le> (\<Sum>y'\<in>bsupp u. ?p (Joined x y') j) + ?p (Left_Orphan x) j"
          for x
        proof (cases "P x x' = 0 \<or> decided_mass rkey u (lkey x) = 0")
          case False
          then have "decided_match (lkey x) (rkey y)"
            using True Pfix by auto
          then show ?thesis
            using y by (simp add: Joined)
        qed (auto simp: Joined True)
        have "?n j \<le> (\<Sum>x\<in>bsupp t. P x x') * bmult u y"
          using True bag_plan_col[OF P, of x'] by (simp add: Joined mult_right_mono)
        also have "\<dots> \<le> (\<Sum>x\<in>bsupp t. (\<Sum>y'\<in>bsupp u. ?p (Joined x y') j) + ?p (Left_Orphan x) j)"
          unfolding sum_distrib_right by (intro sum_mono cover)
        also have "\<dots> = (\<Sum>i\<in>join_indices t u. ?p i j)"
          by (simp add: Joined sum_join_indices sum.distrib)
        finally show ?thesis .
      qed (simp add: Joined)
    next
      case (Left_Orphan x')
      have "?n j \<le> (\<Sum>x\<in>bsupp t. P x x') * orphan_count wl rkey u (lkey x')"
        using bag_plan_col[OF P, of x'] by (simp add: Left_Orphan mult_right_mono)
      also have "\<dots> = (\<Sum>i\<in>join_indices t u. ?p i j)"
        by (simp add: Left_Orphan sum_join_indices sum_distrib_right)
      finally show ?thesis .
    next
      case (Right_Orphan y)
      then have "y \<in> bsupp u"
        using j by simp
      then show ?thesis
        by (simp add: Right_Orphan sum_join_indices)
    qed
  next
    fix i
    assume i: "i \<in> join_indices t u" and "?m i \<noteq> 0"
    show "\<exists>j\<in>join_indices t' u. ?n j \<noteq> 0 \<and> join_label c i \<sqsubseteq> join_label c j"
    proof (cases i)
      case (Joined x y)
      with i \<open>?m i \<noteq> 0\<close> have x: "x \<in> bsupp t" and y: "y \<in> bsupp u"
        and d: "decided_match (lkey x) (rkey y)"
        by (simp_all split: if_split_asm)
      obtain x' where x': "x' \<in> bsupp t'" "P x x' \<noteq> 0"
        using bag_plan_row_ex[OF P x] .
      have "decided_mass rkey u (lkey x) \<noteq> 0"
        using y d by (auto simp: decided_mass_def bag_mass_nonzero_iff)
      then have "decided_match (lkey x') (rkey y)"
        using d Pfix[OF x'(2)] by simp
      then show ?thesis
        using x' y bag_plan_below[OF P x'(2)]
        by (intro bexI[of _ "Joined x' y"]) (auto simp: Joined bsupp_iff intro: c)
    next
      case (Left_Orphan x)
      with i have x: "x \<in> bsupp t"
        by simp
      obtain x' where x': "x' \<in> bsupp t'" "P x x' \<noteq> 0"
        using bag_plan_row_ex[OF P x] .
      note xx' = bag_plan_below[OF P x'(2)]
      show ?thesis
      proof (cases "orphan_count wl rkey u (lkey x') = 0")
        case True
        then obtain y where "y \<in> bsupp u" "decided_match (lkey x') (rkey y)"
          by (auto dest!: orphan_count_0 simp: decided_mass_def bag_mass_nonzero_iff)
        then show ?thesis
          using x' xx' by (intro bexI[of _ "Joined x' y"]) (auto simp: Left_Orphan bsupp_iff intro: c)
      next
        case False
        then show ?thesis
          using x' xx' by (intro bexI[of _ "Left_Orphan x'"]) (auto simp: Left_Orphan bsupp_iff intro: c)
      qed
    next
      case (Right_Orphan y)
      with i have y: "y \<in> bsupp u"
        by simp
      show ?thesis
      proof (cases "orphan_count wr lkey t' (rkey y) = 0")
        case True
        then obtain x' where "x' \<in> bsupp t'" "decided_match (rkey y) (lkey x')"
          by (auto dest!: orphan_count_0 simp: decided_mass_def bag_mass_nonzero_iff)
        then show ?thesis
          using y
          by (intro bexI[of _ "Joined x' y"]) (auto simp: Right_Orphan bsupp_iff decided_match_sym intro: c)
      next
        case False
        then show ?thesis
          using y by (intro bexI[of _ "Right_Orphan y"]) (auto simp: Right_Orphan bsupp_iff)
      qed
    qed
  qed simp_all
qed

lemma BJoin_mono_right:
  assumes "u \<le>\<^sub>b u'" and "monofun rkey" and "\<And>y. rkey y \<in> Keys"
    and c: "\<And>x x' y y'. x \<sqsubseteq> x' \<Longrightarrow> y \<sqsubseteq> y' \<Longrightarrow> c x y \<sqsubseteq> c x' y'"
  shows "BJoin c wl wr lkey rkey t u \<le>\<^sub>b BJoin c wl wr lkey rkey t u'"
  unfolding BJoin_swap[of c wl wr lkey rkey t] by (rule BJoin_mono_left[OF assms(1-3)]) (rule c)

subsection \<open>The join of bags into pairs\<close>

definition bag_pair_join ::
    "join_side \<Rightarrow> join_side \<Rightarrow> ('a \<rightarrow> 'k) \<Rightarrow> ('b \<rightarrow> 'k) \<Rightarrow> 'a bag_pd \<rightarrow> 'b bag_pd \<rightarrow> ('a \<times> 'b) bag_pd"
  where "bag_pair_join wl wr lkey rkey = bag_pd.extension (\<lambda>t. bag_pd.extension (\<lambda>u.
    bag_principal (BJoin pair_basis wl wr (on_basis lkey) (on_basis rkey) t u)))"

lemma bag_pair_join_principal:
  assumes "\<And>x. lkey\<cdot>x \<in> Keys" and "\<And>y. rkey\<cdot>y \<in> Keys"
  shows "bag_pair_join wl wr lkey rkey\<cdot>(bag_principal t)\<cdot>(bag_principal u) =
    bag_principal (BJoin pair_basis wl wr (on_basis lkey) (on_basis rkey) t u)"
  unfolding bag_pair_join_def
  by (simp add: bag_pd.extension_principal bag_pd.extension_mono BJoin_mono_left BJoin_mono_right
      monofun_on_basis pair_basis_mono assms)

text \<open>Sanity check, an N:1 join of two rows with the same decided key: the referencing row is
  consumed by the match, while the referenced row keeps an open-ended number of orphan copies.\<close>

lemma bag_pair_join_unit_match:
  fixes lkey :: "'a \<rightarrow> 'k" and rkey :: "'b \<rightarrow> 'k"
  assumes a: "Cpo.compact a" and b: "Cpo.compact b" and live: "lkey\<cdot>a \<in> Live"
    and k: "rkey\<cdot>b = lkey\<cdot>a" and keys: "\<And>x. lkey\<cdot>x \<in> Keys" "\<And>y. rkey\<cdot>y \<in> Keys"
  shows "bag_pair_join Closed Open lkey rkey\<cdot>(bag_unit\<cdot>a)\<cdot>(bag_unit\<cdot>b) =
    bag_unit\<cdot>(a, b) \<union>\<^sub>b bag_omega\<cdot>(bag_unit\<cdot>(\<bottom>, b))"
proof -
  define a' b' where "a' = Abs_compact_basis a" and "b' = Abs_compact_basis b"
  have ra: "Rep_compact_basis a' = a" and rb: "Rep_compact_basis b' = b"
    using a b by (simp_all add: a'_def b'_def)
  have d: "decided_match (on_basis lkey a') (on_basis rkey b')"
    using live k by (simp add: ra rb decided_match_def)
  have l: "orphan_count Closed (on_basis rkey) (BUnit b') (on_basis lkey a') = 0"
    using d by (simp add: decided_mass_def undecided_mass_def bag_mass_BUnit ra rb k)
  have "BJoin pair_basis Closed Open (on_basis lkey) (on_basis rkey) (BUnit a') (BUnit b') =
      BPlus (BUnit (pair_basis a' b')) (BOmega (BUnit (pair_basis compact_bot b')))"
    by (rule bag_basis_eqI)
      (simp add: BJoin_def bmult_BFamily_sum join_mult_nonzero sum_join_indices d l bmult_BUnit
        bmult_BOmega eq_commute[of _ "pair_basis _ _"] del: orphan_count.simps(2))
  moreover have "bag_unit\<cdot>a = bag_principal (BUnit a')" "bag_unit\<cdot>b = bag_principal (BUnit b')"
    "bag_unit\<cdot>(a, b) = bag_principal (BUnit (pair_basis a' b'))"
    "bag_unit\<cdot>(\<bottom>::'a, b) = bag_principal (BUnit (pair_basis compact_bot b'))"
    using bag_unit_Rep_compact_basis [of a'] bag_unit_Rep_compact_basis [of b']
      bag_unit_Rep_compact_basis [of "pair_basis a' b'"]
      bag_unit_Rep_compact_basis [of "pair_basis (compact_bot::'a compact_basis) b'"]
    by (simp_all add: ra rb)
  ultimately show ?thesis
    by (simp only: bag_pair_join_principal[OF keys] bag_omega_principal bag_plus_principal)
qed

end

subsection \<open>Joins on one row domain\<close>

text \<open>Both sides live in one row domain @{typ 'r}, in disjoint blocks @{text A} and @{text B}. The
  left key columns @{text S} and the right key columns @{text T} are different columns, related by
  the transports @{text \<phi>} and @{text \<psi>} (the column correspondence of the join); the live keys are
  the maximal points of @{text T}. A joined pair is the join of its two blocks, which exists because
  the blocks are disjoint, so no compatibility condition on pairs is needed.\<close>

text \<open>The join of two continuous functions whose values are always joinable is continuous.\<close>

lemma cont_join_joinable:
  assumes f: "cont f" and g: "cont g" and j: "\<And>x. f x \<Up> g x"
  shows "cont (\<lambda>x. f x \<squnion> g x)"
proof (rule contI2)
  show "monofun (\<lambda>x. f x \<squnion> g x)"
  proof (rule monofunI)
    fix x y :: 'a
    assume "x \<sqsubseteq> y"
    then have "f x \<sqsubseteq> f y" "g x \<sqsubseteq> g y"
      using f g by (simp_all add: cont2monofunE)
    then show "f x \<squnion> g x \<sqsubseteq> f y \<squnion> g y"
      using joinableD[OF j[of y]] by (blast intro: join_belowI below_trans)
  qed
  fix Y :: "nat \<Rightarrow> 'a"
  assume Y: "chain Y" and ch: "chain (\<lambda>i. f (Y i) \<squnion> g (Y i))"
  have "f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f (Y i) \<squnion> g (Y i))"
    unfolding cont2contlubE[OF f Y] by (rule lub_mono[OF ch2ch_cont[OF f Y] ch joinableD(1)[OF j]])
  moreover have "g (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f (Y i) \<squnion> g (Y i))"
    unfolding cont2contlubE[OF g Y] by (rule lub_mono[OF ch2ch_cont[OF g Y] ch joinableD(2)[OF j]])
  ultimately show "f (\<Squnion>i. Y i) \<squnion> g (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f (Y i) \<squnion> g (Y i))"
    by (rule join_belowI)
qed

locale bag_join_columns =
  fixes A B S T :: "'r::{bifinite, distributive_cpo} semi_factor" and \<phi> \<psi> :: "'r \<rightarrow> 'r"
  assumes disjoint: "A \<sqinter> B = \<bottom>"
    and \<psi>\<phi>: "\<psi> oo \<phi> = proj S" and \<phi>\<psi>: "\<phi> oo \<psi> = proj T"
    and \<phi>_T: "proj T oo \<phi> = \<phi>" and \<psi>_S: "proj S oo \<psi> = \<psi>"
begin

lemma \<psi>\<phi>_app [simp]: "\<psi>\<cdot>(\<phi>\<cdot>x) = proj S\<cdot>x"
  using \<psi>\<phi> by (simp add: cfun_eq_iff)

lemma \<phi>\<psi>_app [simp]: "\<phi>\<cdot>(\<psi>\<cdot>x) = proj T\<cdot>x"
  using \<phi>\<psi> by (simp add: cfun_eq_iff)

lemma \<phi>_T_app [simp]: "proj T\<cdot>(\<phi>\<cdot>x) = \<phi>\<cdot>x"
  using \<phi>_T by (simp add: cfun_eq_iff)

lemma \<psi>_S_app [simp]: "proj S\<cdot>(\<psi>\<cdot>x) = \<psi>\<cdot>x"
  using \<psi>_S by (simp add: cfun_eq_iff)

lemma \<phi>_S_app [simp]: "\<phi>\<cdot>(proj S\<cdot>x) = \<phi>\<cdot>x"
  by (metis \<phi>_T_app \<phi>\<psi>_app \<psi>\<phi>_app)

lemma \<psi>_T_app [simp]: "\<psi>\<cdot>(proj T\<cdot>x) = \<psi>\<cdot>x"
  by (metis \<psi>_S_app \<phi>\<psi>_app \<psi>\<phi>_app)

text \<open>A decided match reads the same from either side.\<close>

lemma match_transport:
  "(maximal_at T (\<phi>\<cdot>x) \<and> proj T\<cdot>y = \<phi>\<cdot>x) \<longleftrightarrow> (maximal_at S (proj S\<cdot>x) \<and> proj S\<cdot>x = \<psi>\<cdot>y)"
proof
  assume m: "maximal_at T (\<phi>\<cdot>x) \<and> proj T\<cdot>y = \<phi>\<cdot>x"
  have "proj S\<cdot>x = \<psi>\<cdot>y"
    by (metis m \<psi>\<phi>_app \<psi>_T_app)
  moreover have "maximal_at S (proj S\<cdot>x)"
    unfolding maximal_at_def
  proof (intro conjI allI impI)
    fix t
    assume t: "proj S\<cdot>t = t" and le: "proj S\<cdot>x \<sqsubseteq> t"
    have "\<phi>\<cdot>t = \<phi>\<cdot>x"
      using maximal_at_eq[OF m[THEN conjunct1] \<phi>_T_app] monofun_cfun_arg[OF le, of \<phi>] by simp
    then show "t = proj S\<cdot>x"
      by (metis t \<psi>\<phi>_app)
  qed simp
  ultimately show "maximal_at S (proj S\<cdot>x) \<and> proj S\<cdot>x = \<psi>\<cdot>y"
    by blast
next
  assume m: "maximal_at S (proj S\<cdot>x) \<and> proj S\<cdot>x = \<psi>\<cdot>y"
  have "proj T\<cdot>y = \<phi>\<cdot>x"
    by (metis m \<phi>\<psi>_app \<phi>_S_app)
  moreover have "maximal_at T (\<phi>\<cdot>x)"
    unfolding maximal_at_def
  proof (intro conjI allI impI)
    fix t
    assume t: "proj T\<cdot>t = t" and le: "\<phi>\<cdot>x \<sqsubseteq> t"
    have "\<psi>\<cdot>t = proj S\<cdot>x"
      using maximal_at_eq[OF m[THEN conjunct1] \<psi>_S_app] monofun_cfun_arg[OF le, of \<psi>] by simp
    then show "t = \<phi>\<cdot>x"
      by (metis t \<phi>\<psi>_app \<phi>_S_app)
  qed simp
  ultimately show "maximal_at T (\<phi>\<cdot>x) \<and> proj T\<cdot>y = \<phi>\<cdot>x"
    by blast
qed

lemma blocks_joinable: "proj A\<cdot>x \<Up> proj B\<cdot>y"
proof (rule proj_slide)
  show "proj B\<cdot>(proj B\<cdot>y) = proj B\<cdot>y"
    by simp
  have "proj B\<cdot>(proj A\<cdot>x) = \<bottom>"
    using proj_inf[of B A x] disjoint by (simp add: lattice_meet_commute proj_bot)
  then show "proj B\<cdot>(proj A\<cdot>x) \<sqsubseteq> proj B\<cdot>y"
    by simp
qed

definition block_join :: "'r \<times> 'r \<rightarrow> 'r"
  where "block_join = (\<Lambda>(x, y). proj A\<cdot>x \<squnion> proj B\<cdot>y)"

lemma block_join_beta [simp]: "block_join\<cdot>(x, y) = proj A\<cdot>x \<squnion> proj B\<cdot>y"
  unfolding block_join_def by (simp add: split_beta' cont_join_joinable blocks_joinable)

sublocale keys: bag_join_keys "{k. maximal_at T k}" "{k. proj T\<cdot>k = k}"
  by unfold_locales (simp add: maximal_at_eq)

definition bag_join :: "join_side \<Rightarrow> join_side \<Rightarrow> 'r bag_pd \<rightarrow> 'r bag_pd \<rightarrow> 'r bag_pd"
  where "bag_join wl wr = (\<Lambda> X Y. bag_map\<cdot>block_join\<cdot>(keys.bag_pair_join wl wr \<phi> (proj T)\<cdot>X\<cdot>Y))"

lemma bag_join_eq: "bag_join wl wr\<cdot>X\<cdot>Y = bag_map\<cdot>block_join\<cdot>(keys.bag_pair_join wl wr \<phi> (proj T)\<cdot>X\<cdot>Y)"
  by (simp add: bag_join_def)

text \<open>Sanity check: an N:1 join of an @{text A}-row and a @{text B}-row with matching decided keys
  gives the joined row once and the referenced row open-endedly often.\<close>

lemma bag_join_unit_match:
  assumes a: "Cpo.compact a" "proj A\<cdot>a = a" and b: "Cpo.compact b" "proj B\<cdot>b = b"
    and m: "maximal_at T (\<phi>\<cdot>a)" "proj T\<cdot>b = \<phi>\<cdot>a"
  shows "bag_join Closed Open\<cdot>(bag_unit\<cdot>a)\<cdot>(bag_unit\<cdot>b) =
    bag_unit\<cdot>(a \<squnion> b) \<union>\<^sub>b bag_omega\<cdot>(bag_unit\<cdot>b)"
proof -
  have "keys.bag_pair_join Closed Open \<phi> (proj T)\<cdot>(bag_unit\<cdot>a)\<cdot>(bag_unit\<cdot>b) =
      bag_unit\<cdot>(a, b) \<union>\<^sub>b bag_omega\<cdot>(bag_unit\<cdot>(\<bottom>, b))"
    using a b m by (intro keys.bag_pair_join_unit_match) simp_all
  moreover have "block_join\<cdot>(a, b) = a \<squnion> b" "block_join\<cdot>(\<bottom>, b) = b"
    using a b deflation.below[OF proj_defl, of A \<bottom>] by (simp_all add: join_absorbI)
  ultimately show ?thesis
    by (simp add: bag_join_eq)
qed

end

end
