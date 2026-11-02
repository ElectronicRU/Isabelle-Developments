theory Content_Law
  imports Frame Option_PD "HOLCF-Library.List_Cpo"
begin

default_sort type

section \<open>The content law\<close>

text \<open>An expression reads its data through two finite lists of \<^emph>\<open>generalized tables\<close>.  An entry's
  \<^emph>\<open>selector\<close> \<open>(a, \<rho>)\<close> picks the fiber: the rows whose key agrees with the key at hand at
  \<open>a \<squnion> \<rho> \<sqinter> L\<close>, for the frame LOD \<open>L\<close>.  A \<^emph>\<open>guard entry\<close> tests its fiber's rows with the
  frame's filters (the ambient filter and the slice coarsened to \<open>\<rho>\<close>) and its guard, and records,
  three-valued, at which keys some row passes: presence, ignoring the values.  A \<^emph>\<open>value entry\<close> reads its whole fiber
  through a view \<open>(c, \<kappa>)\<close>: the content maps each row's key at \<open>\<kappa>\<close> to its section at \<open>c\<close>, which
  the key determines.  The frame's filters only reach the data through the guards.  The
  \<^emph>\<open>content law\<close> says that the semantics at a key is a function of these contents.\<close>

text \<open>An entry: a selector, picking the fiber; a key part, keying the content; and a payload.  A
  \<^emph>\<open>guard entry\<close> carries a \<^emph>\<open>row guard\<close>, a condition on rows, and a \<^emph>\<open>key guard\<close>, a condition on
  keys.  Its content is defined at the key parts of its fiber's rows: there it gives the truth of
  some row with that key part passing the frame's filters (the ambient filter on the row, the
  slice on its key) and the entry's two guards, a three-valued existential over the one row.  It
  ignores the values, and it is the only place where the frame's filters act.  A \<^emph>\<open>value entry\<close> carries a section.  Its
  content maps each key, at its key part, of the rows of its fiber (all rows of the dataset at the
  selector) to their section there, which the key determines.  Presence comes from the guards,
  values from the value entries.\<close>

record 'k selector =
  lower_part :: "'k semi_factor"
  upper_part :: "'k semi_factor"

hide_const (open) selector.truncate

abbreviation sel :: "'k semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> 'k selector" where
  "sel a \<rho> \<equiv> \<lparr>lower_part = a, upper_part = \<rho>\<rparr>"

text \<open>A selector is the affine LOD map \<open>L \<mapsto> a \<squnion> \<rho> \<sqinter> L\<close>: at the frame LOD it gives the group LOD.\<close>

abbreviation sel_at :: "('k::{bifinite, distributive_cpo}) selector \<Rightarrow> 'k semi_factor \<Rightarrow> 'k semi_factor" where
  "sel_at S L \<equiv> lower_part S \<squnion> (upper_part S \<sqinter> L)"

record ('k::"{domain, distributive_cpo}", 'p) entry =
  esel :: "'k selector"
  ekeys :: "'k semi_factor"
  epay :: 'p

hide_const (open) entry.truncate

abbreviation elower :: "('k::{domain, distributive_cpo}, 'p) entry \<Rightarrow> 'k semi_factor" where
  "elower e \<equiv> lower_part (esel e)"

abbreviation eupper :: "('k::{domain, distributive_cpo}, 'p) entry \<Rightarrow> 'k semi_factor" where
  "eupper e \<equiv> upper_part (esel e)"

abbreviation eguard :: "('k::{domain, distributive_cpo}, 'r::{domain, distributive_cpo} guard \<times> 'k guard) entry \<Rightarrow> 'r guard" where
  "eguard e \<equiv> fst (epay e)"

abbreviation ekguard :: "('k::{domain, distributive_cpo}, 'r::{domain, distributive_cpo} guard \<times> 'k guard) entry \<Rightarrow> 'k guard" where
  "ekguard e \<equiv> snd (epay e)"

abbreviation ecols :: "('k::{domain, distributive_cpo}, 'r::{domain, distributive_cpo} semi_factor) entry \<Rightarrow> 'r semi_factor" where
  "ecols e \<equiv> epay e"

abbreviation eview :: "('k::{domain, distributive_cpo}, 'r::{domain, distributive_cpo} semi_factor) entry \<Rightarrow> ('r, 'k) view" where
  "eview e \<equiv> (ecols e, ekeys e)"

abbreviation mk_guard ::
  "'k selector \<Rightarrow> 'r guard \<Rightarrow> 'k guard \<Rightarrow> 'k semi_factor \<Rightarrow> ('k::{domain, distributive_cpo}, 'r::{domain, distributive_cpo} guard \<times> 'k guard) entry" where
  "mk_guard S \<gamma> \<sigma> \<kappa> \<equiv> \<lparr>esel = S, ekeys = \<kappa>, epay = (\<gamma>, \<sigma>)\<rparr>"

abbreviation mk_value ::
  "'k selector \<Rightarrow> 'r semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('k::{domain, distributive_cpo}, 'r::{domain, distributive_cpo} semi_factor) entry" where
  "mk_value S c \<kappa> \<equiv> \<lparr>esel = S, ekeys = \<kappa>, epay = c\<rparr>"

text \<open>An expression's content semantics takes the guards' contents, truth values at the keys where
  they are defined, as a plain argument, and is continuous in the value entries' contents.\<close>

record ('k::"domain", 'f::type, 'r::"{bifinite, distributive_cpo}", 'v::bifinite) expr =
  emind :: "'k semi_factor"
  eguards :: "('k, 'r guard \<times> 'k guard) entry list"
  evalues :: "('k, 'r semi_factor) entry list"
  esem :: "'r lower_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'v option_pd"
  csem :: "('k \<Rightarrow> tr option) list \<Rightarrow> ('k \<Rightarrow> 'r option) list \<rightarrow> 'v option_pd"

hide_const (open) expr.truncate

text \<open>The selectors of all of an expression's entries.\<close>

abbreviation esels :: "('k::{domain, distributive_cpo}, 'f, 'r::{bifinite, distributive_cpo}, 'v::bifinite, 'z) expr_scheme \<Rightarrow> 'k selector list" where
  "esels E \<equiv> map esel (eguards E) @ map esel (evalues E)"

lemma esels_guardI: "e \<in> set (eguards E) \<Longrightarrow> esel e \<in> set (esels E)"
  by simp

lemma esels_valueI: "e \<in> set (evalues E) \<Longrightarrow> esel e \<in> set (esels E)"
  by simp

text \<open>Selector transformers: raising the lower part by the masked part of an LOD, and meeting the
  upper part with one.\<close>

definition include_sel :: "'k::{bifinite, distributive_cpo} semi_factor \<Rightarrow> 'k selector \<Rightarrow> 'k selector" where
  "include_sel M S = sel (sel_at S M) (upper_part S)"

definition trunc_sel :: "'k::{bifinite, distributive_cpo} semi_factor \<Rightarrow> 'k selector \<Rightarrow> 'k selector" where
  "trunc_sel \<tau> S = sel (lower_part S) (upper_part S \<sqinter> \<tau>)"

lemma include_sel_simps [simp]:
  "lower_part (include_sel M S) = sel_at S M" "upper_part (include_sel M S) = upper_part S"
  by (simp_all add: include_sel_def)

lemma trunc_sel_simps [simp]:
  "lower_part (trunc_sel \<tau> S) = lower_part S" "upper_part (trunc_sel \<tau> S) = upper_part S \<sqinter> \<tau>"
  by (simp_all add: trunc_sel_def)

text \<open>Contents are maps from keys to sections.  A graph, a single-valued set of pairs, gives one;
  the value it records at a key is \<open>cval\<close>.\<close>

definition cval :: "('k \<times> 'b) set \<Rightarrow> 'k \<Rightarrow> 'b" where
  "cval X q = (THE v. (q, v) \<in> X)"

lemma cval_singleton [simp]: "cval {(q, v)} q = v"
  by (simp add: cval_def)

lemma cval_eq: "single_valued X \<Longrightarrow> (q, v) \<in> X \<Longrightarrow> cval X q = v"
  unfolding cval_def by (rule the_equality) (auto dest: single_valuedD)

definition gmap :: "('k \<times> 'b) set \<Rightarrow> 'k \<Rightarrow> 'b option" where
  "gmap X q = (if q \<in> fst ` X then Some (cval X q) else None)"

definition graph :: "('k \<Rightarrow> 'b option) \<Rightarrow> ('k \<times> 'b) set" where
  "graph m = {(q, s). m q = Some s}"

lemma dom_gmap [simp]: "dom (gmap X) = fst ` X"
  by (auto simp: gmap_def dom_def)

lemma gmap_empty_iff [simp]: "gmap X = Map.empty \<longleftrightarrow> X = {}"
  unfolding dom_eq_empty_conv[symmetric] dom_gmap by simp

lemma gmap_apply: "single_valued X \<Longrightarrow> (q, s) \<in> X \<Longrightarrow> gmap X q = Some s"
  unfolding gmap_def by (simp add: cval_eq rev_image_eqI)

lemma gmap_singleton [simp]: "gmap {(q, s)} = [q \<mapsto> s]"
  by (auto simp: gmap_def fun_eq_iff)

lemma single_valued_graph: "single_valued (graph m)"
  by (auto simp: single_valued_def graph_def)

lemma graph_gmap:
  assumes X: "single_valued X"
  shows "graph (gmap X) = X"
proof (rule set_eqI, rule iffI)
  fix x assume "x \<in> graph (gmap X)"
  then obtain q s where x: "x = (q, s)" and q: "gmap X q = Some s" by (auto simp: graph_def)
  then obtain s' where s': "(q, s') \<in> X" by (force simp: gmap_def split: if_splits)
  then show "x \<in> X" using q gmap_apply[OF X s'] by (simp add: x)
next
  fix x assume "x \<in> X"
  then show "x \<in> graph (gmap X)" using gmap_apply[OF X] by (cases x) (simp add: graph_def)
qed

lemma gmap_graph [simp]: "gmap (graph m) = m"
proof
  fix q show "gmap (graph m) q = m q"
  proof (cases "m q")
    case None
    then have "q \<notin> fst ` graph m" by (force simp: graph_def)
    then show ?thesis using None by (simp add: gmap_def)
  next
    case (Some s)
    then have "(q, s) \<in> graph m" by (simp add: graph_def)
    from gmap_apply[OF single_valued_graph this] Some show ?thesis by simp
  qed
qed

text \<open>A guard's content at a key part: none when no row has it, else the Kleene existential over
  the rows having it.  A content is \<^emph>\<open>false\<close> when it is false wherever it is defined: no row passes.\<close>

definition gex :: "'a set \<Rightarrow> ('a \<Rightarrow> tr) \<Rightarrow> tr option" where
  "gex S P = (if S = {} then None else Some (\<exists>\<^sub>K y\<in>S. P y))"

definition gfalse :: "('k \<Rightarrow> tr option) \<Rightarrow> bool" where
  "gfalse G \<longleftrightarrow> (\<forall>q t. G q = Some t \<longrightarrow> t = FF)"

text \<open>Guard contents are \<^emph>\<open>finite\<close> when each is defined at finitely many keys.  An aggregate
  folds over the keys of its fold guard, and of infinitely many members it knows only presence.\<close>

definition gfinite :: "('k \<Rightarrow> tr option) list \<Rightarrow> bool" where
  "gfinite Gs \<longleftrightarrow> (\<forall>G\<in>set Gs. finite (dom G))"

lemma gfinite_simps [simp]:
  "gfinite []" "gfinite (G # Gs) \<longleftrightarrow> finite (dom G) \<and> gfinite Gs" "gfinite (Gs @ Hs) \<longleftrightarrow> gfinite Gs \<and> gfinite Hs"
  by (auto simp: gfinite_def)

lemma gfinite_take: "gfinite Gs \<Longrightarrow> gfinite (take n Gs)" and gfinite_drop: "gfinite Gs \<Longrightarrow> gfinite (drop n Gs)"
  by (auto simp: gfinite_def dest: in_set_takeD in_set_dropD)

lemma gex_None_iff [simp]: "gex S P = None \<longleftrightarrow> S = {}"
  by (simp add: gex_def)

lemma gex_Some: "S \<noteq> {} \<Longrightarrow> gex S P = Some (\<exists>\<^sub>K y\<in>S. P y)"
  by (simp add: gex_def)

lemma gex_empty [simp]: "gex {} P = None"
  by (simp add: gex_def)

lemma gex_cong: "S = T \<Longrightarrow> (\<And>x. x \<in> T \<Longrightarrow> P x = Q x) \<Longrightarrow> gex S P = gex T Q"
  by (simp add: gex_def cong: kleene_bex_cong)

lemma gex_filter_factor:
  assumes "\<And>y. Q (g y) = Q y" and "\<And>y. R (g y) = R y"
  shows "gex {y \<in> M. Q y} R = gex {z \<in> g ` M. Q z} R"
proof -
  have "{z \<in> g ` M. Q z} = g ` {y \<in> M. Q y}" using assms(1) by auto
  then show ?thesis by (simp add: gex_def kleene_bex_image assms(2))
qed

text \<open>Reading a content off the content of a refinement of its key parts: over the classes of a
  partition, the existentials collapse.\<close>

lemma dom_gex_classes: "dom (\<lambda>q0. gex {x \<in> S. g x = q0} P) = g ` S"
  by (auto simp: dom_def)

lemma gex_classes:
  "gex {q0 \<in> dom (\<lambda>q0. gex {x \<in> S. g x = q0} P). C q0} (\<lambda>q0. the (gex {x \<in> S. g x = q0} P)) = gex {x \<in> S. C (g x)} P"
proof -
  let ?Q = "{q0 \<in> g ` S. C q0}"
  have e: "?Q = {} \<longleftrightarrow> {x \<in> S. C (g x)} = {}" by auto
  have "(\<exists>\<^sub>K q0\<in>?Q. the (gex {x \<in> S. g x = q0} P)) = (\<exists>\<^sub>K q0\<in>?Q. \<exists>\<^sub>K x\<in>{x \<in> S. g x = q0}. P x)"
    by (rule kleene_bex_cong[OF refl]) (auto simp: gex_def)
  also have "\<dots> = (\<exists>\<^sub>K x\<in>{x \<in> S. g x \<in> ?Q}. P x)" by (rule kleene_bex_classes)
  also have "{x \<in> S. g x \<in> ?Q} = {x \<in> S. C (g x)}" by auto
  finally have b: "(\<exists>\<^sub>K q0\<in>?Q. the (gex {x \<in> S. g x = q0} P)) = (\<exists>\<^sub>K x\<in>{x \<in> S. C (g x)}. P x)" .
  show ?thesis unfolding dom_gex_classes gex_def[of ?Q] gex_def[of "{x \<in> S. C (g x)}"] e b ..
qed

text \<open>Multiplying a result by a content's truth, absent where the content is undefined.\<close>

lemma gex_mult: "(case gex S P of None \<Rightarrow> Absent | Some t \<Rightarrow> t \<odot> x) = (\<exists>\<^sub>K y\<in>S. P y) \<odot> x"
  by (simp add: gex_def)

subsection \<open>Continuity on contents\<close>

text \<open>Contents are ordered pointwise with missing keys incomparable to present ones, so refining
  a content keeps its keys; results are ordered likewise, and lists componentwise.  The content
  semantics is a continuous function.  Along a chain the keys stay fixed, so a function of a
  \<^emph>\<open>rigid\<close> part of the argument (one that is the same on related arguments) is continuous, and a
  rigid argument may be held fixed.\<close>

definition rigid :: "('a::cpo \<Rightarrow> 'b) \<Rightarrow> bool" where
  "rigid q \<longleftrightarrow> (\<forall>x y. x \<sqsubseteq> y \<longrightarrow> q x = q y)"

lemma rigidI: "(\<And>x y. x \<sqsubseteq> y \<Longrightarrow> q x = q y) \<Longrightarrow> rigid q"
  unfolding rigid_def by blast

lemma rigidD: "rigid q \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> q x = q y"
  unfolding rigid_def by blast

lemma rigid_chain: "rigid q \<Longrightarrow> chain Y \<Longrightarrow> q (Y i) = q (\<Squnion>j. Y j)"
  by (erule rigidD) (erule is_ub_thelub)

lemma rigid_comp: "rigid q \<Longrightarrow> monofun g \<Longrightarrow> rigid (\<lambda>x. q (g x))"
  unfolding rigid_def by (blast dest: monofunE)

lemma cont_rigid_arg:
  fixes h :: "'a::cpo \<Rightarrow> 's \<Rightarrow> 'b::cpo"
  assumes h: "\<And>s. cont (\<lambda>x. h x s)" and q: "rigid q"
  shows "cont (\<lambda>x. h x (q x))"
proof (rule contI2)
  show "monofun (\<lambda>x. h x (q x))"
  proof (rule monofunI)
    fix x y :: 'a assume xy: "x \<sqsubseteq> y"
    have "q y = q x" using rigidD[OF q xy] by simp
    then show "h x (q x) \<sqsubseteq> h y (q y)" by (simp only: cont2monofunE[OF h xy])
  qed
next
  fix Y :: "nat \<Rightarrow> 'a" assume Y: "chain Y"
  have "h (\<Squnion>i. Y i) (q (\<Squnion>i. Y i)) = (\<Squnion>i. h (Y i) (q (\<Squnion>i. Y i)))" by (rule cont2contlubE[OF h Y])
  also have "\<dots> = (\<Squnion>i. h (Y i) (q (Y i)))" by (simp only: rigid_chain[OF q Y])
  finally show "h (\<Squnion>i. Y i) (q (\<Squnion>i. Y i)) \<sqsubseteq> (\<Squnion>i. h (Y i) (q (Y i)))" by simp
qed

lemma cont_rigid: "rigid f \<Longrightarrow> cont f"
  using cont_rigid_arg[of "\<lambda>x s. s" f] by simp

lemma cont_if_rigid:
  assumes "rigid P" and "cont f" and "cont g"
  shows "cont (\<lambda>x. if P x then f x else g x)"
proof -
  have "cont (\<lambda>x. if b then f x else g x)" for b by (cases b) (simp_all add: assms)
  then show ?thesis by (rule cont_rigid_arg[OF _ assms(1)])
qed

lemma map_below_dom: "(X :: 'k \<Rightarrow> 'r::below option) \<sqsubseteq> Y \<Longrightarrow> dom X = dom Y"
proof -
  assume b: "X \<sqsubseteq> Y"
  have "X q = None \<longleftrightarrow> Y q = None" for q
    using fun_belowD[OF b, of q] by (cases "X q"; cases "Y q") simp_all
  then show ?thesis unfolding dom_def by auto
qed

lemma option_below_None: "(u :: 'v::below option) \<sqsubseteq> w \<Longrightarrow> u = None \<longleftrightarrow> w = None"
  by (cases u; cases w) simp_all

lemma rigid_dom: "rigid (\<lambda>X :: 'k \<Rightarrow> 'r::cpo option. dom X)"
  by (rule rigidI) (rule map_below_dom)

lemma rigid_None: "monofun f \<Longrightarrow> rigid (\<lambda>x. f x = (None :: 'v::cpo option))"
  by (rule rigidI) (rule option_below_None, erule monofunE)

lemma rigid_length: "rigid (\<lambda>xs :: 'a::cpo list. P (length xs))"
  by (rule rigidI) (simp add: below_same_length)

lemma cont_hd: "cont (hd :: 'a::cpo list \<Rightarrow> 'a)"
  by (rule list_contI[where g = "\<lambda>x xs y. x"]) simp_all

lemma cont_tl: "cont (tl :: 'a::cpo list \<Rightarrow> 'a list)"
  by (rule list_contI[where g = "\<lambda>x xs y. xs"]) simp_all

lemmas cont2cont_hd [simp, cont2cont] = cont_compose[OF cont_hd]
lemmas cont2cont_tl [simp, cont2cont] = cont_compose[OF cont_tl]

lemma cont_take: "cont (take n :: 'a::cpo list \<Rightarrow> 'a list)"
proof (induct n)
  case (Suc n)
  show ?case by (rule list_contI[where g = "\<lambda>x xs y. x # take n xs"]) (simp_all add: Suc cont_compose)
qed simp

lemma cont_drop: "cont (drop n :: 'a::cpo list \<Rightarrow> 'a list)"
proof (induct n)
  case (Suc n)
  show ?case by (rule list_contI[where g = "\<lambda>x xs y. drop n xs"]) (simp_all add: Suc)
qed (simp add: cont_id)

lemma cont_the: "cont (the :: 'a::cpo option \<Rightarrow> 'a)"
proof (rule contI2[OF monofun_the])
  fix Y :: "nat \<Rightarrow> 'a option" assume Y: "chain Y"
  then show "the (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. the (Y i))"
  proof (cases rule: option_chain_cases)
    case (2 A)
    then show ?thesis by (simp add: lub_Some)
  qed simp
qed

lemma cont_map2: "(\<And>a. cont (h a)) \<Longrightarrow> cont (\<lambda>xs. map2 h as xs)"
proof (induct as)
  case (Cons a as)
  show ?case
    by (rule list_contI[where g = "\<lambda>y ys z. h a y # map2 h as ys"]) (simp_all add: Cons)
qed simp

subsection \<open>Groups and contents\<close>

context dataspace
begin

subsection \<open>Keys and sections guards read\<close>

text \<open>A guard is \<^emph>\<open>keyed\<close> at a key part \<open>a\<close> when in every conforming dataset it is determined by
  the rows' keys there; it \<^emph>\<open>reads\<close> a section \<open>c\<close> when it only depends on the rows' parts at
  \<open>c\<close>.  These are the two things the content law asks of a guard, and only where it needs them: a
  row entry's guard is keyed at its lower part, and the section the contents are computed from is
  read by the guards.\<close>

definition guard_keyed :: "'k semi_factor \<Rightarrow> 'r guard \<Rightarrow> bool" where
  "guard_keyed a \<gamma> \<longleftrightarrow> universally (\<lambda>P. determines P (\<bottom>, a) \<gamma>)"

definition guard_reads :: "'r semi_factor \<Rightarrow> 'r guard \<Rightarrow> bool" where
  "guard_reads c \<gamma> \<longleftrightarrow> (\<forall>y. \<gamma>\<cdot>(y \<downharpoonright> c) = \<gamma>\<cdot>y)"

lemma guard_keyed_mono: "guard_keyed a \<gamma> \<Longrightarrow> a \<sqsubseteq> b \<Longrightarrow> guard_keyed b \<gamma>"
  unfolding guard_keyed_def by (erule universally_mono) (erule determines_mono, simp add: below_prod_def)

lemma guard_keyed_gtrue: "guard_keyed a gtrue"
  by (simp add: guard_keyed_def universally_def determines_def)

lemma guard_keyed_gand: "guard_keyed a \<gamma> \<Longrightarrow> guard_keyed a \<delta> \<Longrightarrow> guard_keyed a (gand \<gamma> \<delta>)"
  unfolding guard_keyed_def universally_def determines_def gand_apply by (blast intro: monofun_cfun)

lemma guard_keyed_holds: "guard_keyed (slod X) (guard_holds X)"
  by (simp add: guard_keyed_def universally_def determines_def guard_holds_def monofun_cfun_arg)

lemma guard_reads_gtrue: "guard_reads c gtrue"
  by (simp add: guard_reads_def)

lemma guard_reads_gand: "guard_reads c \<gamma> \<Longrightarrow> guard_reads c \<delta> \<Longrightarrow> guard_reads c (gand \<gamma> \<delta>)"
  by (simp add: guard_reads_def gand_apply)

text \<open>Likewise for key guards: \<^emph>\<open>keyed\<close> at \<open>a\<close> when they only read keys at \<open>a\<close>; reading \<open>c\<close> when
  they only depend on the rows' keys through the rows' parts at \<open>c\<close>.\<close>

definition kguard_keyed :: "'k semi_factor \<Rightarrow> 'k guard \<Rightarrow> bool" where
  "kguard_keyed a \<sigma> \<longleftrightarrow> (\<forall>k. \<sigma>\<cdot>(proj a\<cdot>k) = \<sigma>\<cdot>k)"

definition kguard_reads :: "'r semi_factor \<Rightarrow> 'k guard \<Rightarrow> bool" where
  "kguard_reads c \<sigma> \<longleftrightarrow> (\<forall>y. \<sigma>\<cdot>(row_key\<cdot>(y \<downharpoonright> c)) = \<sigma>\<cdot>(row_key\<cdot>y))"

lemma kguard_keyed_gtrue: "kguard_keyed a gtrue"
  by (simp add: kguard_keyed_def)

text \<open>Rows agreeing on a key part covering where a guard is keyed agree on it.\<close>

lemma guard_agree:
  assumes g: "guard_keyed a \<gamma>" and d: "conforms data" and x: "x \<in> lower_maximal data" and y: "y \<in> lower_maximal data"
    and le: "a \<sqsubseteq> G" and e: "rproj G y = rproj G x"
  shows "\<gamma>\<cdot>y = \<gamma>\<cdot>x"
proof (rule determinesD[OF universallyD[OF g[unfolded guard_keyed_def] d] y x])
  have "rproj a y = rproj a x" using arg_cong[OF e, of "Rep_cfun (proj a)"] by (simp add: proj_le[OF le])
  then show "vpart (\<bottom>, a) y = vpart (\<bottom>, a) x" by (simp add: proj_bot)
qed

text \<open>Rows agreeing on a key part covering a keyed view's key part agree on its section.\<close>

lemma view_agree:
  assumes v: "keyed_view v" and d: "conforms data" and x: "x \<in> lower_maximal data" and y: "y \<in> lower_maximal data"
    and le: "snd v \<sqsubseteq> G" and e: "rproj G y = rproj G x"
  shows "y \<downharpoonright> fst v = x \<downharpoonright> fst v"
proof -
  have det: "determines (lower_maximal data) (vkey v) (cfst oo vproj v)" by (rule keyed_view_determines[OF v d])
  have "rproj (snd v) y = rproj (snd v) x"
    using arg_cong[OF e, of "Rep_cfun (proj (snd v))"] by (simp add: proj_le[OF le])
  then have "vpart (vkey v) y = vpart (vkey v) x" by (simp add: vkey_def proj_bot)
  from determinesD[OF det y x this] show ?thesis by (simp add: vpart_def)
qed

lemma keyed_view_bot_view: "keyed_view (\<bottom> :: ('r, 'k) view)"
  unfolding inst_prod_pcpo by (rule keyed_view_key)

text \<open>A value entry is \<^emph>\<open>well-formed\<close> when its view is keyed.  Then the view's key part determines
  its section on the rows of a conforming dataset: contents are graphs.  This is a property of the
  expression, independent of the frame.\<close>

definition entry_wf :: "('k, 'r semi_factor) entry \<Rightarrow> bool" where
  "entry_wf e \<longleftrightarrow> keyed_view (eview e)"

lemma entry_wf_view: "keyed_view (c, \<kappa>) \<Longrightarrow> entry_wf (mk_value S c \<kappa>)"
  by (simp add: entry_wf_def)

text \<open>The \<^emph>\<open>fiber\<close> of a selector: the rows whose key agrees with the key at hand at the group LOD.
  Its \<^emph>\<open>group\<close> are the rows passing the frame's filters, the slice coarsened to the upper part;
  whether the group is \<^emph>\<open>populated\<close> is three-valued, the Kleene existential of the filters over the
  fiber.\<close>

definition fiber :: "'r lower_pd \<Rightarrow> 'k semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'r set" where
  "fiber data a \<rho> F k = {y \<in> lower_maximal data. rproj (a \<squnion> (\<rho> \<sqinter> flod F)) y = proj (a \<squnion> (\<rho> \<sqinter> flod F))\<cdot>k}"

definition populated :: "'r lower_pd \<Rightarrow> 'k semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> tr" where
  "populated data a \<rho> F k = (\<exists>\<^sub>K y\<in>fiber data a \<rho> F k. fguard \<rho> F\<cdot>y)"

text \<open>A guard entry's fiber is its selector's.  A row passes the entry when the row passes the
  ambient filter and the row guard, and its key the slice, coarsened to the entry's upper part,
  and the key guard; the content at a key part of the fiber is the Kleene existential of passing
  over the fiber's rows with that key part.\<close>

definition gfiber :: "'r lower_pd \<Rightarrow> ('k, 'r guard \<times> 'k guard) entry \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'r set" where
  "gfiber data e F k = fiber data (elower e) (eupper e) F k"

definition gtruth :: "('k, 'r guard \<times> 'k guard) entry \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'r guard" where
  "gtruth e F = gand (gand (amb F) (eguard e)) (gand (sopen (coarsen (eupper e) (slice F))) (ekguard e) oo row_key)"

definition gcontent :: "'r lower_pd \<Rightarrow> ('k, 'r guard \<times> 'k guard) entry \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> tr option" where
  "gcontent data e F k q = gex {y \<in> gfiber data e F k. rproj (ekeys e) y = q} (Rep_cfun (gtruth e F))"

abbreviation gcontents :: "'r lower_pd \<Rightarrow> ('k, 'r guard \<times> 'k guard) entry list \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> ('k \<Rightarrow> tr option) list" where
  "gcontents data gs F k \<equiv> map (\<lambda>e. gcontent data e F k) gs"

text \<open>Passing an entry is passing the frame's filters at its upper part and its own guards.\<close>

lemma gtruth_split: "gtruth e F\<cdot>y = pand\<cdot>(fguard (eupper e) F\<cdot>y)\<cdot>(pand\<cdot>(eguard e\<cdot>y)\<cdot>(ekguard e\<cdot>(row_key\<cdot>y)))"
proof -
  have "pand\<cdot>(pand\<cdot>a\<cdot>b)\<cdot>(pand\<cdot>c\<cdot>d) = pand\<cdot>(pand\<cdot>a\<cdot>c)\<cdot>(pand\<cdot>b\<cdot>d)" for a b c d
    by (metis pand_assoc pand_commute)
  then show ?thesis by (simp add: gtruth_def fguard_def gand_apply guard_holds_apply)
qed

lemma gtruth_cong: "amb F = amb F' \<Longrightarrow> slice F = slice F' \<Longrightarrow> gtruth e F = gtruth e F'"
  by (simp add: gtruth_def)

lemma gtruth_gtrue: "gtruth (mk_guard S gtrue gtrue \<kappa>) F = fguard (upper_part S) F"
  by (simp add: cfun_eq_iff gtruth_split)

text \<open>The content of a guard passing every row tests the frame's filters alone; keyed at nothing,
  its one key part is \<open>\<bottom>\<close>, where it tells whether the group is populated.\<close>

lemma gcontent_gtrue: "gcontent data (mk_guard S gtrue gtrue \<kappa>) F k q =
    gex {y \<in> fiber data (lower_part S) (upper_part S) F k. rproj \<kappa> y = q} (Rep_cfun (fguard (upper_part S) F))"
  by (simp add: gcontent_def gfiber_def gtruth_gtrue)

lemma gcontent_gtrue_bot:
  "gcontent data (mk_guard S gtrue gtrue \<bottom>) F k =
    (\<lambda>q. if q = \<bottom> then gex (fiber data (lower_part S) (upper_part S) F k) (Rep_cfun (fguard (upper_part S) F)) else None)"
  by (simp add: fun_eq_iff gcontent_gtrue proj_bot eq_commute[of \<bottom>])

lemma dom_gcontent: "dom (gcontent data e F k) = (\<lambda>y. rproj (ekeys e) y) ` gfiber data e F k"
  by (auto simp: dom_def gcontent_def)

text \<open>A value entry's fiber is its selector's; its content graph pairs each row's key at the key
  part with its section at the columns, and the content is that graph as a map.\<close>

definition vfiber :: "'r lower_pd \<Rightarrow> ('k, 'r semi_factor) entry \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'r set" where
  "vfiber data e F k = fiber data (elower e) (eupper e) F k"

definition cpair :: "('k, 'r semi_factor) entry \<Rightarrow> 'r \<Rightarrow> 'k \<times> 'r" where
  "cpair e y = (rproj (ekeys e) y, y \<downharpoonright> ecols e)"

lemma cpair_vpart: "cpair e y = (snd (vpart (eview e) y), fst (vpart (eview e) y))"
  by (simp add: cpair_def vpart_def)

definition cgraph :: "'r lower_pd \<Rightarrow> ('k, 'r semi_factor) entry \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> ('k \<times> 'r) set" where
  "cgraph data e F k = cpair e ` vfiber data e F k"

definition content :: "'r lower_pd \<Rightarrow> ('k, 'r semi_factor) entry \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> 'r option" where
  "content data e F k = gmap (cgraph data e F k)"

abbreviation contents :: "'r lower_pd \<Rightarrow> ('k, 'r semi_factor) entry list \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> ('k \<Rightarrow> 'r option) list" where
  "contents data es F k \<equiv> map (\<lambda>e. content data e F k) es"

text \<open>The \<^emph>\<open>point families\<close> at a row and a key: each entry's content as if its fiber were that
  one row with that key.  A fiber of one row gives the point content.\<close>

definition gpoint :: "('k, 'r guard \<times> 'k guard) entry list \<Rightarrow> 'r \<times> 'k \<Rightarrow> ('k \<Rightarrow> tr option) list" where
  "gpoint gs p = map (\<lambda>e. [proj (ekeys e)\<cdot>(snd p) \<mapsto> TT]) gs"

definition point :: "('k, 'r semi_factor) entry list \<Rightarrow> 'r \<times> 'k \<Rightarrow> ('k \<Rightarrow> 'r option) list" where
  "point es p = map (\<lambda>e. [proj (ekeys e)\<cdot>(snd p) \<mapsto> fst p \<downharpoonright> ecols e]) es"

lemma gpoint_simps [simp]:
  "gpoint [] p = []" "gpoint (e # gs) p = [proj (ekeys e)\<cdot>(snd p) \<mapsto> TT] # gpoint gs p"
  "gpoint (gs @ gs') p = gpoint gs p @ gpoint gs' p" "length (gpoint gs p) = length gs"
  by (simp_all add: gpoint_def)

lemma point_simps [simp]:
  "point [] p = []" "point (e # es) p = [proj (ekeys e)\<cdot>(snd p) \<mapsto> fst p \<downharpoonright> ecols e] # point es p"
  "point (es @ es') p = point es p @ point es' p" "length (point es p) = length es"
  by (simp_all add: point_def)

lemma content_single_fiber: "vfiber data e F k = {y} \<Longrightarrow> content data e F k = hd (point [e] (y, row_key\<cdot>y))"
  by (simp add: content_def cgraph_def cpair_def)

text \<open>A \<^emph>\<open>row entry\<close> keys its content within its lower part, and a row guard entry's guards are
  keyed there too: rows of a fiber, which agree there, agree on what the entry reads, so its
  content has at most one key part, and there the guards are those of any row, conjoined with the
  existential of the frame's filters.\<close>

definition row_entry :: "('k, 'r semi_factor) entry \<Rightarrow> bool" where
  "row_entry e \<longleftrightarrow> ekeys e \<sqsubseteq> elower e"

definition row_guard_entry :: "('k, 'r guard \<times> 'k guard) entry \<Rightarrow> bool" where
  "row_guard_entry e \<longleftrightarrow> ekeys e \<sqsubseteq> elower e \<and> guard_keyed (elower e) (eguard e) \<and> kguard_keyed (elower e) (ekguard e)"

lemma rproj_agree: "s \<sqsubseteq> G \<Longrightarrow> rproj G y = rproj G x \<Longrightarrow> rproj s y = rproj s x"
  by (metis proj_le)

lemma row_entry_image:
  assumes e: "entry_wf e" and r: "row_entry e" and d: "conforms data" and Y: "Y \<subseteq> lower_maximal data"
    and x: "x \<in> Y" and aG: "elower e \<sqsubseteq> G" and agree: "\<And>y. y \<in> Y \<Longrightarrow> rproj G y = rproj G x"
  shows "cpair e ` Y = {cpair e x}"
proof -
  have sG: "ekeys e \<sqsubseteq> G" using r aG unfolding row_entry_def by (rule below_trans)
  have xm: "x \<in> lower_maximal data" using x Y by blast
  have kv: "keyed_view (eview e)" using e by (simp add: entry_wf_def)
  have sG': "snd (eview e) \<sqsubseteq> G" using sG by simp
  have h: "cpair e y = cpair e x" if y: "y \<in> Y" for y
    using rproj_agree[OF sG agree[OF y]] view_agree[OF kv d xm _ sG' agree[OF y]] y Y
    unfolding cpair_def by force
  show ?thesis using x h by blast
qed

lemma row_guard_entry_image:
  assumes r: "row_guard_entry e" and d: "conforms data" and Y: "Y \<subseteq> lower_maximal data"
    and x: "x \<in> Y" and aG: "elower e \<sqsubseteq> G" and agree: "\<And>y. y \<in> Y \<Longrightarrow> rproj G y = rproj G x"
  shows "gex {y \<in> Y. rproj (ekeys e) y = q} (\<lambda>y. pand\<cdot>(\<phi> y)\<cdot>(pand\<cdot>(eguard e\<cdot>y)\<cdot>(ekguard e\<cdot>(row_key\<cdot>y)))) =
    (if q = rproj (ekeys e) x then Some (pand\<cdot>(\<exists>\<^sub>K y\<in>Y. \<phi> y)\<cdot>(pand\<cdot>(eguard e\<cdot>x)\<cdot>(ekguard e\<cdot>(row_key\<cdot>x)))) else None)"
proof -
  have sG: "ekeys e \<sqsubseteq> G" and gk: "guard_keyed (elower e) (eguard e)" and kk: "kguard_keyed (elower e) (ekguard e)"
    using r aG unfolding row_guard_entry_def by (blast intro: below_trans)+
  have xm: "x \<in> lower_maximal data" using x Y by blast
  have g: "eguard e\<cdot>y = eguard e\<cdot>x" if y: "y \<in> Y" for y
    using guard_agree[OF gk d xm _ aG agree[OF y]] y Y by blast
  have k: "ekguard e\<cdot>(row_key\<cdot>y) = ekguard e\<cdot>(row_key\<cdot>x)" if y: "y \<in> Y" for y
  proof -
    have "ekguard e\<cdot>(row_key\<cdot>y) = ekguard e\<cdot>(rproj (elower e) y)" using kk by (simp add: kguard_keyed_def)
    also have "\<dots> = ekguard e\<cdot>(rproj (elower e) x)" by (simp only: rproj_agree[OF aG agree[OF y]])
    also have "\<dots> = ekguard e\<cdot>(row_key\<cdot>x)" using kk by (simp add: kguard_keyed_def)
    finally show ?thesis .
  qed
  have h: "rproj (ekeys e) y = rproj (ekeys e) x" if y: "y \<in> Y" for y
    by (rule rproj_agree[OF sG agree[OF y]])
  show ?thesis
  proof (cases "q = rproj (ekeys e) x")
    case True
    have s: "{y \<in> Y. rproj (ekeys e) y = q} = Y" using True h by auto
    have "(\<exists>\<^sub>K y\<in>Y. pand\<cdot>(\<phi> y)\<cdot>(pand\<cdot>(eguard e\<cdot>y)\<cdot>(ekguard e\<cdot>(row_key\<cdot>y)))) =
        (\<exists>\<^sub>K y\<in>Y. pand\<cdot>(\<phi> y)\<cdot>(pand\<cdot>(eguard e\<cdot>x)\<cdot>(ekguard e\<cdot>(row_key\<cdot>x))))"
      by (rule kleene_bex_cong[OF refl]) (simp add: g k)
    also have "\<dots> = pand\<cdot>(\<exists>\<^sub>K y\<in>Y. \<phi> y)\<cdot>(pand\<cdot>(eguard e\<cdot>x)\<cdot>(ekguard e\<cdot>(row_key\<cdot>x)))" by (rule kleene_bex_pand_const)
    finally show ?thesis unfolding s using True x by (auto simp: gex_def)
  next
    case False
    have s: "{y \<in> Y. rproj (ekeys e) y = q} = {}" using False h by auto
    show ?thesis unfolding s using False by simp
  qed
qed

text \<open>Content graphs of well-formed value entries are single-valued.\<close>

lemma cgraph_single_valued:
  assumes e: "entry_wf e" and d: "conforms data"
  shows "single_valued (cgraph data e F k)"
proof (rule single_valuedI)
  fix q u u' assume u: "(q, u) \<in> cgraph data e F k" and u': "(q, u') \<in> cgraph data e F k"
  obtain y where y: "y \<in> vfiber data e F k" "q = rproj (ekeys e) y" "u = y \<downharpoonright> ecols e"
    using u unfolding cgraph_def cpair_def by blast
  obtain y' where y': "y' \<in> vfiber data e F k" "q = rproj (ekeys e) y'" "u' = y' \<downharpoonright> ecols e"
    using u' unfolding cgraph_def cpair_def by blast
  have m: "y \<in> lower_maximal data" "y' \<in> lower_maximal data"
    using y(1) y'(1) by (auto simp: vfiber_def fiber_def)
  have kv: "keyed_view (eview e)" using e by (simp add: entry_wf_def)
  have "y' \<downharpoonright> fst (eview e) = y \<downharpoonright> fst (eview e)"
    by (rule view_agree[OF kv d m(1) m(2) below_refl]) (use y(2) y'(2) in simp)
  then show "u = u'" using y(3) y'(3) by simp
qed

lemma graph_content: "entry_wf e \<Longrightarrow> conforms data \<Longrightarrow> graph (content data e F k) = cgraph data e F k"
  unfolding content_def by (rule graph_gmap[OF cgraph_single_valued])

subsection \<open>Conformance relative to an expression\<close>

text \<open>Graph-ness only compares rows within a fiber, which agree at the group LOD.  So what a dataset
  must satisfy for a value entry, under a frame, is that within the rows the key at the group LOD
  joined with the view's key part determines the view's section.  Raising the frame weakens this; a
  conforming dataset satisfies it under every frame, by the keyedness of the view.  Guard entries
  ask nothing of the dataset.\<close>

definition entry_conf :: "('k, 'r semi_factor) entry \<Rightarrow> 'r lower_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> bool" where
  "entry_conf e data F \<longleftrightarrow> vfd (lower_maximal data) (\<bottom>, sel_at (esel e) (flod F) \<squnion> ekeys e) (ecols e, \<bottom>)"

definition fconf :: "('k, 'r semi_factor) entry list \<Rightarrow> 'r lower_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> bool" where
  "fconf es data F \<longleftrightarrow> (\<forall>e\<in>set es. entry_conf e data F)"

lemma vfd_trans: "vfd P u v \<Longrightarrow> vfd P v w \<Longrightarrow> vfd P u w"
  by (rule determines_trans)

lemma entry_conf_conforms:
  assumes e: "entry_wf e" and d: "conforms data"
  shows "entry_conf e data F"
  unfolding entry_conf_def
proof (rule vfd_trans[OF vfd_refl vfd_trans[OF _ vfd_refl]])
  have "keyed_view (eview e)" using e by (simp add: entry_wf_def)
  then have "vfd (lower_maximal data) (vkey (eview e)) (eview e)"
    unfolding keyed_view_def by (rule universallyD[OF _ d])
  then show "vfd (lower_maximal data) (\<bottom>, ekeys e) (ecols e, ekeys e)" by (simp add: vkey_def)
  show "(\<bottom>, ekeys e) \<sqsubseteq> (\<bottom>, sel_at (esel e) (flod F) \<squnion> ekeys e)" by (simp add: below_prod_def lattice_join_ge2)
  show "(ecols e, \<bottom>) \<sqsubseteq> (ecols e, ekeys e)" by (simp add: below_prod_def)
qed

lemma fconf_conforms: "(\<And>e. e \<in> set es \<Longrightarrow> entry_wf e) \<Longrightarrow> conforms data \<Longrightarrow> fconf es data F"
  unfolding fconf_def by (blast intro: entry_conf_conforms)

text \<open>A value entry reading no columns is conforming everywhere.\<close>

lemma entry_conf_key_pure: "ecols e = \<bottom> \<Longrightarrow> entry_conf e data F"
  unfolding entry_conf_def by (rule vfd_refl) (simp add: below_prod_def)

text \<open>So the laws of an expression whose value entries read no columns hold on every dataset and
  under every frame: such an expression may be evaluated anywhere.\<close>

lemma fconf_key_pure: "(\<And>e. e \<in> set es \<Longrightarrow> ecols e = \<bottom>) \<Longrightarrow> fconf es data F"
  unfolding fconf_def by (blast intro: entry_conf_key_pure)

lemma cgraph_single_valued_conf:
  assumes c: "entry_conf e data F"
  shows "single_valued (cgraph data e F k)"
proof (rule single_valuedI)
  fix q u u' assume u: "(q, u) \<in> cgraph data e F k" and u': "(q, u') \<in> cgraph data e F k"
  let ?G = "sel_at (esel e) (flod F)"
  obtain y where y: "y \<in> vfiber data e F k" "q = rproj (ekeys e) y" "u = y \<downharpoonright> ecols e"
    using u unfolding cgraph_def cpair_def by blast
  obtain y' where y': "y' \<in> vfiber data e F k" "q = rproj (ekeys e) y'" "u' = y' \<downharpoonright> ecols e"
    using u' unfolding cgraph_def cpair_def by blast
  have m: "y \<in> lower_maximal data" "y' \<in> lower_maximal data" and g: "rproj ?G y' = rproj ?G y"
    using y(1) y'(1) by (auto simp: vfiber_def fiber_def)
  have "rproj (?G \<squnion> ekeys e) y' = rproj (?G \<squnion> ekeys e) y"
    using g y(2) y'(2) by (simp only: rproj_sup_eq)
  then have "vpart (\<bottom>, ?G \<squnion> ekeys e) y' = vpart (\<bottom>, ?G \<squnion> ekeys e) y" by (simp add: semi_factor_p_bot)
  from vfdD[OF c[unfolded entry_conf_def] m(2) m(1) this] show "u = u'" using y(3) y'(3) by simp
qed

lemma graph_content_conf: "entry_conf e data F \<Longrightarrow> graph (content data e F k) = cgraph data e F k"
  unfolding content_def by (rule graph_gmap[OF cgraph_single_valued_conf])

text \<open>A conforming content maps each fiber row's key part to its section, and nothing else.\<close>

lemma dom_content: "dom (content data e F k) = (\<lambda>y. rproj (ekeys e) y) ` vfiber data e F k"
  by (simp add: content_def cgraph_def cpair_def image_image)

lemma content_None_iff: "content data e F k q = None \<longleftrightarrow> q \<notin> (\<lambda>y. rproj (ekeys e) y) ` vfiber data e F k"
  unfolding dom_content[symmetric] by auto

lemma content_row:
  assumes c: "entry_conf e data F" and y: "y \<in> vfiber data e F k"
  shows "content data e F k (rproj (ekeys e) y) = Some (y \<downharpoonright> ecols e)"
  unfolding content_def
  by (rule gmap_apply[OF cgraph_single_valued_conf[OF c]]) (use y in \<open>force simp: cgraph_def cpair_def\<close>)

subsection \<open>Column supports of frames and sections of datasets\<close>

text \<open>A frame reads a section read by its ambient filter and covering the column support of its
  slice's LOD.  The
  \<^emph>\<open>point section\<close> of a dataset at a section is the set of its data points cut down to it; it is
  a plain set, not down-closed: contents are sets of values over data points.\<close>

definition frame_reads :: "'r semi_factor \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> bool" where
  "frame_reads c F \<longleftrightarrow> guard_reads c (amb F) \<and> key_supp\<cdot>(slod (slice F)) \<sqsubseteq> c"

definition pts_section :: "'r semi_factor \<Rightarrow> 'r lower_pd \<Rightarrow> 'r set" where
  "pts_section c data = (\<lambda>y. y \<downharpoonright> c) ` lower_maximal data"

lemma image_filter_factor:
  assumes "\<And>y. Q (g y) = Q y" and "\<And>y. h (g y) = h y"
  shows "h ` {y \<in> M. Q y} = h ` {z \<in> g ` M. Q z}"
proof -
  have "{z \<in> g ` M. Q z} = g ` {y \<in> M. Q y}" using assms(1) by auto
  then show ?thesis by (simp add: image_image assms(2))
qed

lemma sopen_section: "key_supp\<cdot>(slod X) \<sqsubseteq> c \<Longrightarrow> sopen X\<cdot>(row_key\<cdot>(y \<downharpoonright> c)) = sopen X\<cdot>(row_key\<cdot>y)"
  by (metis sopen_lod rproj_section)

text \<open>A view's parts are read off any section covering its columns and its key part's support.\<close>

lemma vpart_section: "fst (vsec v) \<sqsubseteq> c \<Longrightarrow> vpart v (y \<downharpoonright> c) = vpart v y"
  unfolding vsec_def fst_conv
  by (simp add: vpart_def proj_le[OF below_trans[OF lattice_join_ge1]]
      rproj_section[OF below_trans[OF lattice_join_ge2]])

text \<open>The content of a value entry is computed from the point section at any section covering the
  group LOD's support and the entry's view.\<close>

lemma content_section:
  assumes G: "key_supp\<cdot>(sel_at (esel e) (flod F)) \<sqsubseteq> c" and fc: "fst (vsec (eview e)) \<sqsubseteq> c"
  shows "content data e F k = gmap (cpair e ` {z \<in> pts_section c data.
    rproj (sel_at (esel e) (flod F)) z = proj (sel_at (esel e) (flod F))\<cdot>k})"
proof -
  let ?G = "sel_at (esel e) (flod F)"
  let ?P = "\<lambda>z. rproj ?G z = proj ?G\<cdot>k"
  have P: "?P (y \<downharpoonright> c) \<longleftrightarrow> ?P y" for y by (simp add: rproj_section[OF G])
  have h: "cpair e (y \<downharpoonright> c) = cpair e y" for y by (simp only: cpair_vpart vpart_section[OF fc])
  have "vfiber data e F k = {y \<in> lower_maximal data. ?P y}" by (auto simp: vfiber_def fiber_def)
  moreover have "cpair e ` {y \<in> lower_maximal data. ?P y} = cpair e ` {z \<in> pts_section c data. ?P z}"
    unfolding pts_section_def by (rule image_filter_factor) (fact P h)+
  ultimately show ?thesis unfolding content_def cgraph_def by simp
qed

text \<open>The content of a guard entry is computed from the point section at any section covering the
  group LOD's support, the frame and the entry's key part, and read by the guard.\<close>

lemma gcontent_section:
  assumes F: "frame_reads c F" and G: "key_supp\<cdot>(sel_at (esel e) (flod F)) \<sqsubseteq> c"
    and kc: "key_supp\<cdot>(ekeys e) \<sqsubseteq> c" and gc: "guard_reads c (eguard e)" and gk: "kguard_reads c (ekguard e)"
  shows "gcontent data e F k q = gex {z \<in> pts_section c data.
    rproj (sel_at (esel e) (flod F)) z = proj (sel_at (esel e) (flod F))\<cdot>k \<and> rproj (ekeys e) z = q}
    (Rep_cfun (gtruth e F))"
proof -
  let ?G = "sel_at (esel e) (flod F)"
  let ?P = "\<lambda>z. rproj ?G z = proj ?G\<cdot>k \<and> rproj (ekeys e) z = q"
  have sl: "key_supp\<cdot>(slod (coarsen (eupper e) (slice F))) \<sqsubseteq> c"
    using F key_supp_mono[OF below_trans[OF slod_coarsen lattice_meet_le1]] unfolding frame_reads_def
    by (blast intro: below_trans)
  have P: "?P (y \<downharpoonright> c) \<longleftrightarrow> ?P y" for y by (simp add: rproj_section[OF G] rproj_section[OF kc])
  have t: "gtruth e F\<cdot>(y \<downharpoonright> c) = gtruth e F\<cdot>y" for y
    using F gc gk unfolding frame_reads_def guard_reads_def kguard_reads_def
    by (simp add: gtruth_def gand_apply sopen_section[OF sl])
  have fib: "{y \<in> gfiber data e F k. rproj (ekeys e) y = q} = {y \<in> lower_maximal data. ?P y}"
    by (auto simp: gfiber_def fiber_def)
  show ?thesis unfolding gcontent_def fib pts_section_def
    by (rule gex_filter_factor[where Q = ?P and g = "\<lambda>y. y \<downharpoonright> c" and R = "Rep_cfun (gtruth e F)", OF P t])
qed

text \<open>Fibers with the same parameters and rows coincide.\<close>

lemma fiber_cong:
  assumes "a \<squnion> (\<rho> \<sqinter> flod F) = a' \<squnion> (\<rho> \<sqinter> flod F')"
    and "proj (a \<squnion> (\<rho> \<sqinter> flod F))\<cdot>k = proj (a' \<squnion> (\<rho> \<sqinter> flod F'))\<cdot>k'"
  shows "fiber data a \<rho> F k = fiber data a' \<rho> F' k'"
  using assms unfolding fiber_def by simp

text \<open>A lower part covering the masked part of the minimal LOD absorbs it.\<close>

lemma sat_absorb:
  fixes a \<rho> m L :: "'k semi_factor"
  assumes "(\<rho> \<sqinter> m) \<sqsubseteq> a"
  shows "a \<squnion> (\<rho> \<sqinter> (m \<squnion> L)) = a \<squnion> (\<rho> \<sqinter> L)"
proof -
  have "a \<squnion> (\<rho> \<sqinter> (m \<squnion> L)) = (a \<squnion> (\<rho> \<sqinter> m)) \<squnion> (\<rho> \<sqinter> L)"
    by (simp only: truncate_sup lattice_join_assoc)
  also have "a \<squnion> (\<rho> \<sqinter> m) = a" by (rule lattice_join_absorb1[OF assms])
  finally show ?thesis .
qed

end

text \<open>Projecting to a finer LOD after a coarser one changes nothing.\<close>

lemma proj_absorb: "a \<sqsubseteq> b \<Longrightarrow> proj b\<cdot>(proj a\<cdot>k) = proj a\<cdot>k"
  by (metis proj_inf lattice_meet_absorb2)

text \<open>Joins of lists in complete lattices.\<close>

lemma fold_join_absorb: "(\<And>x. x \<in> set xs \<Longrightarrow> x \<sqsubseteq> b) \<Longrightarrow> fold (\<squnion>) xs b = (b::'a::lattice_complete)"
  by (induct xs) (simp_all add: lattice_join_absorb2)

lemma fold_join_bots: "fold (\<squnion>) (map (\<lambda>_. \<bottom>) xs) (\<bottom>::'a::lattice_complete) = \<bottom>"
  by (induct xs) (simp_all add: lattice_join_bot_left)

lemma fold_join_least:
  "(\<And>x. x \<in> set xs \<Longrightarrow> x \<sqsubseteq> y) \<Longrightarrow> b \<sqsubseteq> y \<Longrightarrow> fold (\<squnion>) xs b \<sqsubseteq> (y::'a::lattice_complete)"
  by (induct xs arbitrary: b) (simp_all add: lattice_join_least)

lemma fold_join_base: "b \<sqsubseteq> fold (\<squnion>) xs (b::'a::lattice_complete)"
proof (induct xs arbitrary: b)
  case (Cons x xs)
  have "b \<sqsubseteq> x \<squnion> b" by (rule lattice_join_ge2)
  also have "\<dots> \<sqsubseteq> fold (\<squnion>) xs (x \<squnion> b)" by (rule Cons)
  finally show ?case by simp
qed simp

subsection \<open>The laws\<close>

text \<open>A \<^emph>\<open>semilawful\<close> expression has well-formed value entries, its minimal LOD is the join of its
  entries' lower parts, its content semantics is \<^emph>\<open>strict\<close> (absent as soon as one of its guards'
  contents is false), and its presence and values are its content semantics of its contents, at
  every key of its key LOD and every dataset conforming relative to its value entries (the content
  law).  A \<^emph>\<open>lawful\<close> one is moreover present, at the keys of its key LOD, only where the key is
  realised by a row the frame's filter does not reject (the key law).  What an expression does at other keys is the
  extension of its table to the whole key space, which no law reads.  Separately, an expression is
  \<^emph>\<open>saturated\<close> when each lower part covers the part of the minimal LOD its upper part keeps, so
  that its groups depend on the frame LOD only through the key LOD.\<close>

lemma lod_small_bot [simp]: "lod_small (\<bottom> :: 'a::lod_domain semi_factor)"
  by (rule lod_small_compact) simp

context dataspace
begin

abbreviation kd :: "('k, 'f, 'r, 'v::bifinite, 'z) expr_scheme \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k semi_factor" where
  "kd E F \<equiv> emind E \<squnion> flod F"

text \<open>The content semantics of an expression at its contents.\<close>

abbreviation csem_at :: "('k, 'f, 'r, 'v::bifinite, 'z) expr_scheme \<Rightarrow> 'r lower_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'v option_pd" where
  "csem_at E data F k \<equiv> csem E (gcontents data (eguards E) F k)\<cdot>(contents data (evalues E) F k)"

definition cstrict :: "('k, 'f, 'r, 'v::bifinite, 'z) expr_scheme \<Rightarrow> bool" where
  "cstrict E \<longleftrightarrow> (\<forall>Gs Xs. length Gs = length (eguards E) \<longrightarrow> length Xs = length (evalues E) \<longrightarrow>
     gfinite Gs \<longrightarrow> csem E Gs\<cdot>Xs \<noteq> Absent \<longrightarrow> (\<forall>G\<in>set Gs. \<not> gfalse G))"

lemma cstrictI:
  "(\<And>Gs Xs. length Gs = length (eguards E) \<Longrightarrow> length Xs = length (evalues E) \<Longrightarrow> gfinite Gs \<Longrightarrow>
     csem E Gs\<cdot>Xs \<noteq> Absent \<Longrightarrow> (\<forall>G\<in>set Gs. \<not> gfalse G)) \<Longrightarrow> cstrict E"
  unfolding cstrict_def by blast

lemma cstrictD:
  "cstrict E \<Longrightarrow> length Gs = length (eguards E) \<Longrightarrow> length Xs = length (evalues E) \<Longrightarrow> gfinite Gs \<Longrightarrow>
     G \<in> set Gs \<Longrightarrow> gfalse G \<Longrightarrow>
     csem E Gs\<cdot>Xs = Absent"
  unfolding cstrict_def by blast

text \<open>An expression's entries are \<^emph>\<open>small\<close> when their lower parts and keys are finitary, and the
  value entries' columns too: their contents at compact datasets are then compact.\<close>

definition entries_small :: "('k, 'f, 'r, 'v::bifinite, 'z) expr_scheme \<Rightarrow> bool" where
  "entries_small E \<longleftrightarrow> (\<forall>e\<in>set (eguards E). lod_small (elower e) \<and> lod_small (ekeys e)) \<and>
     (\<forall>e\<in>set (evalues E). lod_small (elower e) \<and> lod_small (ekeys e) \<and> lod_small (ecols e))"

definition semilawful :: "('k, 'f, 'r, 'v::bifinite, 'z) expr_scheme \<Rightarrow> bool" where
  "semilawful E \<longleftrightarrow> emind E = fold (\<squnion>) (map lower_part (esels E)) \<bottom> \<and> (\<forall>e\<in>set (evalues E). entry_wf e) \<and>
     cstrict E \<and> entries_small E \<and>
     (\<forall>data F k. fconf (evalues E) data F \<longrightarrow> proj (kd E F)\<cdot>k = k \<longrightarrow> esem E data F k = csem_at E data F k)"

definition lawful :: "('k, 'f, 'r, 'v::bifinite, 'z) expr_scheme \<Rightarrow> bool" where
  "lawful E \<longleftrightarrow> semilawful E \<and>
     (\<forall>data F k. fconf (evalues E) data F \<longrightarrow> proj (kd E F)\<cdot>k = k \<longrightarrow> esem E data F k \<noteq> Absent \<longrightarrow>
       keyimg data F (kd E F) k)"

definition saturated :: "('k, 'f, 'r, 'v::bifinite, 'z) expr_scheme \<Rightarrow> bool" where
  "saturated E \<longleftrightarrow> (\<forall>S\<in>set (esels E). (upper_part S \<sqinter> emind E) \<sqsubseteq> lower_part S)"

lemma saturatedD: "saturated E \<Longrightarrow> S \<in> set (esels E) \<Longrightarrow> (upper_part S \<sqinter> emind E) \<sqsubseteq> lower_part S"
  unfolding saturated_def by blast

lemma semilawfulI:
  assumes "emind E = fold (\<squnion>) (map lower_part (esels E)) \<bottom>"
    and "\<And>e. e \<in> set (evalues E) \<Longrightarrow> entry_wf e"
    and "\<And>data F k. \<lbrakk>fconf (evalues E) data F; proj (emind E \<squnion> flod F)\<cdot>k = k\<rbrakk> \<Longrightarrow> esem E data F k = csem_at E data F k"
    and "cstrict E"
    and "entries_small E"
  shows "semilawful E"
  unfolding semilawful_def using assms by blast

lemma semilawful_mind_lub: "semilawful E \<Longrightarrow> emind E = fold (\<squnion>) (map lower_part (esels E)) \<bottom>"
  unfolding semilawful_def by blast

lemma semilawful_small: "semilawful E \<Longrightarrow> entries_small E"
  unfolding semilawful_def by blast

lemma entries_smallI:
  "(\<And>e. e \<in> set (eguards E) \<Longrightarrow> lod_small (elower e) \<and> lod_small (ekeys e)) \<Longrightarrow>
   (\<And>v. v \<in> set (evalues E) \<Longrightarrow> lod_small (elower v) \<and> lod_small (ekeys v) \<and> lod_small (ecols v)) \<Longrightarrow> entries_small E"
  unfolding entries_small_def by blast

lemma entries_small_guard: "entries_small E \<Longrightarrow> e \<in> set (eguards E) \<Longrightarrow> lod_small (elower e) \<and> lod_small (ekeys e)"
  unfolding entries_small_def by blast

lemma entries_small_value: "entries_small E \<Longrightarrow> v \<in> set (evalues E) \<Longrightarrow> lod_small (elower v) \<and> lod_small (ekeys v) \<and> lod_small (ecols v)"
  unfolding entries_small_def by blast

lemma lod_small_fold_sup: "(\<And>a. a \<in> set as \<Longrightarrow> lod_small a) \<Longrightarrow> lod_small b \<Longrightarrow> lod_small (fold (\<squnion>) as b)"
  for as :: "'k semi_factor list"
  by (induct as arbitrary: b) (simp_all add: lod_small_sup)

text \<open>The minimal LOD of a semilawful expression is small: it joins its entries' lower parts.\<close>

lemma semilawful_mind_small:
  assumes E: "semilawful E"
  shows "lod_small (emind E)"
proof -
  have sm: "lod_small a" if "a \<in> set (map lower_part (esels E))" for a
    using that entries_small_guard [OF semilawful_small [OF E]] entries_small_value [OF semilawful_small [OF E]] by auto
  have "lod_small (fold (\<squnion>) (map lower_part (esels E)) \<bottom>)"
    by (rule lod_small_fold_sup [OF sm lod_small_compact [OF compact_bottom]])
  then show ?thesis by (simp only: semilawful_mind_lub [OF E])
qed

lemma semilawful_wf: "semilawful E \<Longrightarrow> e \<in> set (evalues E) \<Longrightarrow> entry_wf e"
  unfolding semilawful_def by blast

lemma semilawful_cstrict: "semilawful E \<Longrightarrow> cstrict E"
  unfolding semilawful_def by blast

lemma semilawful_keyed: "semilawful E \<Longrightarrow> e \<in> set (evalues E) \<Longrightarrow> keyed_view (eview e)"
  using semilawful_wf unfolding entry_wf_def by blast

lemma semilawful_csem_conf:
  "\<lbrakk>semilawful E; fconf (evalues E) data F; proj (kd E F)\<cdot>k = k\<rbrakk> \<Longrightarrow> esem E data F k = csem_at E data F k"
  unfolding semilawful_def by blast

lemma semilawful_fconf: "semilawful E \<Longrightarrow> conforms data \<Longrightarrow> fconf (evalues E) data F"
  by (rule fconf_conforms[OF semilawful_wf])

lemma semilawful_csem:
  "\<lbrakk>semilawful E; conforms data; proj (kd E F)\<cdot>k = k\<rbrakk> \<Longrightarrow> esem E data F k = csem_at E data F k"
  by (rule semilawful_csem_conf[OF _ semilawful_fconf])

text \<open>Equal contents give equal values, across datasets and frames.\<close>

lemma semilawful_content_law:
  "\<lbrakk>semilawful E; conforms data; conforms data'; proj (kd E F)\<cdot>k = k; proj (kd E F')\<cdot>k' = k';
    gcontents data (eguards E) F k = gcontents data' (eguards E) F' k';
    contents data (evalues E) F k = contents data' (evalues E) F' k'\<rbrakk> \<Longrightarrow> esem E data F k = esem E data' F' k'"
  by (simp only: semilawful_csem)

text \<open>Refined value contents under the same guard contents give refined values, across datasets
  and frames: the content semantics is continuous in the values.\<close>

lemma semilawful_mono:
  "\<lbrakk>semilawful E; conforms data; conforms data'; proj (kd E F)\<cdot>k = k; proj (kd E F')\<cdot>k' = k';
    gcontents data (eguards E) F k = gcontents data' (eguards E) F' k';
    contents data (evalues E) F k \<sqsubseteq> contents data' (evalues E) F' k'\<rbrakk> \<Longrightarrow> esem E data F k \<sqsubseteq> esem E data' F' k'"
  by (simp only: semilawful_csem monofun_cfun_arg)

lemma lawful_semiI:
  assumes "semilawful E"
    and "\<And>data F k. \<lbrakk>fconf (evalues E) data F; proj (emind E \<squnion> flod F)\<cdot>k = k; esem E data F k \<noteq> Absent\<rbrakk> \<Longrightarrow>
      keyimg data F (emind E \<squnion> flod F) k"
  shows "lawful E"
  unfolding lawful_def using assms by blast

lemma lawfulI:
  assumes "emind E = fold (\<squnion>) (map lower_part (esels E)) \<bottom>"
    and "\<And>e. e \<in> set (evalues E) \<Longrightarrow> entry_wf e"
    and "\<And>data F k. \<lbrakk>fconf (evalues E) data F; proj (emind E \<squnion> flod F)\<cdot>k = k\<rbrakk> \<Longrightarrow> esem E data F k = csem_at E data F k"
    and "\<And>data F k. \<lbrakk>fconf (evalues E) data F; proj (emind E \<squnion> flod F)\<cdot>k = k; esem E data F k \<noteq> Absent\<rbrakk> \<Longrightarrow>
      keyimg data F (emind E \<squnion> flod F) k"
    and "cstrict E"
    and "entries_small E"
  shows "lawful E"
  by (rule lawful_semiI[OF semilawfulI[OF assms(1-3,5,6)] assms(4)])

lemma lawful_semilawful: "lawful E \<Longrightarrow> semilawful E"
  unfolding lawful_def by blast

lemma lawful_key_law_conf:
  "lawful E \<Longrightarrow> fconf (evalues E) data F \<Longrightarrow> proj (kd E F)\<cdot>k = k \<Longrightarrow> esem E data F k \<noteq> Absent \<Longrightarrow>
    keyimg data F (kd E F) k"
  unfolding lawful_def by blast

lemma lawful_key_law:
  "lawful E \<Longrightarrow> conforms data \<Longrightarrow> proj (kd E F)\<cdot>k = k \<Longrightarrow> esem E data F k \<noteq> Absent \<Longrightarrow> keyimg data F (kd E F) k"
  by (rule lawful_key_law_conf[OF _ semilawful_fconf[OF lawful_semilawful]])

lemma lawful_keyed: "lawful E \<Longrightarrow> e \<in> set (evalues E) \<Longrightarrow> keyed_view (eview e)"
  by (rule semilawful_keyed[OF lawful_semilawful])

lemma lower_below_mind:
  assumes E: "semilawful E" and S: "S \<in> set (esels E)"
  shows "lower_part S \<sqsubseteq> emind E"
proof -
  have "lower_part S \<in> set (map lower_part (esels E))" unfolding set_map by (rule imageI[OF S])
  then show ?thesis unfolding semilawful_mind_lub[OF E] by (rule fold_join_upper)
qed

lemma lower_below_mind_guard: "semilawful E \<Longrightarrow> e \<in> set (eguards E) \<Longrightarrow> elower e \<sqsubseteq> emind E"
  by (rule lower_below_mind[OF _ esels_guardI])

lemma lower_below_mind_value: "semilawful E \<Longrightarrow> e \<in> set (evalues E) \<Longrightarrow> elower e \<sqsubseteq> emind E"
  by (rule lower_below_mind[OF _ esels_valueI])

lemma group_below_kd:
  "semilawful E \<Longrightarrow> S \<in> set (esels E) \<Longrightarrow> sel_at S (flod F) \<sqsubseteq> kd E F"
  by (rule join_belowI[OF below_trans[OF lower_below_mind lattice_join_ge1]
        below_trans[OF truncate_below lattice_join_ge2]])

text \<open>Contents agree when the fibers do, and for guard entries the frame's filters.\<close>

lemma gcontent_fiber_cong:
  "fiber data (elower e) (eupper e) F k = fiber data' (elower e) (eupper e) F' k' \<Longrightarrow>
    gtruth e F = gtruth e F' \<Longrightarrow> gcontent data e F k = gcontent data' e F' k'"
  by (simp add: fun_eq_iff gcontent_def gfiber_def)

lemma content_fiber_cong:
  "fiber data (elower e) (eupper e) F k = fiber data' (elower e) (eupper e) F' k' \<Longrightarrow>
    content data e F k = content data' e F' k'"
  by (simp add: content_def cgraph_def vfiber_def)

text \<open>Contents only depend on the point section at a section covering the frame, the key LOD and
  what the entries read.\<close>

definition entry_reads :: "'r semi_factor \<Rightarrow> ('k, 'r semi_factor) entry \<Rightarrow> bool" where
  "entry_reads c e \<longleftrightarrow> fst (vsec (eview e)) \<sqsubseteq> c"

lemma contents_section:
  assumes E: "semilawful E" and F: "frame_reads c F" and K: "key_supp\<cdot>(kd E F) \<sqsubseteq> c"
    and gr: "\<And>e. e \<in> set (eguards E) \<Longrightarrow> key_supp\<cdot>(ekeys e) \<sqsubseteq> c \<and> guard_reads c (eguard e) \<and> kguard_reads c (ekguard e)"
    and cols: "\<And>e. e \<in> set (evalues E) \<Longrightarrow> entry_reads c e"
    and sec: "pts_section c data = pts_section c data'"
  shows "gcontents data (eguards E) F k = gcontents data' (eguards E) F k"
    and "contents data (evalues E) F k = contents data' (evalues E) F k"
proof -
  have G: "key_supp\<cdot>(sel_at S (flod F)) \<sqsubseteq> c" if "S \<in> set (esels E)" for S
    by (rule below_trans[OF key_supp_mono[OF group_below_kd[OF E that]] K])
  show "gcontents data (eguards E) F k = gcontents data' (eguards E) F k"
  proof (rule map_cong[OF refl])
    fix e assume e: "e \<in> set (eguards E)"
    have kc: "key_supp\<cdot>(ekeys e) \<sqsubseteq> c" and gc: "guard_reads c (eguard e)" and gk: "kguard_reads c (ekguard e)"
      using gr[OF e] by simp_all
    show "gcontent data e F k = gcontent data' e F k"
      unfolding fun_eq_iff gcontent_section[OF F G[OF esels_guardI[OF e]] kc gc gk] sec by simp
  qed
  show "contents data (evalues E) F k = contents data' (evalues E) F k"
  proof (rule map_cong[OF refl])
    fix e assume e: "e \<in> set (evalues E)"
    have r: "fst (vsec (eview e)) \<sqsubseteq> c" using cols[OF e] by (simp add: entry_reads_def)
    show "content data e F k = content data' e F k"
      unfolding content_section[OF G[OF esels_valueI[OF e]] r] sec ..
  qed
qed

text \<open>The \<^emph>\<open>grain\<close> of an expression at a frame joins the group LODs of its entries.  Contents, and
  so values, depend on the key only through its part at the grain: an expression emits at its
  grain, and its values at finer keys are broadcast.\<close>

definition grain :: "('k, 'f, 'r, 'v::bifinite, 'z) expr_scheme \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k semi_factor" where
  "grain E F = fold (\<squnion>) (map (\<lambda>S. sel_at S (flod F)) (esels E)) \<bottom>"

lemma group_below_grain: assumes "S \<in> set (esels E)" shows "sel_at S (flod F) \<sqsubseteq> grain E F"
  unfolding grain_def by (rule fold_join_upper) (use assms in force)

lemma grain_below_kd: "semilawful E \<Longrightarrow> grain E F \<sqsubseteq> kd E F"
  unfolding grain_def by (rule fold_join_least) (auto intro: group_below_kd)

theorem sem_grain:
  assumes E: "semilawful E" and d: "conforms data" and k: "proj (kd E F)\<cdot>k = k"
  shows "esem E data F k = esem E data F (proj (grain E F)\<cdot>k)"
proof (rule semilawful_content_law[OF E d d k])
  let ?k = "proj (grain E F)\<cdot>k"
  have at: "proj (sel_at S (flod F))\<cdot>?k = proj (sel_at S (flod F))\<cdot>k" if "S \<in> set (esels E)" for S
    by (rule proj_le[OF group_below_grain[OF that]])
  show "proj (kd E F)\<cdot>?k = ?k"
    by (rule proj_absorb[OF grain_below_kd[OF E]])
  show "gcontents data (eguards E) F k = gcontents data (eguards E) F ?k"
  proof (rule map_cong[OF refl])
    fix e assume e: "e \<in> set (eguards E)"
    show "gcontent data e F k = gcontent data e F ?k"
      using at[OF esels_guardI[OF e]] by (intro gcontent_fiber_cong) (simp_all add: fiber_def)
  qed
  show "contents data (evalues E) F k = contents data (evalues E) F ?k"
  proof (rule map_cong[OF refl])
    fix e assume e: "e \<in> set (evalues E)"
    show "content data e F k = content data e F ?k"
      using at[OF esels_valueI[OF e]] by (intro content_fiber_cong) (simp add: fiber_def)
  qed
qed

text \<open>For lawful expressions the frame LOD inside the minimal LOD does not matter: groups only see
  the key LOD.\<close>

lemma group_kd:
  "saturated E \<Longrightarrow> S \<in> set (esels E) \<Longrightarrow> sel_at S (flod F) = sel_at S (kd E F)"
  by (rule sat_absorb[symmetric, OF saturatedD])

lemma contents_kd:
  assumes E: "saturated E" and F: "amb F = amb F'" "slice F = slice F'" "kd E F = kd E F'"
  shows "gcontents data (eguards E) F k = gcontents data (eguards E) F' k"
    and "contents data (evalues E) F k = contents data (evalues E) F' k"
proof -
  show "gcontents data (eguards E) F k = gcontents data (eguards E) F' k"
  proof (rule map_cong[OF refl])
    fix e assume e: "e \<in> set (eguards E)"
    have "fiber data (elower e) (eupper e) F k = fiber data (elower e) (eupper e) F' k"
      by (rule fiber_cong) (simp_all only: group_kd[OF E esels_guardI[OF e]] F(3))
    then show "gcontent data e F k = gcontent data e F' k" by (rule gcontent_fiber_cong) (rule gtruth_cong[OF F(1,2)])
  qed
  show "contents data (evalues E) F k = contents data (evalues E) F' k"
  proof (rule map_cong[OF refl])
    fix e assume e: "e \<in> set (evalues E)"
    have "fiber data (elower e) (eupper e) F k = fiber data (elower e) (eupper e) F' k"
      by (rule fiber_cong) (simp_all only: group_kd[OF E esels_valueI[OF e]] F(3))
    then show "content data e F k = content data e F' k" by (rule content_fiber_cong)
  qed
qed

text \<open>Pegging the frame to a key does not change that key's contents: the pin's demand within
  a mask is true on the fiber already, by saturation; fibers do not see the slice at all.\<close>

lemma peg_fguard:
  assumes E: "saturated E" and S: "S \<in> set (esels E)" and cK: "compact K" and K: "proj (kd E F)\<cdot>K = K"
    and y: "y \<in> fiber data (lower_part S) (upper_part S) F K"
  shows "fguard (upper_part S) (peg K F)\<cdot>y = fguard (upper_part S) F\<cdot>y"
proof -
  let ?G = "sel_at S (flod F)" and ?T = "(upper_part S \<sqinter> kd E F)"
  have le: "?T \<sqsubseteq> ?G" unfolding group_kd[OF E S] by (rule lattice_join_ge2)
  have yG: "rproj ?G y = proj ?G\<cdot>K" using y by (simp add: fiber_def)
  have pin: "holds (coarsen (upper_part S) (spin K)) (row_key\<cdot>y)"
  proof -
    have "proj (upper_part S)\<cdot>K = proj ?T\<cdot>K" by (simp only: proj_inf K)
    also have "\<dots> = proj ?T\<cdot>(proj ?G\<cdot>K)" by (rule proj_le[OF le, symmetric])
    also have "\<dots> = proj ?T\<cdot>(rproj ?G y)" by (simp only: yG)
    also have "\<dots> = rproj ?T y" by (rule proj_le[OF le])
    finally have "proj (upper_part S)\<cdot>K \<sqsubseteq> row_key\<cdot>y" using proj_below[of ?T "row_key\<cdot>y"] by simp
    then show ?thesis by (rule holds_coarsen_spin[OF cK])
  qed
  show ?thesis using pin
    by (simp add: fguard_def gand_apply coarsen_conj guard_holds_conj guard_holds_apply holds_def)
qed

lemma peg_contents:
  assumes E: "saturated E" and cK: "compact K" and K: "proj (kd E F)\<cdot>K = K"
  shows "gcontents data (eguards E) (peg K F) K = gcontents data (eguards E) F K"
    and "contents data (evalues E) (peg K F) K = contents data (evalues E) F K"
proof -
  show "gcontents data (eguards E) (peg K F) K = gcontents data (eguards E) F K"
  proof (rule map_cong[OF refl])
    fix e assume e: "e \<in> set (eguards E)"
    show "gcontent data e (peg K F) K = gcontent data e F K"
    proof -
      have fp: "fiber data (elower e) (eupper e) (peg K F) K = fiber data (elower e) (eupper e) F K"
        by (simp add: fiber_def)
      have pf: "fguard (eupper e) (peg K F)\<cdot>y = fguard (eupper e) F\<cdot>y" if "y \<in> fiber data (elower e) (eupper e) F K" for y
        by (rule peg_fguard[OF E esels_guardI[OF e] cK K that])
      show ?thesis unfolding fun_eq_iff gcontent_def gfiber_def fp
        by (intro allI gex_cong[OF refl]) (simp add: gtruth_split pf)
    qed
  qed
  show "contents data (evalues E) (peg K F) K = contents data (evalues E) F K"
    by (rule map_cong[OF refl]) (simp add: content_def cgraph_def vfiber_def fiber_def)
qed

text \<open>The effective-LOD law: the frame LOD matters only through the key LOD.\<close>

theorem eff_law:
  assumes E: "semilawful E" "saturated E" and d: "conforms data"
    and F: "amb F = amb F'" "slice F = slice F'" "kd E F = kd E F'" and k: "proj (kd E F)\<cdot>k = k"
  shows "esem E data F k = esem E data F' k"
proof -
  have "proj (kd E F')\<cdot>k = k" using k by (simp add: F(3))
  then show ?thesis by (rule semilawful_content_law[OF E(1) d d k _ contents_kd[OF E(2) F]])
qed

text \<open>The peg law: pegging the frame to a key does not change the value there.\<close>

theorem peg_law:
  assumes E: "semilawful E" "saturated E" and d: "conforms data" and cK: "compact K" and K: "proj (kd E F)\<cdot>K = K"
  shows "esem E data (peg K F) K = esem E data F K"
proof -
  have "proj (kd E (peg K F))\<cdot>K = K" using K by simp
  then show ?thesis by (rule semilawful_content_law[OF E(1) d d _ K peg_contents[OF E(2) cK K]])
qed

text \<open>Locality: the semantics at a frame depends on the dataset only through its point section at
  a section covering the frame, the key LOD and what the entries read.\<close>

theorem sem_section:
  assumes E: "semilawful E" and d: "conforms data" and d': "conforms data'"
    and F: "frame_reads c F" and K: "key_supp\<cdot>(kd E F) \<sqsubseteq> c"
    and gr: "\<And>e. e \<in> set (eguards E) \<Longrightarrow> key_supp\<cdot>(ekeys e) \<sqsubseteq> c \<and> guard_reads c (eguard e) \<and> kguard_reads c (ekguard e)"
    and cols: "\<And>e. e \<in> set (evalues E) \<Longrightarrow> entry_reads c e"
    and sec: "pts_section c data = pts_section c data'" and k: "proj (kd E F)\<cdot>k = k"
  shows "esem E data F k = esem E data' F k"
  by (rule semilawful_content_law[OF E d d' k k contents_section[OF E F K gr cols sec]])

end

subsection \<open>Lemmas for the combinators\<close>

lemma proj_sup_eq:
  "proj (a \<squnion> b)\<cdot>x = proj (a \<squnion> b)\<cdot>z \<longleftrightarrow> proj a\<cdot>x = proj a\<cdot>z \<and> proj b\<cdot>x = proj b\<cdot>z"
proof
  assume e: "proj (a \<squnion> b)\<cdot>x = proj (a \<squnion> b)\<cdot>z"
  show "proj a\<cdot>x = proj a\<cdot>z \<and> proj b\<cdot>x = proj b\<cdot>z"
    using arg_cong[OF e, of "Rep_cfun (proj a)"] arg_cong[OF e, of "Rep_cfun (proj b)"]
    by (simp add: proj_le lattice_join_ge1 lattice_join_ge2)
qed (simp add: proj_sup)


context dataspace
begin

text \<open>The fiber of the full mask on top of an LOD is the key's own fiber; it is populated unless the
  key is not realised by a row the frame's filter does not reject.\<close>

lemma fiber_top:
  assumes "proj (c \<squnion> flod F)\<cdot>k = k"
  shows "fiber data c \<top> F k = {y \<in> lower_maximal data. rproj (c \<squnion> flod F) y = k}"
  using assms by (simp add: fiber_def truncate_top)

lemma keyimg_populated_top:
  assumes "proj (c \<squnion> flod F)\<cdot>k = k"
  shows "keyimg data F (c \<squnion> flod F) k \<longleftrightarrow> populated data c \<top> F k \<noteq> FF"
  by (auto simp: populated_def kleene_bex_not_FF fiber_top[OF assms] keyimg_def)

end

end
