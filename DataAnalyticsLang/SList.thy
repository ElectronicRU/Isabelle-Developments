theory SList
  imports Domain_Transfer
begin

section \<open>Strict-tail lists: a recursive test case for instance derivation\<close>

domain ('v::"domain") slist = SNil | SCons (lazy 'v) "'v slist"

subsection \<open>Map equations\<close>

lemma slist_map_strict [simp]: "slist_map\<cdot>f\<cdot>\<bottom> = \<bottom>"
  by (subst slist_map_unfold) simp

lemma slist_map_SNil [simp]: "slist_map\<cdot>f\<cdot>SNil = SNil"
  by (subst slist_map_unfold) (simp add: SNil_def slist.abs_iso)

lemma slist_map_SCons [simp]: "l \<noteq> \<bottom> \<Longrightarrow> slist_map\<cdot>f\<cdot>(SCons\<cdot>v\<cdot>l) = SCons\<cdot>(f\<cdot>v)\<cdot>(slist_map\<cdot>f\<cdot>l)"
  by (subst slist_map_unfold) (simp add: SCons_def slist.abs_iso)

lemma slist_map_bottom_iff [simp]: "slist_map\<cdot>f\<cdot>l = \<bottom> \<longleftrightarrow> l = \<bottom>"
  by (induct l rule: slist.induct) simp_all

lemma "OFCLASS('v::{domain, bounded_complete} slist, bounded_complete_class)"
  apply (rule bounded_complete_iterateI[OF slist.chain_take slist.lub_take slist.take_def])
  apply (rule preserves_LAM, intro cont2cont)
  apply (rule lubs_on_iso)
   apply (rule iso.intro, rule slist.abs_iso, rule slist.rep_iso)
  apply (intro lubs_on_ssum_map lubs_on_sprod_map lubs_on_ID)
  apply assumption
  done

lemma "OFCLASS('v::domain slist, separated_po_class)"
  apply (rule separated_po_iterateI[OF slist.chain_take slist.lub_take slist.take_def])
  apply (rule preserves_LAM, intro cont2cont)
  apply (rule sep_on_iso)
   apply (rule iso.intro, rule slist.abs_iso, rule slist.rep_iso)
  apply (intro sep_on_ssum_map sep_on_sprod_map sep_on_u_map sep_on_ID)
  apply assumption
  done

domain ('v::"domain") lstream = LSCons (lazy 'v) (lazy "'v lstream")

lemma "OFCLASS('v::{domain, bounded_complete} lstream, bounded_complete_class)"
  apply (rule bounded_complete_iterateI[OF lstream.chain_take lstream.lub_take lstream.take_def])
  apply (rule preserves_LAM, intro cont2cont)
  apply (rule lubs_on_iso)
   apply (rule iso.intro, rule lstream.abs_iso, rule lstream.rep_iso)
  apply (intro lubs_on_sprod_map lubs_on_u_map lubs_on_ID)
  apply assumption
  done

lemma "OFCLASS('v::domain lstream, separated_po_class)"
  apply (rule separated_po_iterateI[OF lstream.chain_take lstream.lub_take lstream.take_def])
  apply (rule preserves_LAM, intro cont2cont)
  apply (rule sep_on_iso)
   apply (rule iso.intro, rule lstream.abs_iso, rule lstream.rep_iso)
  apply (intro sep_on_sprod_map sep_on_u_map sep_on_ID)
  done

subsection \<open>Bounded completeness\<close>

lemma is_lub_pair_below: "a \<sqsubseteq> b \<Longrightarrow> {a, b} <<| b"
  by (auto intro: is_lubI is_ubI dest: is_ubD)

lemma comparable_lub: "a \<sqsubseteq> b \<or> b \<sqsubseteq> a \<Longrightarrow> \<exists>z. {a, b} <<| z"
  by (metis insert_commute is_lub_pair_below)

lemma below_SNil_iff: "a \<sqsubseteq> SNil \<longleftrightarrow> a = \<bottom> \<or> a = SNil"
  by (cases a rule: slist.exhaust) simp_all

lemma below_SCons_iff: "m \<noteq> \<bottom> \<Longrightarrow> x \<sqsubseteq> SCons\<cdot>w\<cdot>m \<longleftrightarrow>
    x = \<bottom> \<or> (\<exists>w' m'. x = SCons\<cdot>w'\<cdot>m' \<and> m' \<noteq> \<bottom> \<and> w' \<sqsubseteq> w \<and> m' \<sqsubseteq> m)"
  by (cases x rule: slist.exhaust) auto

lemma SCons_below_iff: "m \<noteq> \<bottom> \<Longrightarrow> SCons\<cdot>w\<cdot>m \<sqsubseteq> u \<longleftrightarrow>
    (\<exists>w' m'. u = SCons\<cdot>w'\<cdot>m' \<and> m' \<noteq> \<bottom> \<and> w \<sqsubseteq> w' \<and> m \<sqsubseteq> m')"
  by (cases u rule: slist.exhaust) auto

lemma slist_bounded_lub:
  fixes a b c :: "'v::{domain, bounded_complete} slist"
  assumes "a \<sqsubseteq> c" "b \<sqsubseteq> c" shows "\<exists>z. {a, b} <<| z"
  using assms
proof (induct c arbitrary: a b rule: slist.induct)
  case 1
  then show ?case by (intro comparable_lub) simp
next
  case 2
  then show ?case by (intro comparable_lub) (auto simp: below_SNil_iff)
next
  case (3 v l)
  show ?case
  proof (cases "a = \<bottom> \<or> b = \<bottom>")
    case True then show ?thesis by (intro comparable_lub) auto
  next
    case False
    with 3(3,4) obtain va la vb lb where
      a: "a = SCons\<cdot>va\<cdot>la" "la \<noteq> \<bottom>" "va \<sqsubseteq> v" "la \<sqsubseteq> l" and
      b: "b = SCons\<cdot>vb\<cdot>lb" "lb \<noteq> \<bottom>" "vb \<sqsubseteq> v" "lb \<sqsubseteq> l"
      by (auto simp: below_SCons_iff[OF 3(1)])
    from 3(2)[OF a(4) b(4)] obtain z where z: "{la, lb} <<| z" by blast
    have vj: "{va, vb} <<| va \<squnion> vb" using a(3) b(3) by (rule join_is_lub)
    have lz: "la \<sqsubseteq> z" "lb \<sqsubseteq> z" using z by (auto dest: is_lubD1 is_ubD)
    with a(2) have zb: "z \<noteq> \<bottom>" by (auto simp: bottomI)
    have "{a, b} <<| SCons\<cdot>(va \<squnion> vb)\<cdot>z"
    proof (rule is_lubI)
      have "va \<sqsubseteq> va \<squnion> vb" "vb \<sqsubseteq> va \<squnion> vb" using vj by (auto dest: is_lubD1 is_ubD)
      with lz a b zb show "{a, b} <| SCons\<cdot>(va \<squnion> vb)\<cdot>z" by (auto intro!: is_ubI)
    next
      fix u assume u: "{a, b} <| u"
      then have "a \<sqsubseteq> u" "b \<sqsubseteq> u" by (auto dest: is_ubD)
      with a b obtain w m where wm: "u = SCons\<cdot>w\<cdot>m" "m \<noteq> \<bottom>" "va \<sqsubseteq> w" "la \<sqsubseteq> m" "vb \<sqsubseteq> w" "lb \<sqsubseteq> m"
        by (auto simp: SCons_below_iff)
      have "va \<squnion> vb \<sqsubseteq> w" using wm by (blast intro: is_lubD2[OF vj] is_ubI)
      moreover have "z \<sqsubseteq> m" using wm by (blast intro: is_lubD2[OF z] is_ubI)
      ultimately show "SCons\<cdot>(va \<squnion> vb)\<cdot>z \<sqsubseteq> u" using wm zb by simp
    qed
    then show ?thesis ..
  qed
qed

instance slist :: ("{domain, bounded_complete}") bounded_complete
  by (rule bounded_complete_finite_joinI) (rule slist_bounded_lub)

subsection \<open>Meets and joins\<close>

context
  fixes v w :: "'v::{domain, bounded_complete}" and l m :: "'v slist"
  assumes l: "l \<noteq> \<bottom>" and m: "m \<noteq> \<bottom>"
begin

lemma SCons_joinable_iff [simp]: "SCons\<cdot>v\<cdot>l \<Up> SCons\<cdot>w\<cdot>m \<longleftrightarrow> v \<Up> w \<and> l \<Up> m"
proof
  assume "SCons\<cdot>v\<cdot>l \<Up> SCons\<cdot>w\<cdot>m"
  then obtain u where "SCons\<cdot>v\<cdot>l \<sqsubseteq> u" "SCons\<cdot>w\<cdot>m \<sqsubseteq> u" unfolding joinable_def by blast
  then show "v \<Up> w \<and> l \<Up> m" using l m by (auto simp: SCons_below_iff intro: joinableI)
next
  assume "v \<Up> w \<and> l \<Up> m"
  then have "v \<sqsubseteq> v \<squnion> w" "w \<sqsubseteq> v \<squnion> w" "l \<sqsubseteq> l \<squnion> m" "m \<sqsubseteq> l \<squnion> m" by (auto dest: joinableD)
  moreover from this l have "l \<squnion> m \<noteq> \<bottom>" by (auto simp: bottomI)
  ultimately show "SCons\<cdot>v\<cdot>l \<Up> SCons\<cdot>w\<cdot>m"
    using l m by (intro joinableI[of _ "SCons\<cdot>(v \<squnion> w)\<cdot>(l \<squnion> m)"]) simp_all
qed

lemma SCons_join:
  assumes vw: "v \<Up> w" and lm: "l \<Up> m"
  shows "SCons\<cdot>v\<cdot>l \<squnion> SCons\<cdot>w\<cdot>m = SCons\<cdot>(v \<squnion> w)\<cdot>(l \<squnion> m)"
proof (rule below_antisym)
  have up: "v \<sqsubseteq> v \<squnion> w" "w \<sqsubseteq> v \<squnion> w" "l \<sqsubseteq> l \<squnion> m" "m \<sqsubseteq> l \<squnion> m"
    by (rule joinableD[OF vw])+ (rule joinableD[OF lm])+
  have lmb: "l \<squnion> m \<noteq> \<bottom>" using up(3) l by (auto dest: bottomI)
  show "SCons\<cdot>v\<cdot>l \<squnion> SCons\<cdot>w\<cdot>m \<sqsubseteq> SCons\<cdot>(v \<squnion> w)\<cdot>(l \<squnion> m)"
    by (rule join_belowI) (simp_all add: l m lmb up)
  have j: "SCons\<cdot>v\<cdot>l \<Up> SCons\<cdot>w\<cdot>m" using vw lm by simp
  then have h: "SCons\<cdot>v\<cdot>l \<sqsubseteq> SCons\<cdot>v\<cdot>l \<squnion> SCons\<cdot>w\<cdot>m" "SCons\<cdot>w\<cdot>m \<sqsubseteq> SCons\<cdot>v\<cdot>l \<squnion> SCons\<cdot>w\<cdot>m"
    by (rule joinableD)+
  from h(1) obtain j k where jk: "SCons\<cdot>v\<cdot>l \<squnion> SCons\<cdot>w\<cdot>m = SCons\<cdot>j\<cdot>k" "k \<noteq> \<bottom>" "v \<sqsubseteq> j" "l \<sqsubseteq> k"
    unfolding SCons_below_iff[OF l] by blast
  from h(2) have "w \<sqsubseteq> j" "m \<sqsubseteq> k" unfolding jk(1) using m jk(2) by simp_all
  with jk show "SCons\<cdot>(v \<squnion> w)\<cdot>(l \<squnion> m) \<sqsubseteq> SCons\<cdot>v\<cdot>l \<squnion> SCons\<cdot>w\<cdot>m"
    using lmb by (simp add: join_belowI)
qed

lemma SCons_meet:
  "SCons\<cdot>v\<cdot>l \<sqinter> SCons\<cdot>w\<cdot>m = (if l \<sqinter> m = \<bottom> then \<bottom> else SCons\<cdot>(v \<sqinter> w)\<cdot>(l \<sqinter> m))"
proof -
  let ?r = "SCons\<cdot>v\<cdot>l \<sqinter> SCons\<cdot>w\<cdot>m"
  have r: "?r \<sqsubseteq> SCons\<cdot>v\<cdot>l" "?r \<sqsubseteq> SCons\<cdot>w\<cdot>m" by (rule meet_below1, rule meet_below2)
  have shape: "?r = \<bottom> \<or> (\<exists>v' l'. ?r = SCons\<cdot>v'\<cdot>l' \<and> l' \<noteq> \<bottom> \<and> v' \<sqsubseteq> v \<sqinter> w \<and> l' \<sqsubseteq> l \<sqinter> m)"
    using r l m by (auto simp: below_SCons_iff intro: meet_greatest)
  show ?thesis
  proof (cases "l \<sqinter> m = \<bottom>")
    case True
    with shape show ?thesis by auto
  next
    case False
    have "SCons\<cdot>(v \<sqinter> w)\<cdot>(l \<sqinter> m) \<sqsubseteq> ?r"
      using False l m by (intro meet_greatest) (simp_all add: meet_below1 meet_below2)
    moreover have "?r \<sqsubseteq> SCons\<cdot>(v \<sqinter> w)\<cdot>(l \<sqinter> m)" using shape False by auto
    ultimately show ?thesis using False by (simp add: below_antisym)
  qed
qed

lemma SNil_SCons_meet [simp]: "SNil \<sqinter> SCons\<cdot>v\<cdot>l = \<bottom>" "SCons\<cdot>v\<cdot>l \<sqinter> SNil = \<bottom>"
  using l meet_below1[of SNil "SCons\<cdot>v\<cdot>l"] meet_below2[of SNil "SCons\<cdot>v\<cdot>l"]
    meet_below1[of "SCons\<cdot>v\<cdot>l" SNil] meet_below2[of "SCons\<cdot>v\<cdot>l" SNil]
  by (auto simp: below_SNil_iff below_SCons_iff)

lemma SNil_SCons_joinable [simp]: "\<not> SNil \<Up> SCons\<cdot>v\<cdot>l" "\<not> SCons\<cdot>v\<cdot>l \<Up> SNil"
  using l by (auto simp: joinable_def SCons_below_iff below_SNil_iff)

end

lemma join_bottom_iff [simp]:
  fixes a b :: "'a::bounded_complete"
  shows "a \<Up> b \<Longrightarrow> a \<squnion> b = \<bottom> \<longleftrightarrow> a = \<bottom> \<and> b = \<bottom>"
  by (metis joinableD bottomI join_absorbI minimal)

lemma SNil_meet_SNil [simp]: "(SNil :: 'v::{domain, bounded_complete} slist) \<sqinter> SNil = SNil"
  by (rule meet_absorbI) simp

text \<open>Joinable nonbottom lists have the same length, so they meet any third list to \<open>\<bottom>\<close> together.
  This is what keeps the smash product inside @{typ \<open>'v slist\<close>} distributive.\<close>

lemma slist_meet_bottom_cong:
  fixes x y z :: "'v::{domain, bounded_complete} slist"
  assumes "x \<Up> y" "x \<noteq> \<bottom>" "y \<noteq> \<bottom>" "z \<sqinter> x = \<bottom>" shows "z \<sqinter> y = \<bottom>"
  using assms
proof (induct z arbitrary: x y rule: slist.induct)
  case 1 then show ?case by simp
next
  case 2
  then show ?case
    by (cases x rule: slist.exhaust; cases y rule: slist.exhaust) simp_all
next
  case (3 v l)
  then show ?case
    by (cases x rule: slist.exhaust; cases y rule: slist.exhaust) (auto simp: SCons_meet split: if_splits)
qed

lemma slist_distrib:
  fixes a b c :: "'v::{domain, distributive_cpo} slist"
  assumes "a \<Up> b" shows "c \<sqinter> (a \<squnion> b) = c \<sqinter> a \<squnion> (c \<sqinter> b)"
  using assms
proof (induct c arbitrary: a b rule: slist.induct)
  case 1 then show ?case by simp
next
  case 2 then show ?case
    by (cases a rule: slist.exhaust; cases b rule: slist.exhaust)
      (simp_all add: join_absorbI SCons_join)
next
  case (3 v l)
  note l = 3(1) and IH = 3(2) and ab = 3(3)
  consider "a = \<bottom>" | "b = \<bottom>" | "a = SNil" "b = SNil"
    | va la vb lb where "a = SCons\<cdot>va\<cdot>la" "b = SCons\<cdot>vb\<cdot>lb" "la \<noteq> \<bottom>" "lb \<noteq> \<bottom>"
    using ab by (cases a rule: slist.exhaust; cases b rule: slist.exhaust) auto
  then show ?case
  proof cases
    case 1 then show ?thesis by (simp add: join_absorbI)
  next
    case 2 then show ?thesis by (simp add: join_absorbI meet_sym)
  next
    case 3 then show ?thesis using l by (simp add: join_absorbI)
  next
    case (4 va la vb lb)
    with ab have j: "va \<Up> vb" "la \<Up> lb" by simp_all
    have mjs: "x \<sqinter> y \<Up> x \<sqinter> z" for x y z :: "'v slist" by (rule joinableI[OF meet_below1 meet_below1])
    have mjv: "x \<sqinter> y \<Up> x \<sqinter> z" for x y z :: 'v by (rule joinableI[OF meet_below1 meet_below1])
    have lab: "la \<squnion> lb \<noteq> \<bottom>" using 4 j by simp
    have cong: "l \<sqinter> la = \<bottom> \<longleftrightarrow> l \<sqinter> lb = \<bottom>"
      using 4 j slist_meet_bottom_cong joinable_sym by metis
    have cong2: "l \<sqinter> (la \<squnion> lb) = \<bottom> \<longleftrightarrow> l \<sqinter> la = \<bottom>"
      using 4 j lab slist_meet_bottom_cong joinableD joinable_if_below1 joinable_sym by metis
    show ?thesis
    proof (cases "l \<sqinter> la = \<bottom>")
      case True
      with cong cong2 4 j l lab show ?thesis by (simp add: SCons_join SCons_meet)
    next
      case False
      with cong have F: "l \<sqinter> lb \<noteq> \<bottom>" by simp
      have "SCons\<cdot>v\<cdot>l \<sqinter> (a \<squnion> b) = SCons\<cdot>(v \<sqinter> va \<squnion> v \<sqinter> vb)\<cdot>(l \<sqinter> la \<squnion> l \<sqinter> lb)"
      proof -
        have nb: "l \<sqinter> la \<squnion> l \<sqinter> lb \<noteq> \<bottom>" using IH[OF j(2)] cong2 False by simp
        show ?thesis
          by (simp only: 4(1,2) SCons_join[OF 4(3,4) j] SCons_meet[OF l lab] nb
            if_False meet_join_distrib[OF j(1)] IH[OF j(2)])
      qed
      also have "\<dots> = SCons\<cdot>(v \<sqinter> va)\<cdot>(l \<sqinter> la) \<squnion> SCons\<cdot>(v \<sqinter> vb)\<cdot>(l \<sqinter> lb)"
        by (rule SCons_join[symmetric, OF False F mjv mjs])
      also have "\<dots> = (SCons\<cdot>v\<cdot>l \<sqinter> a) \<squnion> (SCons\<cdot>v\<cdot>l \<sqinter> b)"
        by (simp only: 4(1,2) SCons_meet[OF l 4(3)] SCons_meet[OF l 4(4)] False F if_False)
      finally show ?thesis .
    qed
  qed
qed

instance slist :: ("{domain, distributive_cpo}") distributive_cpo
  by intro_classes (rule slist_distrib)

end
