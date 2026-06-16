theory Repro2 imports Main begin

(* this sort assignment fails (ord incompatible with default sort type), I am not sure why *)
class order_chain = order +
  assumes "\<exists>x::(nat\<Rightarrow>'a::ord). \<forall>i. x i \<le> x (Suc i)"

(* However if we make local copies of type classes, the same thing succeeds *)
class ord2 =
  fixes less_eq2 :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and less2 :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

notation
  less_eq2  (\<open>'(\<le>2')\<close>) and
  less_eq2  (\<open>(\<open>notation=\<open>infix \<le>\<close>\<close>_/ \<le>2 _)\<close>  [51, 51] 50) and
  less2  (\<open>'(<2')\<close>) and
  less2  (\<open>(\<open>notation=\<open>infix <\<close>\<close>_/ <2 _)\<close>  [51, 51] 50)
end

class preorder2 = ord2 +
  assumes less_le2_not_le2: "x <2 y \<longleftrightarrow> x \<le>2 y \<and> \<not> (y \<le>2 x)"
  and order2_refl [iff]: "x \<le>2 x"
  and order2_trans: "x \<le>2 y \<Longrightarrow> y \<le>2 z \<Longrightarrow> x \<le>2 z"
begin

lemma order2_le_trans: "x <2 y \<Longrightarrow> y <2 z \<Longrightarrow> x <2 z"
  unfolding less_le2_not_le2
  using order2_trans by blast
end

class order2 = preorder2 +
  assumes order2_antisym: "x \<le>2 y \<Longrightarrow> y \<le>2 x \<Longrightarrow> x = y"

class order2_chain = order2 +
  assumes "\<exists>x::(nat\<Rightarrow>'a::preorder2). \<forall>i. x i \<le>2 x (Suc i)"
begin
(* We have succeeded, but the local context is weird: local facts now refer to e.g.
locale fixed variable less_eq2, which is distinct from polymorphic constant less_eq2 *)
lemma "x \<le>2 y \<Longrightarrow> y \<le>2 z \<Longrightarrow> x \<le>2 z" by (fact order2_trans) (* fails *)
lemma "x \<le>2 y \<Longrightarrow> y \<le>2 z \<Longrightarrow> x \<le>2 z" by (fact preorder2_class.order2_trans) (*succeeds*)
end

(* Weirdly this works with base classes but with superclass ord (because it has no axioms maybe?)
*)
class order_chain_higher_sort = ord +
  assumes "\<exists>x::(nat\<Rightarrow>'a::order). \<forall>i. x i \<le> x (Suc i)"

end