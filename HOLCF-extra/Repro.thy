theory Repro imports HOLCF begin
default_sort type

thm po.is_ubI
thm po_class.is_ubI

(* the trick works with a HOLCF class *)
class holcf = pcpo + assumes "\<exists>(a::(nat\<Rightarrow>'a)). chain a"
begin
typ 'a (* 'a::cpo *)
(*theorem borked*)
thm below_refl
thm is_ubI (*(\<And>x. x \<in> ?S \<Longrightarrow> below x ?u) \<Longrightarrow> po.is_ub below ?S ?u*)
end


(*but doesn't work with a HOL class *)
class hol = linorder +
  assumes "\<exists>(a :: (nat\<Rightarrow>'a)). mono a"
(*error "Sort constraint order inconsistent with default type for type variable "'a"*)

(* this works fine and outputs class hol2 = order + ... *)
class hol2 = ord +
  assumes "\<exists>(a :: (nat\<Rightarrow>'a::order)). mono a"

(* this also produces an error *)
class hol3 = order +
  assumes "\<exists>(a :: (nat\<Rightarrow>'a)). mono a"

end