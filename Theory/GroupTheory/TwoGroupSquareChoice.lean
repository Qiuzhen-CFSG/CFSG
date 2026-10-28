module
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Nilpotent
/-! # An outside normalizer element with square in a proper two-subgroup
The normalizer condition and the first power of two entering the subgroup
produce the initial crossing actor. Source application: Aschbacher--Smith
2.5.7, printed p.556.
-/
public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
theorem exists_outside_normalizer_square_mem
    (S T:Subgroup G) (hT:IsPGroup 2 T) (hST:S<T) :
    ∃x:G,x∈T ∧ x∉S ∧ x∈normalizer (S:Set G) ∧ x^2∈S := by
  classical
  let : Group.IsNilpotent T:=hT.isNilpotent
  have hproper:S.subgroupOf T<⊤:=by
    rw [lt_top_iff_ne_top,Ne,subgroupOf_eq_top]
    exact hST.not_ge
  have ht:=Group.normalizerCondition_of_isNilpotent (S.subgroupOf T) hproper
  obtain ⟨a,ha,hout⟩:=SetLike.exists_of_lt ht
  rw [←subgroupOf_normalizer_eq hST.le] at ha
  have hnot:(a:G)∉S:=hout
  have he:∃n:ℕ,(a:G)^(2^n)∈S:=by
    obtain ⟨n,hn⟩:=hT.exists_pow_pow_eq_one a
    exact ⟨n,by rw [←Subgroup.coe_pow,hn,Subgroup.coe_one];exact S.one_mem⟩
  let n:=Nat.find he
  have hn:(a:G)^(2^n)∈S:=Nat.find_spec he
  have hnpos:0<n:=by
    by_contra h
    have hn0:n=0:=by omega
    rw [hn0,pow_zero,pow_one] at hn
    exact hnot hn
  refine ⟨(a:G)^(2^(n-1)),T.pow_mem a.property _,?_,(normalizer (S:Set G)).pow_mem ha _,?_⟩
  · exact Nat.find_min he (by omega)
  · rw [←pow_mul,←pow_succ,show n-1+1=n by omega]
    exact hn
end Subgroup
