module
public import Theory.GroupTheory.SubgroupPartitionCounting
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Tactic.Group
/-! # Choosing a plane-moving square
A moved subgroup supplies a new outside normalizer element whose square
escapes it. Centralizing-factor absorption and the index-two cardinal bound
supply the local normalizer contradiction for the remaining invariant case.
Source: Aschbacher--Smith 2.5.7, printed p.556.
-/
public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
theorem exists_square_escape_of_moved_subgroup
    (N S T:Subgroup G) (hNS:N≤S) (hST:S≤T)
    (x:G) (hxT:x∈T) (hxS:x∉S) (hx:x∈normalizer (S:Set G))
    (hx2:x^2∈S) (hm:x∉normalizer (N:Set G)) :
    ∃y:G,y∈T ∧ y∉S ∧ y∈normalizer (S:Set G) ∧ y^2∈S ∧ y^2∉N := by
  by_cases hxn:x^2∈N
  · have hnot:¬N.conjBy x≤N:=by
      intro h
      have he:N.conjBy x=N:=eq_of_le_of_card_ge h (by
        change Nat.card N≤Nat.card (N.map (MulAut.conj x).toMonoidHom)
        rw [card_map_of_injective (MulAut.conj x).injective])
      exact hm (mem_normalizer_iff_map_conj_eq.mpr he)
    obtain ⟨b,hb,hbn⟩:=SetLike.not_le_iff_exists.mp hnot
    obtain ⟨a,ha,rfl⟩:=hb
    have haS:a∈S:=hNS ha
    have he:(a*x)^2=a*(x*a*x⁻¹)*x^2:=by simp only [pow_two];group
    refine ⟨a*x,T.mul_mem (hST haS) hxT,?_,?_,?_,?_⟩
    · intro hy
      exact hxS (S.mul_mem_cancel_left haS |>.mp hy)
    · exact (normalizer (S:Set G)).mul_mem (S.le_normalizer haS) hx
    · rw [he]
      exact S.mul_mem (S.mul_mem haS ((hx a).mp haS)) hx2
    · intro hy
      rw [he] at hy
      exact hbn (N.mul_mem_cancel_left ha |>.mp (N.mul_mem_cancel_right hxn |>.mp hy))
  · exact ⟨x,hxT,hxS,hx,hx2,hxn⟩
end Subgroup
namespace Subgroup
variable {G:Type*} [Group G]
theorem normalizes_intermediate_of_centralizing_factor
    (X V C I:Subgroup G) (hVX:V≤X) (hXV:X≤normalizer (V:Set G))
    (hCX:C≤centralizer (X:Set G)) (hVI:V≤I) (hIC:I≤V⊔C) :
    X≤normalizer (I:Set G) := by
  have hVC:V≤centralizer (C:Set G):=hVX.trans (le_centralizer_iff.mp hCX)
  apply le_normalizer_iff.mpr
  intro x hx t ht
  have hmem:t∈(V:Set G)*(C:Set G):=by
    rw [←coe_mul_of_left_le_normalizer_right V C (hVC.trans (centralizer_le_normalizer _))]
    exact hIC ht
  obtain ⟨v,hv,c,hc,rfl⟩:=hmem
  have hcI:c∈I:=by
    have hh:=I.mul_mem (I.inv_mem (hVI hv)) ht
    simpa only [inv_mul_cancel_left] using hh
  have hxv:x*v*x⁻¹∈I:=hVI ((hXV hx v).mp hv)
  have hxc:x*c*x⁻¹=c:=by rw [hCX hc x hx,mul_inv_cancel_right]
  have he:x*(v*c)*x⁻¹=(x*v*x⁻¹)*(x*c*x⁻¹):=by group
  rw [he,hxc]
  exact I.mul_mem hxv hcI

theorem card_le_adjoin_of_relIndex_le_two [Finite G]
    (N S:Subgroup G) (hNS:N≤S) (hi:N.relIndex S≤2) (x:G) (hx:x∉S) :
    Nat.card S≤Nat.card (N⊔zpowers x:Subgroup G) := by
  let U:=N⊔zpowers x
  have hne:N.relIndex U≠1:=by
    intro he
    have hUN:U≤N:=relIndex_eq_one.mp he
    exact hx (hNS (hUN (mem_sup_right (mem_zpowers x))))
  have hn:N.relIndex U≠0:=index_ne_zero_of_finite
  have htwo:2≤N.relIndex U:=by omega
  rw [←relIndex_mul_card_of_le hNS,←relIndex_mul_card_of_le (show N≤U from le_sup_left)]
  exact Nat.mul_le_mul_right _ (hi.trans htwo)
end Subgroup
