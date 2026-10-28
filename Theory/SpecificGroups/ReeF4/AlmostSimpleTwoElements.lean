module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms
public import Theory.GroupTheory.PerfectCentralCoverOuter
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.ElementaryAbelian.Basic

/-!
# Two-elements above a Ree component

For the simple-range Ree carrier every two-power automorphism is inner.
Innerness lifts from the actual central quotient of a perfect component.
Self-centralization of the generalized Fitting subgroup then places every
ambient two-element in that component. Odd outer actions remain allowed.

This proves the outer-action reduction in Guralnick--Malle, *Classification
of 2F-modules, II*, Lemma 8.8, internal pp.57--58, for every central cover.
It uses neither a multiplier calculation nor a module classification.
-/

public section

namespace ReeF4
open Subgroup Theory.GroupTheory

variable {H : Type*} [Group H] [Finite H] (N : Subgroup H)
  [N.Normal] [Group.IsPerfect N]

/-- Two-elements of an ambient group with Ree generalized Fitting subgroup
belong to that subgroup, including when it is a central cover. -/
theorem twoPower_mem_of_generalizedFitting {m : ℕ} (hm : 1 ≤ m)
    (hF : generalizedFitting H = N) (e : N ⧸ center N ≃* Model m)
    (x : H) (r : ℕ) (hx : x ^ (2 ^ r) = 1) : x ∈ N := by
  let a : MulAut N := MulAut.conjNormal x
  have ha : a ^ (2 ^ r) = 1 := by
    change (MulAut.conjNormal x) ^ (2 ^ r) = 1
    rw [← map_pow, hx, map_one]
  have hqa : MulAut.centralQuotientAction e a ^ (2 ^ r) = 1 := by
    rw [← map_pow, ha, map_one]
  obtain ⟨y, hy⟩ := Parabolics.OuterLocal.LargeAutomorphisms.inner_of_twoPower
    hm (MulAut.centralQuotientAction e a) r hqa
  obtain ⟨n, hn⟩ := (MulAut.centralQuotientAction_inner_iff e a).mp ⟨y, hy.symm⟩
  have hinner : a ∈ MulAut.innerSubgroup N := ⟨n, hn.symm⟩
  change x ∈ (MulAut.innerSubgroup N).comap MulAut.conjNormal at hinner
  rw [MulAut.conjNormal_comap_innerSubgroup] at hinner
  have hC : centralizer (N : Set H) ≤ N := by
    simpa only [hF] using centralizer_generalizedFitting_le H
  simpa only [sup_eq_left.mpr hC] using hinner

/-- In particular every elementary two-subgroup is an actual subgroup of N. -/
theorem elementary_le_of_generalizedFitting {m : ℕ} (hm : 1 ≤ m)
    (hF : generalizedFitting H = N) (e : N ⧸ center N ≃* Model m)
    (A : Subgroup H) [IsElementaryAbelian 2 A] : A ≤ N := by
  intro x hx
  exact twoPower_mem_of_generalizedFitting N hm hF e x 1
    (by simpa only [pow_one] using elemPow_eq_one_of_isElementaryAbelian x hx)

end ReeF4
