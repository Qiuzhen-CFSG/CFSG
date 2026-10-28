module
public import Theory.GroupTheory.SemidihedralCyclicHall
public import Theory.SpecificGroups.Classical.SylowMarkedSL2.SemidihedralControl
/-!
# Cyclic odd Hall control of a marked SL₂(5)

An automorphism preserving a solvable intersection with a cyclic odd Hall
subgroup fixes the central involution of its full semidihedral Sylow.
Recovering the marked SL₂(5) as the derived involution centralizer then
proves normalization. The automorphism need not preserve the chosen Sylow.

Source: Aschbacher--Smith A.3.21(a) and 5.1.13, printed pp.55,636.
-/
public noncomputable section
open Subgroup

open scoped MatrixGroups
namespace Theory.SpecificGroups.Classical.SylowMarkedSL2
/-- A solvable intersection with a cyclic odd Hall subgroup and full
semidihedral Sylow subgroup preserves its marked SL₂(5). -/
theorem automorphism_preserves_sl2_five_of_cyclic_odd_hall
    {Y F : Type*} [Group Y] [Finite Y] [Field F] [Finite F]
    (hgens : ∀ S : Sylow 2 Y, ∃ a b : S, orderOf a = 8 ∧ orderOf b = 2 ∧
      b*a*b⁻¹=a^3 ∧ closure ({a,b} : Set S)=⊤)
    (hbound : ∀ z : Y, orderOf z = 2 →
      Nat.card (commutator (centralizer ({z} : Set Y))) ≤ 120)
    (R J : Subgroup Y) (eR : R ≃* SL(2,F)) (hF : Nat.card F = 5)
    (S : Sylow 2 Y) (hSR : (S : Subgroup Y) ≤ normalizer (R : Set Y))
    (hSJ : (S : Subgroup Y) ≤ J) (hs : Group.IsSolvable J)
    (D : Subgroup J) [IsCyclic D] (hD : IsHallSubgroup OddHall.oddPrimes D)
    (φ : MulAut Y) (hJ : J.map φ.toMonoidHom = J) : R.map φ.toMonoidHom = R := by
  let Q := S.subtype hSJ
  let e : Q ≃* S := subgroupOfEquivOfLe hSJ
  obtain ⟨a,b,ha,hb,hab,hg⟩ := hgens S
  let a' := e.symm a
  let b' := e.symm b
  have ha' : orderOf a' = 8 := (e.symm.orderOf_eq a).trans ha
  have hb' : orderOf b' = 2 := (e.symm.orderOf_eq b).trans hb
  have hab' : b'*a'*b'⁻¹=a'^3 := by
    simpa only [a',b',map_mul,map_inv,map_pow] using congrArg e.symm hab
  have hg' : closure ({a',b'} : Set Q)=⊤ := by
    have hh := congrArg (map e.symm.toMonoidHom) hg
    rw [MonoidHom.map_closure,map_top_of_surjective _ e.symm.surjective] at hh
    simpa only [Set.image_insert_eq,Set.image_singleton, MulEquiv.coe_toMonoidHom] using hh
  let ψ : MulAut J := (J.equivMapOfInjective φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr hJ)
  have hh := Semidihedral.automorphism_fix_fourth_of_cyclic_odd_hall hs D hD Q a' b' ha' hb' hab' hg' ψ
  have hfix : φ ((a : Y)^4)=(a : Y)^4 := congrArg J.subtype hh
  exact Theory.SpecificGroups.Classical.SylowMarkedSL2.automorphism_preserves_sl2_five_of_fix_fourth
    hbound R eR hF S hSR a b ha hb hab hg φ hfix
end Theory.SpecificGroups.Classical.SylowMarkedSL2
