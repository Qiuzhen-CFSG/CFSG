module

public import Theory.GroupTheory.CComponent.PrimeGroupOvergroup

/-!
# Exhaustion by a component orbit

If a C-component and a p-subgroup generate a finite group, the conjugate
span has p-group quotient. Every C-component lies in that span by perfectness.
A component outside the given orbit would centralize every orbit factor,
when distinct components commute, and therefore centralize itself.

Source: the orbit argument in Aschbacher–Smith, A.3.8(3), printed p.45.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
theorem IsCComponent.conjugate_of_pGroup_generated_of_commuting
    {X B S : Subgroup G} (hX : X.IsCComponent) (hB : B.IsCComponent)
    (hS : IsPGroup p S) (hgen : X ⊔ S = ⊤)
    (hc : ∀ C : Subgroup G, C.IsCComponent → B ≠ C → ⁅B,C⁆ = ⊥) :
    ∃ s : S, B = X.map (MulAut.conj (s : G)).toMonoidHom := by
  classical
  by_contra! hn
  let D := componentOrbit X S
  let : D.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact (normal_subgroupOf_iff_le_normalizer (componentOrbit_le_sup X S)).mp
      (componentOrbit_normal_subgroupOf_sup X S)
  let : Group.IsNilpotent (G ⧸ D) :=
    (isPGroup_quotient_of_sup_eq_top D S hS ((componentOrbit_sup X S).trans hgen)).isNilpotent
  let : Group.IsPerfect B := hB.perfect
  have hBD : B ≤ D :=
    (le_solvableResidual_of_isPerfect B).trans (solvableResidual_le_of_solvable_quotient D)
  have hDC : D ≤ centralizer (B : Set G) := by
    apply iSup_le
    intro s
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (hc _ (hX.map_equiv (MulAut.conj (s : G))) (hn s)))
  exact hB.ne_bot ((commutator_eq_self (H := B)).symm.trans
    (commutator_eq_bot_iff_le_centralizer.mpr (hBD.trans hDC)))
end Subgroup
