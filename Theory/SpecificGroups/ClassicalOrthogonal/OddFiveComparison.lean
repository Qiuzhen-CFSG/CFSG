/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
See also LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.OddFiveComparison.Kernel
public import Theory.SpecificGroups.ClassicalOrthogonal.OddFiveComparison.Surjectivity
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Basic

/-!
# The actual odd-five orthogonal and symplectic-four comparison

The exterior-square action has exactly the literal Siegel-generated group
as image and the matrix symplectic center as kernel. The first isomorphism
theorem identifies that image with PSp₄. Grün's lemma and the already proved
perfectness of Sp₄ over finite odd fields show that the image has trivial
center. Thus its original scalar quotient is the same group.

The resulting equivalence retains the actual exterior action on every
matrix lift. No order comparison or orthogonal simplicity theorem is used.
The quotient construction adapts ATLAS's
`LinearGroups/Orthogonal/B2ExteriorComparison.lean`, replacing its order
argument by explicit Siegel lifts and retaining CFSG's concrete carriers.

Source: GLS3 §2.7; Aschbacher–Smith A.2.17, printed pp.38–39.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.OddFiveComparison
open Matrix.PSp4Three
variable {F : Type} [Field F]

/-- Restricting the codomain leaves the already computed kernel unchanged. -/
theorem toElementary_kernel (h2 : (2 : F) ≠ 0) :
    (toElementary (F := F)).ker = Subgroup.center (Sp 2 F) := by
  ext g
  change toElementary g = 1 ↔ g ∈ Subgroup.center (Sp 2 F)
  rw [← toOrthogonal_eq_one_iff_center h2 g]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- The first isomorphism theorem applied to the actual exterior-square map. -/
def pspEquivElementary (h2 : (2 : F) ≠ 0) :
    PSp 2 F ≃* OmegaOdd 2 F :=
  (QuotientGroup.quotientMulEquivOfEq (toElementary_kernel h2).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (toElementary (F := F))
      (toElementary_surjective))

/-- The equivalence retains the actual matrix action on each lift. -/
theorem pspEquivElementary_projection (h2 : (2 : F) ≠ 0)
    (g : Sp 2 F) :
    pspEquivElementary h2 (QuotientGroup.mk g) = toElementary g :=
  rfl

variable [Finite F]

private theorem symplectic_perfect (h2 : (2 : F) ≠ 0) : Group.IsPerfect (Sp 2 F) := by
  apply Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.perfect
  let := Fintype.ofFinite F
  have hcard : 1 < Nat.card F := by
    simpa only [Nat.card_eq_fintype_card] using Fintype.one_lt_card (α := F)
  have hne : Nat.card F ≠ 2 := by
    intro hc
    have hc' : Fintype.card F = 2 := by simpa only [Nat.card_eq_fintype_card] using hc
    let : CharP F 2 := charP_of_card_eq_prime hc'
    exact h2 CharTwo.two_eq_zero
  omega

/-- No nonidentity scalar survives in the elementary image over a finite odd field. -/
theorem elementaryScalarSubgroup_eq_bot (h2 : (2 : F) ≠ 0) :
    elementaryScalarSubgroup (formB 2 F) = ⊥ := by
  let := symplectic_perfect h2
  let e := pspEquivElementary h2
  apply le_antisymm ?_ bot_le
  intro z hz
  have hz' := elementaryScalarSubgroup_le_center (formB 2 F) hz
  have hc : e.symm z ∈ Subgroup.center (PSp 2 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply e.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using
      (Subgroup.mem_center_iff.mp hz') (e g)
  rw [Group.IsPerfect.center_quotient_center_eq_bot, Subgroup.mem_bot] at hc
  rw [Subgroup.mem_bot]
  apply e.symm.injective
  simpa only [map_one] using hc

/-- The genuine B₂/C₂ comparison, retaining exactly the original orthogonal scalar quotient. -/
def projectiveEquivPSp (h2 : (2 : F) ≠ 0) :
    POmegaOdd 2 F ≃* ((Matrix.symplecticGroup (Fin 2) F) ⧸
      Subgroup.center (Matrix.symplecticGroup (Fin 2) F)) :=
  ((QuotientGroup.quotientMulEquivOfEq (elementaryScalarSubgroup_eq_bot h2)).trans
    QuotientGroup.quotientBot).trans (pspEquivElementary h2).symm

/-- The projective comparison agrees with the original matrix quotient on all lifts. -/
theorem projectiveEquivPSp_projection (h2 : (2 : F) ≠ 0)
    (g : Sp 2 F) :
    projectiveEquivPSp h2
      (projectiveElementaryMap _ (toElementary g)) = QuotientGroup.mk g := by
  change (pspEquivElementary h2).symm
    (pspEquivElementary h2 (QuotientGroup.mk g)) = _
  exact MulEquiv.symm_apply_apply _ _

end ClassicalOrthogonal.OddFiveComparison
