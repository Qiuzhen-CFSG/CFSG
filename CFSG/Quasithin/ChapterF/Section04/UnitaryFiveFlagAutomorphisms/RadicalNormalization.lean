module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.RadicalRigidity
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveFlagAutomorphisms.GraphCoefficient

/-!
# Radical scalars of the normalized native U₅(4) involution

The original residual quotient marking identifies the normalized actor's
SL₂ projection with the identity. Its restriction to the actual plane radical
has one nonzero scalar on vectors and the norm scalar on the entire center.
Retain the original involution's cocycle equation and the exact compatibility
with the moving Levi section. Full radical and opposite-endpoint rigidity
remain necessary to construct one unitary representative.

Source: Aschbacher–Smith F.4.29(2), printed p.289 of refs/quasithin.pdf.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitaryFiveFlagAutomorphisms
open Subgroup GreenBook.UnitaryFive Theory.SpecificGroups.UnitaryFive
variable (U : Model 4)

/-- The same plane-residual actor in its established semidirect coordinates. -/
def rightCoordinateAction : flagAutomorphisms U →* MulAut (PlaneCore.PlaneSemidirect U.form) :=
  (MulAut.congr (rightCoordinates U).symm).toMonoidHom.comp (rightLocalAction U)

theorem rightCoordinateAction_apply (a : flagAutomorphisms U) (p : PlaneCore.PlaneSemidirect U.form) :
    rightCoordinates U (rightCoordinateAction U a p) = rightLocalAction U a (rightCoordinates U p) := by
  change rightCoordinates U ((rightCoordinates U).symm
    (rightLocalAction U a (rightCoordinates U p))) = _
  exact (rightCoordinates U).apply_symm_apply _

/-- Quotient-triviality concerns the actual SL₂ projection, not a substitute marking. -/
theorem rightCoordinateAction_right (a : flagAutomorphisms U)
    (ha : rightLinearAction U a = 1) (p : PlaneCore.PlaneSemidirect U.form) :
    (rightCoordinateAction U a p).right = p.right := by
  apply Theory.PSL2.quotientMap_injective U.F
  rw [←rightQuotientProjection_coordinates, rightCoordinateAction_apply,
    rightQuotientProjection_action,ha,MulAut.one_apply,rightQuotientProjection_coordinates]

/-- Restriction of this same native actor to the characteristic plane radical. -/
def rightRadicalAction (a : flagAutomorphisms U) : MulAut (PlaneCore.Parameters U.form) :=
  FlagAutomorphisms.radicalAction U.form (rightCoordinateAction U a)

/-- The coordinate action on parameters agrees with the actor on the carrier. -/
theorem rightRadicalAction_native (a : flagAutomorphisms U) (u : PlaneCore.Parameters U.form) :
    (rightCoordinates U (SemidirectProduct.inl (rightRadicalAction U a u))).val =
      a.val (rightCoordinates U (SemidirectProduct.inl u)).val := by
  change (rightCoordinates U (SemidirectProduct.inl
    (FlagAutomorphisms.radicalAction U.form (rightCoordinateAction U a) u))).val = _
  rw [FlagAutomorphisms.radicalAction_inl,rightCoordinateAction_apply,rightLocalAction_val]

/-- A quotient-trivial native actor has one nonzero vector scalar and its
norm on the entire radical center. No Levi-complement invariance is assumed. -/
theorem rightRadicalAction_scalars (a : flagAutomorphisms U) (ha : rightLinearAction U a = 1) :
    ∃ k : U.F, k ≠ 0 ∧
      (∀ u : PlaneCore.Parameters U.form, (rightRadicalAction U a u).x = k • u.x) ∧
      (∀ u : PlaneCore.Parameters U.form, u.x = 0 →
        (rightRadicalAction U a u).z = (k * U.form.conj k) • u.z) := by
  obtain ⟨k,hk,hx⟩ := FlagAutomorphisms.radicalAction_vector_scalar U.form
    U.rightLeviTrace U.rightLeviTrace_spec (rightCoordinateAction U a)
      (rightCoordinateAction_right U a ha)
  exact ⟨k,hk,hx,FlagAutomorphisms.radical_center_scalar U.form U.rightLeviTrace
    U.rightLeviTrace_spec (rightRadicalAction U a) k hx⟩

/-- The actual native actor's Levi deviation is retained in the full-radical
compatibility equation. -/
theorem rightRadicalAction_compatibility (a : flagAutomorphisms U)
    (ha : rightLinearAction U a = 1) (A : Matrix.SpecialLinearGroup (Fin 2) U.F)
    (u : PlaneCore.Parameters U.form) :
    rightRadicalAction U a (PlaneCore.Parameters.planeAction A u) =
      FlagAutomorphisms.leviDeviation U.form (rightCoordinateAction U a) A *
        PlaneCore.Parameters.planeAction A (rightRadicalAction U a u) *
        (FlagAutomorphisms.leviDeviation U.form (rightCoordinateAction U a) A)⁻¹ :=
  FlagAutomorphisms.radicalAction_compatibility U.form (rightCoordinateAction U a)
    (rightCoordinateAction_right U a ha) A u

/-- Reduction of a native involution to the remaining radical and opposite
endpoint compatibility problem, retaining its exact cocycle equation. -/
theorem involution_radical_normalize (a : flagAutomorphisms U) (ha : a ^ 2 = 1)
    (hc : rightCoefficient U a = U.form.conj) :
    ∃ (b : U.overlap) (γ : flagAutomorphisms U) (k : U.F),
      b.val ∈ U.rightLocalImage ∧ k ≠ 0 ∧
      a = innerFlag U b * γ * graphFlag U ∧ rightLinearAction U γ = 1 ∧
      (∀ u : PlaneCore.Parameters U.form, (rightRadicalAction U γ u).x = k • u.x) ∧
      (∀ u : PlaneCore.Parameters U.form, u.x = 0 →
        (rightRadicalAction U γ u).z = (k * U.form.conj k) • u.z) ∧
      (γ * graphFlag U) * innerFlag U b * (γ * graphFlag U) = (innerFlag U b)⁻¹ := by
  obtain ⟨b,β,hb,he,hq,hcocycle⟩ := rightLinearAction_normalize_involution U a ha
  obtain ⟨γ,hγ,hγq⟩ := normalize_graph U β (hc ▸ hq)
  obtain ⟨k,hk,hx,hz⟩ := rightRadicalAction_scalars U γ hγq
  refine ⟨b,γ,k,hb,hk,?_,hγq,hx,hz,?_⟩
  · rw [he,hγ,mul_assoc]
  · rwa [←hγ]
end CFSG.Quasithin.ChapterF.UnitaryFiveFlagAutomorphisms
