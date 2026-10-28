module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.Rotation
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.SemidihedralTorus.ActorCoordinates.MarkedFourPlacement

/-!
# Rotation coordinates for an actor fixing a marked inner four-group

Normalize the original form and marked involution, use the proved marked-four
placement, and apply standard-fixer coordinates to the image of the entire
actor. The resulting projective equivalence gives the exact rotation curve
formula, including its single Boolean parameter for each automorphism.

The standard-fixer premise remains explicit. Its producer is
qt-e01-odd-psu3-standard-fixer-coordinates; the marked-four placement is
already proved by qt-e01-odd-psu3-marked-four-placement.
Source: Aschbacher--Smith E.1.14(7), printed p.214, citing Aschbacher (1982),
Lemma 4.11, and A.3.21(a)--(b), printed p.55.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry
open InnerGeometry.SemidihedralTorus
variable {F : Type} [Field F] [Finite F]
/-- One equivalence marks the involution and transports every actor on the
literal norm-one rotation curve. -/
theorem rotation_coordinates_of_fixed_four (J : HermitianForm 3 F)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (U : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hU : IsPGroup 2 U)
    (w : ProjectiveSpecialUnitaryMatrixGroup J) (hw : orderOf w = 2)
    (B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    [IsElementaryAbelian 2 B] (hB : Nat.card B = 4) (hwB : w ∈ B)
    (hBU : ∀ a ∈ U, ∀ x ∈ B, a x = x)
    (hfix : StandardFixerCoordinates (HermitianForm.IdentityGram.identityGram J)) :
    ∃ (h2 : (2 : F) ≠ 0)
      (e : ProjectiveSpecialUnitaryMatrixGroup J ≃*
        ProjectiveSpecialUnitaryMatrixGroup (HermitianForm.IdentityGram.identityGram J)),
      e w = (HermitianForm.IdentityGram.identityGram J).specialToProjective
        (Matrix.SU3.standardInvolution (HermitianForm.IdentityGram.identityGram J) rfl) ∧
      ∀ a ∈ U, ∃ ε : Bool, ∀ k : HermitianForm.EvenInner.normOne
          (HermitianForm.IdentityGram.identityGram J),
        MulAut.congr e a (projectiveRotation _ rfl h2 k) =
          projectiveRotation _ rfl h2 (if ε then k⁻¹ else k) := by
  let J₁ := HermitianForm.IdentityGram.identityGram J
  obtain ⟨e₁, he₁⟩ := exists_marked_identityGram_equiv J hp ho hcard hc (MulEquiv.refl _) w hw
  let B₁ := B.map e₁.toMonoidHom
  have hB₁ : IsElementaryAbelian 2 B₁ := IsElementaryAbelian.map e₁.toMonoidHom
  have hB₁card : Nat.card B₁ = 4 := by rw [card_map_of_injective e₁.injective, hB]
  have hwB₁ : J₁.specialToProjective (Matrix.SU3.standardInvolution J₁ rfl) ∈ B₁ := by
    rw [← he₁]
    exact mem_map_of_mem e₁.toMonoidHom hwB
  obtain ⟨b, hbw, hbB⟩ := markedFourPlacement J₁ rfl hp ho hcard hc B₁ hB₁ hB₁card hwB₁
  let e₂ := e₁.trans b
  have he₂ : e₂ w = J₁.specialToProjective (Matrix.SU3.standardInvolution J₁ rfl) := by
    change b (e₁ w) = _
    rw [he₁, hbw]
  have hB₂ : B.map e₂.toMonoidHom = standardFour J₁ := by
    rw [← hbB]
    change _ = (B.map e₁.toMonoidHom).map b.toMonoidHom
    rw [Subgroup.map_map]
    rfl
  let U₂ := U.map (MulAut.congr e₂).toMonoidHom
  have hU₂ : IsPGroup 2 U₂ := hU.map _
  have hfix₂ : ∀ a ∈ U₂, ∀ x ∈ standardFour J₁, a x = x := by
    rintro a ⟨a₀, ha₀, rfl⟩ x hx
    rw [← hB₂] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change e₂ (a₀ (e₂.symm (e₂ y))) = e₂ y
    rw [e₂.symm_apply_apply, hBU a₀ ha₀ y hy]
  obtain ⟨c, hcs, hcoord⟩ := hfix U₂ hU₂ hfix₂
  have h2 : (2 : F) ≠ 0 := Field.two_ne_zero_of_odd_card F (by rw [hcard]; exact ho.pow)
  refine ⟨h2, e₂.trans c, ?_, ?_⟩
  · change c (e₂ w) = _
    rw [he₂]
    exact hcs _ (standardInvolution_mem_standardFour J₁ rfl)
  · intro a ha
    exact rotation_action_of_signSemilinear J₁ rfl h2 _
      (hcoord (MulAut.congr e₂ a) (mem_map_of_mem _ ha))
end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry
