module

public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.SpecificGroups.PSL3.RootPlaneGeometry

/-!
# Elementary two-subgroups of SL₃ in root planes

Conjugate an elementary two-subgroup into the literal upper-unitriangular
Sylow subgroup, then use the exponent-two classification there. Each root
plane has order q². Consequently its subgroups have binary rank at most 2r
when q = 2^r, and equality forces the subgroup to be the whole root plane.
These assertions include q = 2 and concern SL₃ itself.

This supplies the group-theoretic step of the adjoint obstruction in
Guralnick–Malle, Classification of 2F-modules II, author manuscript Lemma 4.5,
pp.23–24, paragraph 2. The strict fixed-space assembly is in the parent module.
-/

public section
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3Even.UnipotentGeometry
open Representation.BinaryOffender
namespace Representation.SL3.BinaryDefiningFactors.AdjointFixedSpaces
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem elementary_conjugate_le_rootPlane {r : ℕ} (hr : 0 < r)
    (hF : Nat.card F = 2 ^ r) (E : Subgroup SL(3,F)) (hE : IsElementaryTwo E) :
    ∃ (g : SL(3,F)) (point : Bool),
      E.map (MulAut.conj g).toMonoidHom ≤ rootPlaneSL F point := by
  let : IsElementaryAbelian 2 E := hE.2
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hES⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  obtain ⟨g, hg, _⟩ :=
    Matrix.PSL3.CartanActions.BorelQuotient.sylowSL_normalizer_conjugate F hr hF S
  let A := E.map (MulAut.conj g⁻¹).toMonoidHom
  have hAU : A ≤ unipotentSL F := by
    rintro x ⟨y, hy, rfl⟩
    have hyS := hES hy
    rw [← hg] at hyS
    obtain ⟨z, hz, rfl⟩ := hyS
    change g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ ∈ unipotentSL F
    simpa [mul_assoc] using hz
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hp := marked_elementary_le_plane F (unipotentSL F) (unipotentSLEquiv F) A hAU
  rcases hp with hp | hp
  · exact ⟨g⁻¹, true, hp⟩
  · exact ⟨g⁻¹, false, hp⟩

omit [Finite F] [CharP F 2] in
theorem card_rootPlaneSL (point : Bool) :
    Nat.card (rootPlaneSL F point) = Nat.card F ^ 2 := by
  cases point <;> unfold rootPlaneSL <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [Subgroup.card_map_of_injective (specialLinear_injective F), card_V₂]
  · rw [Subgroup.card_map_of_injective (specialLinear_injective F), card_V₁]

omit [CharP F 2] in
theorem rank_le_of_le_rootPlane {r : ℕ} (hF : Nat.card F = 2 ^ r)
    (E : Subgroup SL(3,F)) (point : Bool) (hE : E ≤ rootPlaneSL F point) :
    rank E ≤ 2 * r := by
  have hc := Subgroup.card_le_of_le hE
  rw [card_rootPlaneSL, hF, ← pow_mul, mul_comm r 2] at hc
  have hh := Nat.log_mono_right hc (b := 2)
  simpa [rank, Nat.log_pow (by decide : 1 < 2)] using hh

omit [CharP F 2] in
theorem eq_rootPlane_of_rank_eq {r : ℕ} (hF : Nat.card F = 2 ^ r)
    (E : Subgroup SL(3,F)) (hE : IsElementaryTwo E) (point : Bool)
    (hle : E ≤ rootPlaneSL F point) (heq : rank E = 2 * r) :
    E = rootPlaneSL F point := by
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [card_rootPlaneSL, hF, hE.card_eq_two_pow_rank, heq, ← pow_mul, mul_comm r 2]

end Representation.SL3.BinaryDefiningFactors.AdjointFixedSpaces
