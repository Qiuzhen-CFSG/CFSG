module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.Reduction
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.CharP.Two

/-!
# A local route to square membership in the J₄ matrix group

Let C be the intersection of the literal matrix group with the ambient
centralizer of `matrixUnitA`. A matrix normalizing the group and centralizing
`matrixUnitA` normalizes C. If its induced action on C squares to an inner
action, correcting its square by that local conjugator leaves a matrix in the
ambient centralizer of C. Containment of this latter centralizer in the model
then proves the required square membership.

The matrix-centralizer input follows from a separate linear calculation:
the commutant of C is spanned by `1` and `matrixA`. Over the binary field,
the only units in this span are `1` and `matrixUnitA`; the other two matrices
have square zero. The local action and commutant calculations are explicit
unproved premises of this module, independent of one another.

Source motivation: GLS3, Table 5.3i, identifies the 2A centralizer as
`2^(1+12).(3M22.2)` and gives Out(J₄) = 1. Neither assertion is assumed here.
In particular C is defined by actual matrix commutation, not by identifying
it with the separately certified `max1Subgroup` of shape `2^11.M24`.
The weaker outer-group consequence is used on printed p.510 of
Aschbacher–Smith, `refs/quasithin.pdf`.
-/

@[expose] public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares

/-- The actual involution centralizer, embedded in the ambient matrix units. -/
def involutionCentralizer : Subgroup BinaryMatrixˣ :=
  matrixGroup ⊓ Subgroup.centralizer ({matrixUnitA} : Set BinaryMatrixˣ)

theorem mem_involutionCentralizer_iff (u : BinaryMatrixˣ) :
    u ∈ involutionCentralizer ↔
      u ∈ matrixGroup ∧ u * matrixUnitA = matrixUnitA * u := by
  exact and_congr_right (fun _ => Subgroup.mem_centralizer_singleton_iff)

theorem involutionCentralizer_le_matrixGroup : involutionCentralizer ≤ matrixGroup :=
  inf_le_left

theorem matrixUnitA_mem_involutionCentralizer : matrixUnitA ∈ involutionCentralizer :=
  (mem_involutionCentralizer_iff _).mpr ⟨a.property, rfl⟩

/-- The two original hypotheses preserve the actual local subgroup. -/
theorem normalizes_involutionCentralizer (u : BinaryMatrixˣ)
    (hun : u ∈ Subgroup.normalizer (matrixGroup : Set BinaryMatrixˣ))
    (hua : u * matrixUnitA = matrixUnitA * u) :
    u ∈ Subgroup.normalizer (involutionCentralizer : Set BinaryMatrixˣ) := by
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hun, (Subgroup.centralizer ({matrixUnitA} : Set BinaryMatrixˣ)).le_normalizer
      (Subgroup.mem_centralizer_singleton_iff.mpr hua)⟩

/-- A local calculation of the induced action, with no global-normalizer
or ambient implementation hypothesis. It does not assert matrix membership. -/
def LocalNormalizerActionSquares : Prop :=
  ∀ (u : BinaryMatrixˣ)
    (hu : u ∈ Subgroup.normalizer (involutionCentralizer : Set BinaryMatrixˣ)),
    u * matrixUnitA = matrixUnitA * u →
    ∃ c : involutionCentralizer,
      (involutionCentralizer.normalizerMonoidHom ⟨u, hu⟩) ^ 2 = MulAut.conj c

/-- The ambient centralizer has no extra matrix units outside the model. -/
def LocalMatrixCentralizer : Prop :=
  Subgroup.centralizer (involutionCentralizer : Set BinaryMatrixˣ) ≤ matrixGroup

/-- The concrete linear algebra input: arbitrary matrices commuting with the
local subgroup lie in the span of the identity and the first generator. -/
def LocalMatrixCommutant : Prop :=
  ∀ M : BinaryMatrix,
    (∀ c : involutionCentralizer,
      M * ((c : BinaryMatrixˣ) : BinaryMatrix) =
        ((c : BinaryMatrixˣ) : BinaryMatrix) * M) →
    ∃ r s : ZMod 2, M = r • (1 : BinaryMatrix) + s • matrixA

/-- A local automorphism calculation is a sufficient, stronger input. -/
theorem localNormalizerActionSquares_of_automorphism_squares
    (h : ∀ α : MulAut involutionCentralizer,
      ∃ c : involutionCentralizer, α ^ 2 = MulAut.conj c) :
    LocalNormalizerActionSquares := by
  intro u hu _
  exact h (involutionCentralizer.normalizerMonoidHom ⟨u, hu⟩)

/-- The two other binary linear combinations cannot be units. -/
theorem unit_eq_one_or_matrixUnitA_of_span (u : BinaryMatrixˣ) (r s : ZMod 2)
    (h : (u : BinaryMatrix) = r • (1 : BinaryMatrix) + s • matrixA) :
    u = 1 ∨ u = matrixUnitA := by
  have hn := Units.ne_zero u
  have hn2 := Units.ne_zero (u * u)
  change (u : BinaryMatrix) * (u : BinaryMatrix) ≠ 0 at hn2
  have htwo : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases htwo r with rfl | rfl <;> rcases htwo s with rfl | rfl <;>
    simp only [zero_smul, one_smul, zero_add, add_zero] at h
  · exact (hn h).elim
  · exact Or.inr (Units.ext h)
  · exact Or.inl (Units.ext h)
  · exfalso
    apply hn2
    rw [h, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, matrixA_mul_self]
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply, add_assoc,
      CharTwo.add_cancel_left, CharTwo.add_self_eq_zero]

/-- The commutant calculation discharges the matrix-centralizer input. -/
theorem localMatrixCentralizer_of_commutant (hcomm : LocalMatrixCommutant) :
    LocalMatrixCentralizer := by
  intro u hu
  obtain ⟨r, s, hrs⟩ := hcomm (u : BinaryMatrix) (by
    intro c
    have hc := Subgroup.mem_centralizer_iff.mp hu (c : BinaryMatrixˣ) c.property
    exact @congrArg BinaryMatrixˣ BinaryMatrix
      (u * (c : BinaryMatrixˣ)) ((c : BinaryMatrixˣ) * u) Units.val hc.symm)
  rcases unit_eq_one_or_matrixUnitA_of_span u r s hrs with rfl | rfl
  · exact matrixGroup.one_mem
  · exact a.property

/-- Correct an inner action by its actual local conjugator. -/
theorem corrected_square_mem_centralizer (u : BinaryMatrixˣ)
    (hu : u ∈ Subgroup.normalizer (involutionCentralizer : Set BinaryMatrixˣ))
    (c : involutionCentralizer)
    (hc : (involutionCentralizer.normalizerMonoidHom ⟨u, hu⟩) ^ 2 = MulAut.conj c) :
    (c : BinaryMatrixˣ)⁻¹ * u ^ 2 ∈
      Subgroup.centralizer (involutionCentralizer : Set BinaryMatrixˣ) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have he := congrArg (fun α : MulAut involutionCentralizer =>
    ((α ⟨x, hx⟩ : involutionCentralizer) : BinaryMatrixˣ)) hc
  change u * (u * x * u⁻¹) * u⁻¹ = (c : BinaryMatrixˣ) * x * (c : BinaryMatrixˣ)⁻¹ at he
  have he' : u ^ 2 * x = (c : BinaryMatrixˣ) * x * (c : BinaryMatrixˣ)⁻¹ * u ^ 2 := by
    calc
      u ^ 2 * x = (u * (u * x * u⁻¹) * u⁻¹) * u ^ 2 := by
        simp only [pow_two]
        group
      _ = (c : BinaryMatrixˣ) * x * (c : BinaryMatrixˣ)⁻¹ * u ^ 2 := by rw [he]
  calc
    x * ((c : BinaryMatrixˣ)⁻¹ * u ^ 2) =
        (c : BinaryMatrixˣ)⁻¹ * ((c : BinaryMatrixˣ) * x *
          (c : BinaryMatrixˣ)⁻¹ * u ^ 2) := by group
    _ = (c : BinaryMatrixˣ)⁻¹ * (u ^ 2 * x) := by rw [← he']
    _ = ((c : BinaryMatrixˣ)⁻¹ * u ^ 2) * x := by rw [mul_assoc]

/-- Multiplying the corrected matrix by its local conjugator gives membership. -/
theorem square_mem_of_local (hact : LocalNormalizerActionSquares)
    (hcent : LocalMatrixCentralizer) (u : BinaryMatrixˣ)
    (hu : u ∈ Subgroup.normalizer (involutionCentralizer : Set BinaryMatrixˣ))
    (hua : u * matrixUnitA = matrixUnitA * u) : u ^ 2 ∈ matrixGroup := by
  obtain ⟨c, hc⟩ := hact u hu hua
  have hrem := hcent (corrected_square_mem_centralizer u hu c hc)
  have h := matrixGroup.mul_mem (involutionCentralizer_le_matrixGroup c.property) hrem
  simpa only [mul_inv_cancel_left] using h

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares
