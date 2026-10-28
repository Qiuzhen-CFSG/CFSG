module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddTwoPrimary.LocalOrder
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddTwoPrimary.OrthogonalMap.QuaternionTwist
public import Theory.AtlasPort.LinearGroups.G2.FieldTransport
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The orthogonal subgroup map in odd-prime G₂

Choose a nonsquare in the prime field. The quaternion-coordinate construction
then supplies a homomorphism from `(SL₂(p) × SL₂(p)) ⋊ C₂` into the actual
split-octonion automorphism group, with exactly the diagonal scalar kernel.
Coefficientwise field transport gives the required map over any field of
cardinality `p`. The existing image-order calculation supplies its odd index,
so this constructs the literal `LocalModel` consumed by the universal-cover
argument.

Source context: Aschbacher–Smith I.1.1–I.1.4, printed pp.407–408,
and GLS III §6.1. The imported coordinate model and field transport preserve
the licensed ATLAS realization; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Atlas.G2.MultiplierOrdinary.OddTwoPrimary
open OrthogonalMap

/-- An actual orthogonal subgroup map, with precisely the diagonal scalar kernel. -/
theorem exists_orthogonal_diagonal_map {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) (hp : 3 < p) :
    ∃ (φ : C2 →* MulAut (RankOne p × RankOne p))
      (j : (RankOne p × RankOne p) ⋊[φ] C2 →* Model F),
      ∀ x, j x = 1 ↔ x = 1 ∨ x = SemidirectProduct.inl (-1,-1) := by
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; omega)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha (by exact ⟨0, by simp⟩)
  let d := -a
  have hd : d ≠ 0 := neg_ne_zero.mpr ha0
  let := Fintype.ofFinite F
  let e : ZMod p ≃+* F := ZMod.ringEquivOfPrime F Fact.out
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  refine ⟨action d hd, (fieldEquiv e).toMonoidHom.comp (inclusion d hd), ?_⟩
  intro x
  change fieldEquiv e (inclusion d hd x) = 1 ↔ _
  rw [map_eq_one_iff _ (fieldEquiv e).injective]
  exact inclusion_kernel d hd (by simpa [d] using ha) x

/-- The constructed map supplies the literal odd-index local model used in the
universal-cover argument. The order calculation is reused without extra premises. -/
theorem exists_orthogonal_localModel {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) (hp : 3 < p) :
    Nonempty (LocalModel p (Model F)) := by
  obtain ⟨φ,j,hj⟩ := exists_orthogonal_diagonal_map hF hp
  exact ⟨⟨φ,j,hj,odd_index_of_diagonal_kernel hF hp φ j hj⟩⟩

end Atlas.G2.MultiplierOrdinary.OddTwoPrimary

end
