module

public import Theory.Representation.SL3.BinaryDefiningFactors
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.RestrictedSeparation
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.RestrictedFactors
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.HighestVector
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.FixedLine
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.OrbitSpan
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.CharacterSeparation
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Basic
public import Theory.Representation.TwoDimensionalOddOrder

/-!
# Simplicity and separation of the concrete binary SL₃ tensor words

The four restricted factors are simple, and every word of length `n` gives a
simple representation of SL₃(F) when `|F| = 2^n`. Every nonzero
subrepresentation has a nonzero upper-fixed vector by the finite p-group
fixed-vector theorem. The proved fixed-line and orbit-span results then show
that it contains the highest vector and therefore the entire module.

The re-exported character-polynomial argument proves that an actual equivalence
between two words of this length identifies their labels. Together these
results give the concrete simple family required by the separate completeness
argument. They include the field of order two and require no algebraic closure
of the coefficient field.

Source: GLS III, 2.8.2, 2.8.5–6, 2.8.9 and 2.8.10(c).
-/

public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MatrixGroups TensorProduct
namespace Representation.SL3.BinaryDefiningFactors.TensorSimplicity
variable {K : Type*} [Field K]
variable {F : Type*} [Field F] [Finite F] [CharP K 2]
open Matrix.PSL3Even.UnipotentGeometry

/-- A one-dimensional upper-fixed space and a cyclic highest vector imply
simplicity. The unconditional theorem below supplies both premises. -/
theorem wordRep_isIrreducible_of_fixedLine_and_span (ι : F →+* K)
    (n : ℕ) (hcard : Nat.card F = 2 ^ n) (w : List Factor)
    (hfixed : ∀ v : WordSpace K w,
      (∀ u : U F, wordRep ι w (specialLinear F u) v = v) →
        v ∈ Submodule.span K {wordSeed K w})
    (hspan : Submodule.span K (Set.range fun g : SL(3,F) =>
      wordRep ι w g (wordSeed K w)) = ⊤) : IsIrreducible (wordRep ι w) := by
  let : Nontrivial (WordSpace K w) := ⟨⟨wordSeed K w, 0, wordSeed_ne_zero K w⟩⟩
  rw [IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  have hS' : S.toSubmodule ≠ ⊥ := fun h => hS (Subrepresentation.toSubmodule_injective h)
  let : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hS'
  have hp : IsPGroup (ringChar K) (U F) := by
    rw [ringChar.eq K 2]
    apply IsPGroup.of_card (n := n * 3)
    rw [card_U, hcard, pow_mul]
  obtain ⟨v, hv, hfix⟩ := pGroup_fix_nonzero_vector
    (by rw [ringChar.eq K 2]; decide) hp (S.toRepresentation.comp (specialLinear F))
  have hv0 : (v : WordSpace K w) ≠ 0 := fun h => hv (Subtype.ext h)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hfixed v (by
    intro u
    exact congrArg Subtype.val (hfix u)))
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_smul] at hc
    exact hv0 hc.symm
  have hseed : wordSeed K w ∈ S := by
    have hh := S.toSubmodule.smul_mem c⁻¹ v.property
    rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at hh
    exact hh
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  exact S.apply_mem_toSubmodule g hseed

/-- Every concrete Frobenius tensor word of field length is irreducible.
The fixed-line and cyclic-vector inputs are proved for the actual action;
no irreducibility, classification, or completeness premise is required. -/
theorem wordRep_isIrreducible (ι : F →+* K) (n : ℕ)
    (hcard : Nat.card F = 2 ^ n) (w : List Factor) (hw : w.length = n) :
    IsIrreducible (wordRep ι w) :=
  wordRep_isIrreducible_of_fixedLine_and_span ι n hcard w
    (FixedLine.fixed_mem_span ι n hcard w hw)
    (wordSeed_orbit_span ι n hcard w hw)

end Representation.SL3.BinaryDefiningFactors.TensorSimplicity
