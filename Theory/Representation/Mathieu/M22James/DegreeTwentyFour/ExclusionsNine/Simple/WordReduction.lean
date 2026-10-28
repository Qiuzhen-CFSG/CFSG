module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsNine.Simple.Models
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.PointConstituents

/-!
# Absolute mixed-word reduction for binary degree eighteen

The actual Schur field has degree two. Tensor-word classification after
extension to its algebraic closure gives a word of dimension nine and period
two, so its labels are precisely natural/dual in one of the two orders.
The equivalence here is over that closure. The final binary recognition
contract retains the remaining coordinate comparison and descent explicitly.

Source: GLS III, 2.8.6, Remark 2.8.8 and 2.8.10(c), used to establish the
3.M₂₂ degree exclusion in Guralnick–Malle I, Proposition 5.1, pp.15–16.
-/

@[expose] public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsNine.Simple
universe u
open Representation Representation.SL3.BinaryDefiningFactors
open Representation.SL3FourLocalCatalogue
open scoped MonoidAlgebra
set_option backward.isDefEq.respectTransparency false
variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]
  (σ : Representation (ZMod 2) SL U) [IsIrreducible σ]

abbrev SchurField := Module.End (ZMod 2)[SL] σ.asModule
abbrev SplittingField := AlgebraicClosure (SchurField σ)
instance schurField_charTwo : CharP (SchurField σ) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (SchurField σ)).injective 2

/-- The labels retain both mixed natural/dual orientations. -/
def mixedWord (b : Bool) : List Factor :=
  if b then [.natural, .dual] else [.dual, .natural]

private lemma mixed_word_pattern (w : List Factor) (hlen : w.length = 2)
    (hd : wordDegree w = 9) (hperiod : w.rotate 1 ≠ w) :
    ∃ b, w = mixedWord b := by
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  cases a <;> cases b <;> simp_all [wordDegree, Factor.dimension]
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Over the algebraic closure of the actual Schur field, the binary
18-dimensional action is an actual mixed tensor word. No absolute
irreducibility or Schur field is assumed for the original action. -/
theorem exists_absolute_mixed_equiv (hq : CentralQuadratic σ)
    (hd : Module.finrank (ZMod 2) U = 18) :
    ∃ (ι : F →+* SplittingField σ) (b : Bool),
      Nonempty ((extendScalars (SplittingField σ) σ.endFieldRep).Equiv
        (wordRep ι (mixedWord b))) := by
  let : Algebra (ZMod 2) (SplittingField σ) := ZMod.algebra (SplittingField σ) 2
  let : IsAbsolutelyIrreducible σ.endFieldRep := endFieldRep_isAbsolutelyIrreducible σ
  let : IsIrreducible (extendScalars (SplittingField σ) σ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension σ.endFieldRep (SplittingField σ)
  let ι : F →+* SplittingField σ :=
    (IsAlgClosed.lift (R := ZMod 2) (S := F) (M := SplittingField σ)).toRingHom
  have hcard : Nat.card F = 2 ^ 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  obtain ⟨w, hw, ⟨e⟩⟩ := exists_word_equiv ι 2 hcard
    (extendScalars (SplittingField σ) σ.endFieldRep)
  have hs : schurDegree 2 σ = 2 :=
    (PointConstituents.schurDegree_eq_two_and_finrank_cases σ hq (by omega)).1
  have hp := word_rotate_iff_schurDegree_dvd σ ι w (hw ▸ hcard)
    (fun v hv => wordRep_isIrreducible ι 2 hcard v (hv.trans hw))
    (fun u v hu hv h => (wordRep_equiv_iff ι 2 hcard u v (hu.trans hw) (hv.trans hw)).mp h)
    ⟨e⟩ 1
  have hdim : Module.finrank (ZMod 2) U = schurDegree 2 σ * wordDegree w := by
    rw [Representation.finrank_eq_schurDegree_mul 2 σ (SplittingField σ),
      e.toLinearEquiv.finrank_eq, finrank_wordSpace]
  rw [hs, hd] at hdim
  have hne : w.rotate 1 ≠ w := hp.not.mpr (by rw [hs]; decide)
  obtain ⟨b, hb⟩ := mixed_word_pattern w hw (by omega) hne
  exact ⟨ι, b, hb ▸ ⟨e⟩⟩

/-- The remaining binary recognition statement. It requires an actual
intertwining equivalence, not an equality of dimensions or a family label. -/
def SimplePointRecognition : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (τ : Representation (ZMod 2) SL V),
    CentralQuadratic τ → τ.IsIrreducible → Module.finrank (ZMod 2) V = 18 →
      ∃ b : Bool, Nonempty (τ.Equiv (mixedBinaryRep b))

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsNine.Simple
