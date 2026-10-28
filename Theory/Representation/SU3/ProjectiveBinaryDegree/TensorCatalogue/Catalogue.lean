module

public import Theory.Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.Catalogue.Assembly
public import Theory.Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.Catalogue.RestrictedWords
public import Theory.Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.Catalogue.ClassBound

/-!
# The defining-characteristic unitary tensor-word catalogue

For the full SU₃(2ˢ), the literal restrictions of the length-s binary SL₃
words are irreducible, pairwise inequivalent, and exhaust the finite-dimensional
irreducible representations over an algebraically closed field of characteristic
two. Their factors are the concrete trivial, natural, dual and trace-zero
adjoint actions, of dimensions 1, 3, 3 and 8; `finrank_wordSpace` gives the
product of those dimensions.

Unitary fixed-line geometry and torus weights prove simplicity and separation
after compatible transport of the arbitrary Hermitian form. The trace bound
on actual SU₃ odd-order conjugacy classes then proves exhaustion of the 4ˢ
words. All three premises of the finite-family argument are discharged here.
The carrier universe is arbitrary and the models are actual representation
equivalences, including the Schur scalar extension and projective inflation.

Sources: GLS III, 2.8.2, 2.8.6(a), 2.8.10(c); Guralnick--Malle, Theorem 4.10.
Reused from `CFSG/Quasithin/ChapterK/Section01To04/RankOne/UnitaryRecognition/MinimalDegree/Catalogue.lean`, with the original
proofs retained in a reusable Theory namespace for Fong--Seitz I (4D).
-/

public section

open BenderSuzuki.MatrixGroups Representation
open Representation.SL3.BinaryDefiningFactors
open scoped MonoidAlgebra TensorProduct

namespace Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue

variable {F K : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [Field K] [IsAlgClosed K] [CharP K 2]

/-- Every length-s concrete tensor word is irreducible on the full SU₃(2ˢ),
including for `s = 2` and for an arbitrary nondegenerate Hermitian form. -/
theorem word_isIrreducible
    (J : HermitianForm 3 F) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (ι : F →+* K) (w : List Factor) (hw : w.length = s) :
    IsIrreducible (word J ι w) :=
  RestrictedWords.word_isIrreducible J s hs hcard hconj ι w hw

/-- Equivalence of two restricted length-s words is exactly equality of their
label lists. Natural and dual labels remain distinct. -/
theorem word_equiv_iff
    (J : HermitianForm 3 F) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (ι : F →+* K) (v w : List Factor) (hv : v.length = s) (hw : w.length = s) :
    Nonempty ((word J ι v).Equiv (word J ι w)) ↔ v = w :=
  RestrictedWords.word_equiv_iff J s hs hcard hconj ι v w hv hw

/-- The full unitary catalogue: every finite-dimensional irreducible action,
on any carrier universe, has a unique length-s word model. The witness
intertwines the original action with the literal restricted tensor word. -/
theorem existsUnique_word_equiv
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (J : HermitianForm 3 F) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (ι : F →+* K) (ρ : Representation K J.specialSubgroup W) [IsIrreducible ρ] :
    ∃! w : List Factor, w.length = s ∧ Nonempty (ρ.Equiv (word J ι w)) := by
  exact RestrictedWords.existsUnique_word_equiv_of_class_bound J s hs hcard hconj ι
    (Theory.SpecificGroups.SU3.BinaryPRegularClasses.card_pRegularConjClasses_le
      J s hs hcard hconj) ρ

/-- Existence form of the unitary catalogue, retaining an actual intertwiner. -/
theorem exists_word_equiv
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (J : HermitianForm 3 F) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (ι : F →+* K) (ρ : Representation K J.specialSubgroup W) [IsIrreducible ρ] :
    ∃ w : List Factor, w.length = s ∧ Nonempty (ρ.Equiv (word J ι w)) :=
  (existsUnique_word_equiv J s hs hcard hconj ι ρ).exists

/-- Apply the catalogue to the scalar extension of the actual Schur-field
representation of any irreducible binary action. This supplies the `hmodel`
input of `isNatural_of_schur_word`, with the chosen embedding and explicit
endomorphism-field algebra, without a faithfulness or degree hypothesis. -/
theorem exists_schur_word_model
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (J : HermitianForm 3 F)
    (σ : Representation (ZMod 2) J.specialSubgroup V) [IsIrreducible σ]
    [Algebra (Module.End (ZMod 2)[J.specialSubgroup] σ.asModule) K]
    (s : ℕ) (hs : 2 ≤ s) (ι : F →+* K)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s)) :
    ∃ w : List Factor, w.length = s ∧
      Nonempty ((extendScalars K σ.endFieldRep).Equiv (word J ι w)) := by
  exact exists_schur_word_model_of_simple_family J σ s hs ι hcard hconj
    (word_isIrreducible J s hs hcard hconj ι)
    (fun v w hv hw he => (word_equiv_iff J s hs hcard hconj ι v w hv hw).mp he)

/-- The catalogue includes all irreducible PSU₃ actions, inflated along the
literal special-to-projective quotient map. No faithfulness is assumed. -/
theorem exists_projective_word_model
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (J : HermitianForm 3 F)
    (ρ : Representation K (ProjectiveSpecialUnitaryMatrixGroup J) V) [IsIrreducible ρ]
    (s : ℕ) (hs : 2 ≤ s) (ι : F →+* K)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s)) :
    ∃ w : List Factor, w.length = s ∧
      Nonempty (Representation.Equiv (ρ.comp J.specialToProjective) (word J ι w)) := by
  let : IsIrreducible (ρ.comp J.specialToProjective) :=
    (irreducible_comp_surjective_iff J.specialToProjective
      J.specialToProjective_surjective ρ).mpr inferInstance
  exact exists_word_equiv J s hs hcard hconj ι (ρ.comp J.specialToProjective)

end Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue
