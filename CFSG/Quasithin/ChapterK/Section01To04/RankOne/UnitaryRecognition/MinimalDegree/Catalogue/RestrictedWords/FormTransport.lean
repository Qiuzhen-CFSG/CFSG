module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.TensorWords
public import Theory.Representation.SU3.BinaryDefiningWords.Conjugation
public import Theory.Representation.Quotient
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# Transport of the actual unitary words to standard Hermitian form

The quadratic Frobenius hypothesis gives the fixed-field cardinality required
by Hermitian basis existence. Its matrix conjugation gives one isomorphism of
special unitary groups, and the conjugation theorem for concrete tensor words
gives compatible representation equivalences for every word. Surjective
pullback then transfers irreducibility and equivalence of any pair of words in
both directions. No simplicity or classification theorem is assumed here.

Sources: Huppert II.10.4(b); GLS III, 2.8.2, 2.8.6(a), and 2.8.10(c).
-/

public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MatrixGroups
open Representation
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.MinimalDegree.RestrictedWords
section
open BenderSuzuki.MatrixGroups Representation.SL3.BinaryDefiningFactors Matrix
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
variable {F K : Type*} [Field F] [Field K] [IsAlgClosed K] [CharP K 2]

/-- A specified Hermitian basis change intertwines every concrete word. -/
theorem word_formTransport_equiv (J : HermitianForm 3 F) (ι : F →+* K)
    (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form)
    (w : List Factor) :
    Nonempty (Representation.Equiv
      ((word (standardForm J) ι w).comp (specialEquiv J C hC).toMonoidHom)
      (word J ι w)) := by
  apply wordEquiv_of_matrix_conjugacy ι w (specialLinearInclusion J)
    ((specialLinearInclusion (standardForm J)).comp (specialEquiv J C hC).toMonoidHom) C
  intro g
  have incl (I : HermitianForm 3 F) (a : I.specialSubgroup) :
      SpecialLinearGroup.toGL (specialLinearInclusion I a) = a.val := Units.ext rfl
  change C * SpecialLinearGroup.toGL
    (specialLinearInclusion (standardForm J) (specialEquiv J C hC g)) =
    SpecialLinearGroup.toGL (specialLinearInclusion J g) * C
  rw [incl, incl, specialEquiv_apply]
  simp [mul_assoc]


end

section
open BenderSuzuki.MatrixGroups Representation.SL3.BinaryDefiningFactors Matrix
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
variable {F K : Type*} [Field F] [Field K] [IsAlgClosed K] [CharP K 2]

omit [IsAlgClosed K] [CharP K 2] in
private theorem irreducible_iff_of_equiv {G V W : Type*} [Group G]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {ρ : Representation K G V} {τ : Representation K G W} (e : ρ.Equiv τ) :
    IsIrreducible ρ ↔ IsIrreducible τ := by
  let f := Representation.IntertwiningMap.equivLinearMapAsModule ρ τ e.toIntertwiningMap
  have hf : Function.Bijective f := e.toLinearEquiv.bijective
  let ef := LinearEquiv.ofBijective f hf
  rw [irreducible_iff_isSimpleModule_asModule, irreducible_iff_isSimpleModule_asModule]
  exact ef.isSimpleModule_iff

/-- One group isomorphism transports the entire family of words simultaneously. -/
theorem exists_word_formTransport [Finite F] [Algebra (ZMod 2) F]
    (J : HermitianForm 3 F) (s : ℕ) (hs : 0 < s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (ι : F →+* K) :
    ∃ e : J.specialSubgroup ≃* (standardForm J).specialSubgroup,
      ∀ w : List Factor, Nonempty (Representation.Equiv
        ((word (standardForm J) ι w).comp e.toMonoidHom) (word J ι w)) := by
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 s hs hcard hconj
  obtain ⟨C, hC⟩ := exists_standard_basis J (2 ^ s) hcard hfixed
  exact ⟨specialEquiv J C hC, fun w => word_formTransport_equiv J ι C hC w⟩

/-- Irreducibility of an arbitrary-form word is equivalent to its standard-form counterpart. -/
theorem word_standard_irreducible_iff [Finite F] [Algebra (ZMod 2) F]
    (J : HermitianForm 3 F) (s : ℕ) (hs : 0 < s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (ι : F →+* K) (w : List Factor) :
    IsIrreducible (word J ι w) ↔ IsIrreducible (word (standardForm J) ι w) := by
  obtain ⟨e, he⟩ := exists_word_formTransport J s hs hcard hconj ι
  obtain ⟨φ⟩ := he w
  exact (irreducible_iff_of_equiv φ).symm.trans
    (irreducible_comp_surjective_iff e.toMonoidHom e.surjective _)

/-- Equivalence between two words is preserved and reflected by standard-form transport. -/
theorem word_standard_equiv_iff [Finite F] [Algebra (ZMod 2) F]
    (J : HermitianForm 3 F) (s : ℕ) (hs : 0 < s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (ι : F →+* K) (v w : List Factor) :
    Nonempty ((word J ι v).Equiv (word J ι w)) ↔
      Nonempty ((word (standardForm J) ι v).Equiv (word (standardForm J) ι w)) := by
  obtain ⟨e, he⟩ := exists_word_formTransport J s hs hcard hconj ι
  obtain ⟨φ⟩ := he v
  obtain ⟨ψ⟩ := he w
  constructor
  · rintro ⟨f⟩
    exact ⟨inflationEquiv e.toMonoidHom e.surjective _ _ (φ.trans (f.trans ψ.symm))⟩
  · rintro ⟨f⟩
    exact ⟨φ.symm.trans ((restrictEquiv e.toMonoidHom f).trans ψ)⟩


end

end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.MinimalDegree.RestrictedWords
