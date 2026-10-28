module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.TensorWords
public import Theory.Representation.PSL3Three.AbsoluteDegrees.Saturation
public import Theory.Representation.EndFieldFrobenius
public import Theory.SpecificGroups.SU3.ProjectiveEntrywiseAction

/-!
# Finite-family assembly for the restricted unitary words

There are 4ˢ words of length s in the four concrete binary defining factors.
If their restrictions to SU₃ are simple and pairwise inequivalent, and SU₃ has
at most 4ˢ odd-order classes, the modular simple-family bound proves exhaustion.
A choice of basis handles arbitrary carrier universes. Applying this exhaustion
to the scalar extension of the actual Schur model supplies precisely the word
witness used by `isNatural_of_schur_word`. Inflation along the actual projective
quotient is included as a separate application.

The restricted simplicity, separation and class bound are explicit, unproved
premises here. Restricting the SL₃ catalogue along an injective group map does
not establish them. Thus the results below are conditional assembly lemmas,
not the unconditional defining-characteristic SU₃ classification.

Sources: GLS III, 2.8.2, 2.8.6(a) and 2.8.10(c); Guralnick--Malle,
Theorem 4.10, first paragraph. The group-specific premises must refer to the
literal action `word J ι w` defined in `TensorWords`.
-/

public section

set_option backward.isDefEq.respectTransparency false

open BenderSuzuki.MatrixGroups Representation
open Representation.SL3.BinaryDefiningFactors
open scoped MatrixGroups MonoidAlgebra TensorProduct

namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.MinimalDegree

universe u

variable {F : Type*} {K : Type u} [Field F] [Finite F]
  [Field K] [IsAlgClosed K] [CharP K 2]

private theorem card_words_unitary (s : ℕ) :
    Nat.card {w : List Factor // w.length = s} = 4 ^ s := by
  change Nat.card (List.Vector Factor s) = _
  rw [Nat.card_eq_fintype_card, card_vector]
  rfl

private theorem exists_word_equiv_sameUniverse
    {W : Type u} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (J : HermitianForm 3 F) (s : ℕ) (ι : F →+* K)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hirr : ∀ w : List Factor, w.length = s → IsIrreducible (word J ι w))
    (hne : ∀ v w : List Factor, v.length = s → w.length = s →
      Nonempty ((word J ι v).Equiv (word J ι w)) → v = w)
    (hclasses : Nat.card (ConjClasses.mk ''
      {g : J.specialSubgroup | ¬ 2 ∣ orderOf g}) ≤ Nat.card F)
    (ρ : Representation K J.specialSubgroup W) [IsIrreducible ρ] :
    ∃ w : List Factor, w.length = s ∧ Nonempty (ρ.Equiv (word J ι w)) := by
  classical
  let I := List.Vector Factor s
  let M : I → Type u := fun w => WordSpace K w.val
  let rep : ∀ w : I, Representation K J.specialSubgroup (M w) :=
    fun w => word J ι w.val
  have irr : ∀ w : I, IsIrreducible (rep w) := fun w => hirr w.val w.property
  have hpair : Pairwise fun v w : I => IsEmpty ((rep v).Equiv (rep w)) := by
    intro v w hvw
    constructor
    intro φ
    exact hvw (Subtype.ext (hne v.val w.val v.property w.property ⟨φ⟩))
  have hpow : (2 ^ s) ^ 2 = 4 ^ s := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    rfl
  have hbound : Nat.card (ConjClasses.mk ''
      {g : J.specialSubgroup | ¬ 2 ∣ orderOf g}) ≤ Nat.card I := by
    change _ ≤ Nat.card {w : List Factor // w.length = s}
    rw [card_words_unitary]
    simpa only [hcard, hpow] using hclasses
  obtain ⟨w, he⟩ := exists_equiv_of_pRegular_class_bound M rep 2 hpair hbound ρ
  exact ⟨w.val, w.property, he⟩

/-- Once the restricted words are a simple family and reach the odd-order class
bound, every irreducible representation occurs in that family. The original
carrier may lie in an arbitrary universe, independently of the coefficient
field. The witness is an actual intertwining equivalence. -/
theorem exists_word_equiv_of_simple_family_and_class_bound
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (J : HermitianForm 3 F) (s : ℕ) (ι : F →+* K)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hirr : ∀ w : List Factor, w.length = s → IsIrreducible (word J ι w))
    (hne : ∀ v w : List Factor, v.length = s → w.length = s →
      Nonempty ((word J ι v).Equiv (word J ι w)) → v = w)
    (hclasses : Nat.card (ConjClasses.mk ''
      {g : J.specialSubgroup | ¬ 2 ∣ orderOf g}) ≤ Nat.card F)
    (ρ : Representation K J.specialSubgroup W) [IsIrreducible ρ] :
    ∃ w : List Factor, w.length = s ∧ Nonempty (ρ.Equiv (word J ι w)) := by
  classical
  let b := (Module.finBasis K W).equivFun
  let σ : Representation K J.specialSubgroup (Fin (Module.finrank K W) → K) :=
    b.conjRingEquiv.toMonoidHom.comp ρ
  let φ : ρ.Equiv σ := Representation.Equiv.mk b (by
    intro g
    ext v
    simp [σ, LinearEquiv.conjRingEquiv])
  have hirrσ : IsIrreducible σ := by
    let f := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ φ.toIntertwiningMap
    have hf : Function.Bijective f := φ.toLinearEquiv.bijective
    let ef := LinearEquiv.ofBijective f hf
    rw [irreducible_iff_isSimpleModule_asModule]
    exact ef.isSimpleModule_iff.mp ((irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance)
  obtain ⟨w, hw, ⟨ψ⟩⟩ := exists_word_equiv_sameUniverse J s ι hcard hirr hne hclasses σ
  exact ⟨w, hw, ⟨φ.trans ψ⟩⟩

/-- Exhaustion and separation give a unique label list, retaining the actual
representation equivalence on the original carrier. -/
theorem existsUnique_word_equiv_of_simple_family_and_class_bound
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (J : HermitianForm 3 F) (s : ℕ) (ι : F →+* K)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hirr : ∀ w : List Factor, w.length = s → IsIrreducible (word J ι w))
    (hne : ∀ v w : List Factor, v.length = s → w.length = s →
      Nonempty ((word J ι v).Equiv (word J ι w)) → v = w)
    (hclasses : Nat.card (ConjClasses.mk ''
      {g : J.specialSubgroup | ¬ 2 ∣ orderOf g}) ≤ Nat.card F)
    (ρ : Representation K J.specialSubgroup W) [IsIrreducible ρ] :
    ∃! w : List Factor, w.length = s ∧ Nonempty (ρ.Equiv (word J ι w)) := by
  obtain ⟨w, hw, ⟨φ⟩⟩ :=
    exists_word_equiv_of_simple_family_and_class_bound J s ι hcard hirr hne hclasses ρ
  refine ⟨w, ⟨hw, ⟨φ⟩⟩, ?_⟩
  rintro v ⟨hv, ⟨ψ⟩⟩
  exact hne v w hv hw ⟨ψ.symm.trans φ⟩

/-- The exact word-model witness consumed by `isNatural_of_schur_word`, obtained
from the scalar extension of an arbitrary irreducible binary action. The
endomorphism-field algebra and the chosen embedding of F are explicit.
No faithfulness, offender, degree bound or natural identification is assumed. -/
theorem exists_schur_word_model_of_simple_family_and_class_bound
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (J : HermitianForm 3 F)
    (σ : Representation (ZMod 2) J.specialSubgroup V) [IsIrreducible σ]
    [Algebra (Module.End (ZMod 2)[J.specialSubgroup] σ.asModule) K]
    (s : ℕ) (ι : F →+* K) (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hirr : ∀ w : List Factor, w.length = s → IsIrreducible (word J ι w))
    (hne : ∀ v w : List Factor, v.length = s → w.length = s →
      Nonempty ((word J ι v).Equiv (word J ι w)) → v = w)
    (hclasses : Nat.card (ConjClasses.mk ''
      {g : J.specialSubgroup | ¬ 2 ∣ orderOf g}) ≤ Nat.card F) :
    ∃ w : List Factor, w.length = s ∧
      Nonempty ((extendScalars K σ.endFieldRep).Equiv (word J ι w)) := by
  let : IsAbsolutelyIrreducible σ.endFieldRep := endFieldRep_isAbsolutelyIrreducible σ
  let : IsIrreducible (extendScalars K σ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension σ.endFieldRep K
  exact exists_word_equiv_of_simple_family_and_class_bound
    J s ι hcard hirr hne hclasses (extendScalars K σ.endFieldRep)

/-- Irreducible representations of the actual projective image are covered
by the same catalogue after inflation along its natural surjection. This
application makes no assumption that an SU₃ representation is faithful. -/
theorem exists_projective_word_model_of_simple_family_and_class_bound
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (J : HermitianForm 3 F)
    (ρ : Representation K (ProjectiveSpecialUnitaryMatrixGroup J) V) [IsIrreducible ρ]
    (s : ℕ) (ι : F →+* K) (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hirr : ∀ w : List Factor, w.length = s → IsIrreducible (word J ι w))
    (hne : ∀ v w : List Factor, v.length = s → w.length = s →
      Nonempty ((word J ι v).Equiv (word J ι w)) → v = w)
    (hclasses : Nat.card (ConjClasses.mk ''
      {g : J.specialSubgroup | ¬ 2 ∣ orderOf g}) ≤ Nat.card F) :
    ∃ w : List Factor, w.length = s ∧
      Nonempty (Representation.Equiv (ρ.comp J.specialToProjective) (word J ι w)) := by
  let : IsIrreducible (ρ.comp J.specialToProjective) :=
    (irreducible_comp_surjective_iff J.specialToProjective
      J.specialToProjective_surjective ρ).mpr inferInstance
  exact exists_word_equiv_of_simple_family_and_class_bound
    J s ι hcard hirr hne hclasses (ρ.comp J.specialToProjective)

end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.MinimalDegree
