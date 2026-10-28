module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Permutation
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.PermutationRelations
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates
public import Theory.Representation.HigmanSims.LargeModels.TracePair
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408

/-!
# The common presentation input for the two remaining HS models

The degree-896 and degree-1408 constructions use two encodings of the same
thirteen ATLAS relators. Expanding the signed words proves their equality in
every group. The induced marked surjection between the presentations commutes
with their literal maps to the degree-100 permutation carrier. Thus
faithfulness of the signed-word presentation also supplies the kernel inclusion
needed by the degree-896 descent.

All matrix relations, density and separating-trace certificates are already
proved. The final two lemmas apply this bridge to the actual model producers;
only injectivity of the concrete presentation map remains explicit. This is
an abstract presentation obligation, not a bound on its permutation image.

Source: ATLAS HSG1-P1.M, HSG1-f4r896aB0 and HSd2G1-f2r1408B0, with source
attribution retained in the imported construction modules. The consumer is the
modular saturation proof of the degree window used in Guralnick--Malle,
Classification of 2F-modules I, Proposition 5.1, HS paragraph, and AS K.4.
-/

public section
open Sporadic.LeechRelated.HS
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.HSDegree

private theorem word_eq_relation {G : Type*} [Group G] (a b : G) (i : Fin 13) :
    AtlasPresentation.word a b i =
      Representation.HigmanSims.LargeModels.TracePair.Descent.relation a b i := by
  fin_cases i <;>
    simp [AtlasPresentation.word, AtlasPresentation.relatorLetters,
      AtlasPresentation.letter,
      Representation.HigmanSims.LargeModels.TracePair.Descent.relation,
      pow_succ, mul_assoc, mul_inv_rev]

open Representation.HigmanSims.LargeModels.TracePair in
/-- The two literal presentation maps have the same marked generators and
relators. Faithfulness of the signed-word map supplies the word-kernel contract. -/
theorem relatorsPresentCarrier_of_faithful
    (hf : Function.Injective AtlasPresentation.toCarrier) :
    Descent.RelatorsPresentCarrier := by
  let f : AtlasPresentation.Universal →* Descent.Presentation :=
    AtlasPresentation.pairHom (PresentedGroup.of false) (PresentedGroup.of true) (by
      intro i
      rw [word_eq_relation]
      have h := PresentedGroup.one_of_mem (rels := Descent.relators) ⟨i, rfl⟩
      rw [Descent.relator, Descent.map_relation] at h
      exact h)
  have hcomp : Descent.presentedToCarrier.comp f = AtlasPresentation.toCarrier := by
    apply PresentedGroup.ext
    intro i
    change Descent.presentedToCarrier (f (AtlasPresentation.generator i)) =
      AtlasPresentation.toCarrier (AtlasPresentation.generator i)
    cases i <;> simp only [f, AtlasPresentation.pairHom_generator_false,
      AtlasPresentation.pairHom_generator_true, AtlasPresentation.toCarrier_generator_false,
      AtlasPresentation.toCarrier_generator_true, Descent.presentedToCarrier_a,
      Descent.presentedToCarrier_b]
  have hsurj : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← PresentedGroup.closure_range_of (rels := Descent.relators)]
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨i, rfl⟩
    cases i
    · exact ⟨AtlasPresentation.generator false,
        AtlasPresentation.pairHom_generator_false ..⟩
    · exact ⟨AtlasPresentation.generator true,
        AtlasPresentation.pairHom_generator_true ..⟩
  apply Descent.relatorsPresentCarrier_of_injective
  intro x y hxy
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨b, rfl⟩ := hsurj y
  apply congrArg f
  apply hf
  simpa only [← hcomp, MonoidHom.comp_apply] using hxy

open Representation.HigmanSims.LargeModels

/-- The actual degree-896 action and its Frobenius conjugate, including the
trace separating them, require only the remaining carrier-presentation proof. -/
theorem traceSeparatedPairExists_of_presentationFaithful
    (hf : Function.Injective AtlasPresentation.toCarrier) : TraceSeparatedPairExists :=
  traceSeparatedPairExists_of_certificates
    (fun _ => TracePair.Descent.MatrixRelations.markedAction_exists
      (relatorsPresentCarrier_of_faithful hf))
    TracePair.matrixAlgebraFull TracePair.trace_matrixA_mul_matrixB

/-- The degree-1408 restriction is absolutely irreducible on the literal HS
carrier once its marked presentation map is proved faithful. -/
theorem restrictedModelExists_of_presentationFaithful
    (hf : Function.Injective AtlasPresentation.toCarrier) : RestrictedModelExists :=
  restrictedModelExists_of_descent_and_density
    (Restricted1408.matrixDescentExists_of_presentation (fun _ => hf)
      Restricted1408.matrixRelations)
    Restricted1408.matrixAlgebraIsFull

end CFSG.Quasithin.ChapterK.SporadicCatalogue.HSDegree
