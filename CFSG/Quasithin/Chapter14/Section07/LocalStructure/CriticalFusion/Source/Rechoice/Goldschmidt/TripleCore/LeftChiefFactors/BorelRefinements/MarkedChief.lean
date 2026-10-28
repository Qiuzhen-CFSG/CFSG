module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.BorelRefinements.DualCore
public import Theory.GroupTheory.NoncentralChiefRefinement.ConjugationPullback

/-!
# Chief refinements for the marked Borel and its normalizer

For any surjective actor map to a subgroup between the marked Borel and its
S₅ normalizer, pull back the actual invariant F₄-line. Its two irreducible
noncentral binary factors give two chief factors on any literal section
surjecting onto the natural module. The annihilator flag gives two factors
when the literal contragredient embeds in the section. Finally the actual
root, in additive F₄ coordinates, pulls back to one chief factor above the
actor kernel. Taking the actor to be either endpoint gives the Borel and
normalizer assertions with their original markings and quotient maps.

These are the three model contributions used in Aschbacher–Smith 14.7.70,
printed p.1074/PDF p.1091. SourceChief applies them to the original sections.
-/

@[expose] public section
noncomputable section
open Subgroup NoncentralChiefRefinement Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
open Representation.SL2FourNatural Representation.SL2FourNatural.BorelDualCore
variable (r : ChapterJ.L2FourAction) (A : Subgroup ChapterJ.S5)
  (hBA : borel r ≤ A) (hAN : A ≤ normalizer r)
  {K : Type*} [Group K] (q : K →* A)

/-- The invariant natural line pulled back along the specified actor map. -/
def pulledLine : Subrepresentation ((actorNatural r A).comp q) where
  toSubmodule := (actorLine r A hAN).toSubmodule
  apply_mem_toSubmodule k _ hv := (actorLine r A hAN).apply_mem_toSubmodule (q k) hv

include hBA in
theorem pulledLine_irreducible (hq : Function.Surjective q) :
    IsIrreducible (pulledLine r A hAN q).toRepresentation := by
  change IsIrreducible ((actorLine r A hAN).toRepresentation.comp q)
  exact (irreducible_comp_surjective_iff q hq _).mpr (actorLine_irreducible r A hBA hAN)

include hBA in
theorem pulledQuotient_irreducible (hq : Function.Surjective q) :
    IsIrreducible (pulledLine r A hAN q).quotientRepresentation := by
  change IsIrreducible ((actorQuotient r A hAN).comp q)
  exact (irreducible_comp_surjective_iff q hq _).mpr (actorQuotient_irreducible r A hBA hAN)

include hBA in
theorem pulled_factors_noncentral (hq : Function.Surjective q) :
    (∃ k v, (pulledLine r A hAN q).toRepresentation k v ≠ v) ∧
    (∃ k v, (pulledLine r A hAN q).quotientRepresentation k v ≠ v) := by
  constructor
  · obtain ⟨a, v, hv⟩ := actorLine_noncentral r A hBA hAN
    obtain ⟨k, rfl⟩ := hq a
    exact ⟨k, v, hv⟩
  · obtain ⟨a, v, hv⟩ := actorQuotient_noncentral r A hBA hAN
    obtain ⟨k, rfl⟩ := hq a
    exact ⟨k, v, hv⟩

variable [Finite K] {C D : NormalNode K}

include hBA hAN in
/-- An equivariant natural quotient supplies two factors for either marked actor. -/
theorem exists_naturalChief_of_actorMap (hq : Function.Surjective q) (hCD : C ≤ D)
    (f : Section C D →* Multiplicative SL2FourNatural.V) (hf : Function.Surjective f)
    (he : ∀ k x, (f (sectionAction C D k x)).toAdd =
      actorNatural r A (q k) (f x).toAdd) :
    ∃ s : ChiefSeries K, s.head = C ∧ s.last = D ∧ 2 ≤ s.noncentralTwoCount := by
  let := pulledLine_irreducible r A hBA hAN q hq
  let := pulledQuotient_irreducible r A hBA hAN q hq
  obtain ⟨hP, hQ⟩ := pulled_factors_noncentral r A hBA hAN q hq
  exact BinaryFlag.exists_refinement_of_surjection hCD (pulledLine r A hAN q) hP hQ f hf he

include hBA hAN in
/-- An embedded literal contragredient supplies two factors; surjectivity of the embedding
is neither needed nor asserted. The annihilator reverses the original flag. -/
theorem exists_dualChief_of_actorMap (hq : Function.Surjective q) (hCD : C ≤ D)
    (j : Multiplicative (Module.Dual (ZMod 2) SL2FourNatural.V) →* Section C D)
    (hj : Function.Injective j)
    (he : ∀ k v, j (Multiplicative.ofAdd (Representation.dual ((actorNatural r A).comp q) k v)) =
      sectionAction C D k (j (Multiplicative.ofAdd v))) :
    ∃ s : ChiefSeries K, s.head = C ∧ s.last = D ∧ 2 ≤ s.noncentralTwoCount := by
  let P := pulledLine r A hAN q
  let := pulledLine_irreducible r A hBA hAN q hq
  let := pulledQuotient_irreducible r A hBA hAN q hq
  let := annihilator_irreducible ((actorNatural r A).comp q) P
  let := annihilatorQuotient_irreducible ((actorNatural r A).comp q) P
  obtain ⟨hP, hQ⟩ := pulled_factors_noncentral r A hBA hAN q hq
  exact BinaryFlag.exists_refinement_of_embedding hCD (annihilator _ P)
    (annihilator_noncentral _ P hQ) (annihilatorQuotient_noncentral _ P hP) j hj he

omit [Finite K] in
/-- Actual quotient coordinates on the preimage of the marked root, over the original
actor kernel. Specializing A to the Borel or normalizer gives its two-core section. -/
def pulledCoreCoordinates (hq : Function.Surjective q) :
    SectionCoordinates (ConjugationPullback.kernelNode q)
      (ConjugationPullback.preimageNode q (rootNode r A hBA hAN))
      ((actorCore r A hAN).comp q) 1 :=
  ConjugationPullback.coordinates q (rootNode r A hBA hAN) (actorCore r A hAN)
    (actorCoreCoordinates r A hBA hAN) (actorCoreCoordinates_equivariant r A hBA hAN) hq

omit [Finite K] in
/-- The pulled-back core is one noncentral binary chief factor, with literal endpoints. -/
theorem exists_coreChief_of_actorMap (hq : Function.Surjective q) :
    ∃ s : ChiefSeries K, s.head = ConjugationPullback.kernelNode q ∧
      s.last = ConjugationPullback.preimageNode q (rootNode r A hBA hAN) ∧
      s.length = 1 ∧ s.noncentralTwoCount = 1 := by
  let := actorCore_irreducible r A hBA hAN
  exact ConjugationPullback.exists_chief q (rootNode r A hBA hAN) (actorCore r A hAN)
    (actorCoreCoordinates r A hBA hAN) (actorCoreCoordinates_equivariant r A hBA hAN)
    hq (actorCore_noncentral r A hBA hAN)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
