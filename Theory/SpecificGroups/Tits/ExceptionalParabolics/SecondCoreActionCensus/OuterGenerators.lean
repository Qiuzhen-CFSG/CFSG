module
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreActionCensus.CoreAutomorphisms
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreActionCensus.CoreAutomorphismCertificate

/-!
# Five certified automorphisms of the actual second core

Each finite normal-form permutation fixes the identity and preserves right
multiplication by s3 and s7. The two-generator reconstruction consequently
makes it an automorphism of the literal two-core. The exported evaluation
lemmas retain its complete action and its exact generator images.

These are candidate lifts for the outer-quotient construction owned by
qt-e-quintic-second-parabolic. Exhaustion of the automorphism group and the
quotient relations remain separate obligations; they are not assumed here.
The tables are kernel-checked against the Atlas1600 marking of Parrott
(1972), §5, p.683, via `CoreAutomorphismCertificate`.
-/

public section
namespace Tits.ExceptionalParabolics.SecondCoreAction
namespace OuterGenerators
open CoreGenerators

private theorem perm_normalForm (n : Fin 1024) :
    CoreGenerators.perm (coreNormalForm n) = CoreAutomorphismCertificate.form n := by
  change AmalgamRigidity.SecondExtension.perm (coreNormalForm n : second) = _
  rw [coreNormalForm_val,AmalgamRigidity.SecondExtension.map_word]
  unfold CoreAutomorphismCertificate.form
  congr 1
  exact funext AmalgamRigidity.SecondExtension.perm_gen

private theorem perm_pairGenerator (i : Fin 2) :
    CoreGenerators.perm (pairGenerator i) =
      ![AmalgamRigidity.SecondExtension.packedGen 3,
        AmalgamRigidity.SecondExtension.packedGen 7] i := by
  fin_cases i <;> exact perm_generator _

private theorem transitions (n : Fin 1024) (i : Fin 2) :
    coreNormalForm (CoreAutomorphismCertificate.next n i) =
      coreNormalForm n * pairGenerator i := by
  apply eq_of_points
  · simpa only [map_mul,perm_normalForm,perm_pairGenerator] using
      (CoreAutomorphismCertificate.transitions n i).1
  · simpa only [map_mul,perm_normalForm,perm_pairGenerator] using
      (CoreAutomorphismCertificate.transitions n i).2

private theorem image_transitions (a : Fin 5) (n : Fin 1024) (i : Fin 2) :
    coreNormalForm (CoreAutomorphismCertificate.image a (CoreAutomorphismCertificate.next n i)) =
      coreNormalForm (CoreAutomorphismCertificate.image a n) *
        coreNormalForm (CoreAutomorphismCertificate.image a (pairIndex i)) := by
  apply eq_of_points
  · simpa only [map_mul,perm_normalForm,pairIndex] using
      (CoreAutomorphismCertificate.image_transitions a n i).1
  · simpa only [map_mul,perm_normalForm,pairIndex] using
      (CoreAutomorphismCertificate.image_transitions a n i).2

private theorem image_bijective (a : Fin 5) :
    Function.Bijective (CoreAutomorphismCertificate.image a) :=
  (Function.LeftInverse.injective (CoreAutomorphismCertificate.image_left_inverse a)).bijective_of_finite

/-- Five certified assignments on the actual core. Their role in the outer
quotient is a separate assertion, not part of this construction. -/
noncomputable def candidateAut (a : Fin 5) : MulAut Core :=
  ofTransitions CoreAutomorphismCertificate.next transitions
    (CoreAutomorphismCertificate.image a) (image_bijective a)
    (CoreAutomorphismCertificate.image_zero a) (image_transitions a)

theorem candidateAut_normalForm (a : Fin 5) (n : Fin 1024) :
    candidateAut a (coreNormalForm n) =
      coreNormalForm (CoreAutomorphismCertificate.image a n) :=
  ofTransitions_apply _ _ _ _ _ _ n

theorem candidateAut_generators (a : Fin 5) :
    candidateAut a (generator 2) =
      coreNormalForm (CoreAutomorphismCertificate.generatorImages a).1 ∧
    candidateAut a (generator 6) =
      coreNormalForm (CoreAutomorphismCertificate.generatorImages a).2 := by
  change candidateAut a (coreNormalForm 4) = _ ∧ candidateAut a (coreNormalForm 256) = _
  rw [candidateAut_normalForm,candidateAut_normalForm,
    (CoreAutomorphismCertificate.generatorImages_eq a).1,
    (CoreAutomorphismCertificate.generatorImages_eq a).2]
  exact ⟨rfl,rfl⟩

end OuterGenerators
end Tits.ExceptionalParabolics.SecondCoreAction
