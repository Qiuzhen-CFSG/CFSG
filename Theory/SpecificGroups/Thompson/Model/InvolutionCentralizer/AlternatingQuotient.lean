module

public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.Words
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.Permutations
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.FourSpaceAction
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates

/-!
# An alternating-nine section of the Thompson involution centralizer

The literal max3 word subgroup lies in the centralizer of the standard
involution, by the checked word matrices and commutation certificates.
Its action on nine distinct four-spaces in the 29/21 section of the fixed
248-dimensional representation induces exactly the two permutations proved
to generate A₉. Restricting the action to this image gives the unconditional
surjection `quotientHom : wordSubgroup →* alternatingGroup (Fin 9)`.

The general action-to-quotient adapter is retained below, and its matrix-image
premises are discharged in the concrete construction. This proves the section
needed in Aschbacher–Smith A.2.19 without assuming splitting, ambient simplicity
or group order. It does not identify the whole centralizer or the kernel.

Source: GLS3 Table 5.3x; ATLAS `ThG1-max3W1`. The original program, attribution
and the certified linear algebra witnesses are in `AlternatingQuotient/source/`.
-/

namespace Thompson.InvolutionCentralizer.AlternatingQuotient

/-- The actual range is A₉ once the two generator images are established. -/
public theorem range_eq_alternating_of_generator_images
    (f : wordSubgroup →* Equiv.Perm (Fin 9))
    (hx : f generatorX = permA) (hy : f generatorY = permB) :
    f.range = alternatingGroup (Fin 9) := by
  have h := congrArg (Subgroup.map f) generators_closure
  rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map,
    hx, hy, closure_generators] at h
  exact h.symm

/-- Restrict the action homomorphism to its certified alternating image. -/
@[expose] public def quotientOfAction
    (f : wordSubgroup →* Equiv.Perm (Fin 9))
    (hx : f generatorX = permA) (hy : f generatorY = permB) :
    wordSubgroup →* alternatingGroup (Fin 9) :=
  f.codRestrict _ fun g => (range_eq_alternating_of_generator_images f hx hy) ▸
    (show f g ∈ f.range from ⟨g, rfl⟩)

/-- Generation supplies surjectivity; no surjectivity premise is needed. -/
public theorem quotientOfAction_surjective
    (f : wordSubgroup →* Equiv.Perm (Fin 9))
    (hx : f generatorX = permA) (hy : f generatorY = permB) :
    Function.Surjective (quotientOfAction f hx hy) := by
  intro g
  have hg : g.val ∈ f.range := by
    rw [range_eq_alternating_of_generator_images f hx hy]
    exact g.property
  obtain ⟨x, hx'⟩ := hg
  exact ⟨x, Subtype.ext hx'⟩

/-- The actual A₉ quotient of the source word subgroup in the involution
centralizer. Both matrix-image premises of the four-space action are proved. -/
@[expose] public noncomputable def quotientHom :
    wordSubgroup →* alternatingGroup (Fin 9) :=
  quotientOfAction (fourSpaceAction matrixHom_wordA matrixHom_wordB)
    (fourSpaceAction_generatorX matrixHom_wordA matrixHom_wordB)
    (fourSpaceAction_generatorY matrixHom_wordA matrixHom_wordB)

/-- The first source word has its prescribed permutation image. -/
public theorem quotientHom_generatorX :
    (quotientHom generatorX : Equiv.Perm (Fin 9)) = permA :=
  fourSpaceAction_generatorX matrixHom_wordA matrixHom_wordB

/-- The second source word has its prescribed permutation image. -/
public theorem quotientHom_generatorY :
    (quotientHom generatorY : Equiv.Perm (Fin 9)) = permB :=
  fourSpaceAction_generatorY matrixHom_wordA matrixHom_wordB

/-- The quotient is induced by matrix multiplication on the literal lifted
four-spaces. The inverse permutation matches the right row action. -/
public theorem quotientHom_map_liftedBlockSpace (g : wordSubgroup) (i : Fin 9) :
    (liftedBlockSpace i).map (matrixHom g.val).vecMulLinear =
      liftedBlockSpace ((quotientHom g : Equiv.Perm (Fin 9))⁻¹ i) :=
  fourSpaceAction_map_liftedBlockSpace matrixHom_wordA matrixHom_wordB g i

/-- The two certified generator images generate all of A₉. -/
public theorem quotientHom_surjective : Function.Surjective quotientHom :=
  quotientOfAction_surjective (fourSpaceAction matrixHom_wordA matrixHom_wordB)
    (fourSpaceAction_generatorX matrixHom_wordA matrixHom_wordB)
    (fourSpaceAction_generatorY matrixHom_wordA matrixHom_wordB)

/-- The standard Thompson involution centralizer has an actual A₉ section.
This is the section assertion from GLS3 Table 5.3x used in A.2.19. -/
public theorem exists_subgroup_surjective :
    ∃ H : Subgroup Model, H ≤ Thompson.InvolutionCentralizer.subgroup ∧
      ∃ f : H →* alternatingGroup (Fin 9), Function.Surjective f :=
  ⟨wordSubgroup, wordSubgroup_le_centralizer, quotientHom, quotientHom_surjective⟩

end Thompson.InvolutionCentralizer.AlternatingQuotient
