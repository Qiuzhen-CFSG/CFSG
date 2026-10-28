module
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionAlternatingQuotient.Setup
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionAlternatingQuotient.PairOrbit

/-!
# The alternating quotient from the concrete Lyons pair orbit

A certified family of 55 distinct matrices supplies eleven distinct stars.
Conjugation by each literal local generator induces its specified even
permutation on those stars. Subgroup closure propagates the action, injectivity
of the star labeling makes its restriction a homomorphism, and the two generator
images generate A₁₁. This constructs the map in the required matrix-to-permutation
direction without assuming that the central extension splits.

The kernel-checked `pairOrbitCertificate` instantiates the general construction
to give the unconditional `quotient` and `quotient_surjective`. The explicit
matrix family is retained in `Atlas111InvolutionAlternatingQuotient/source/`.
These exports discharge the quotient-map premise of the chapter consumer
`CFSG.Quasithin.ChapterA.lyonsA11SectionOfSurjective`.

Source: GLS3 section 5.3, Lyons involution table, printed p.278; ATLAS
`LyG1-f5r111B0` and the exact subgroup program `LyG1-max4W1`.
-/

namespace Lyons.SimplicityCertificate.AlternatingQuotient

private theorem star_invariance (C : PairOrbitCertificate) (g : involutionLocalSubgroup) :
    ∃ p : alternatingGroup (Fin 11), ∀ i,
      matrixSetAction (g : LyonsGroup) (star C i) = star C (p.val i) := by
  have h : involutionLocalSubgroup ≤
      (Theory.GroupAction.permutationLiftSubgroup (star C) (alternatingGroup (Fin 11))).comap
        matrixSetAction := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    change ∃ p ∈ alternatingGroup (Fin 11), ∀ i,
      matrixSetAction g (star C i) = star C (p i)
    rcases hg with rfl | rfl
    · exact ⟨letterA, letterA_even, star_actionA C⟩
    · exact ⟨letterB, letterB_even, star_actionB C⟩
  obtain ⟨p, hp, he⟩ := h g.property
  exact ⟨⟨p, hp⟩, he⟩

/-- The matrix orbit certificate gives a homomorphism from the literal word subgroup. -/
public noncomputable def quotientOfPairOrbit (C : PairOrbitCertificate) :
    involutionLocalSubgroup →* alternatingGroup (Fin 11) :=
  Theory.GroupAction.permutationLiftHom
    (matrixSetAction.comp involutionLocalSubgroup.subtype) (star C) (star_injective C)
    (alternatingGroup (Fin 11)) (star_invariance C)

public theorem quotientOfPairOrbit_A (C : PairOrbitCertificate) :
    quotientOfPairOrbit C ⟨involutionLocalA, involutionLocalA_mem⟩ =
      ⟨letterA, letterA_even⟩ :=
  Theory.GroupAction.permutationLiftHom_eq _ _ _ _ _ _ _ (star_actionA C)

public theorem quotientOfPairOrbit_B (C : PairOrbitCertificate) :
    quotientOfPairOrbit C ⟨involutionLocalB, involutionLocalB_mem⟩ =
      ⟨letterB, letterB_even⟩ :=
  Theory.GroupAction.permutationLiftHom_eq _ _ _ _ _ _ _ (star_actionB C)

/-- Surjectivity follows from the two specified generator images, without any
ambient or local group-order assumption. -/
public theorem quotientOfPairOrbit_surjective (C : PairOrbitCertificate) :
    Function.Surjective (quotientOfPairOrbit C) := by
  let f := (alternatingGroup (Fin 11)).subtype.comp (quotientOfPairOrbit C)
  have h : Subgroup.closure {letterA, letterB} ≤ f.range := by
    apply (Subgroup.closure_le _).mpr
    intro p hp
    rcases hp with rfl | rfl
    · refine ⟨⟨involutionLocalA, involutionLocalA_mem⟩, ?_⟩
      exact congrArg Subtype.val (quotientOfPairOrbit_A C)
    · refine ⟨⟨involutionLocalB, involutionLocalB_mem⟩, ?_⟩
      exact congrArg Subtype.val (quotientOfPairOrbit_B C)
  rw [closure_letters] at h
  intro p
  obtain ⟨g, hg⟩ := h p.property
  exact ⟨g, Subtype.ext hg⟩

/-- The alternating quotient of the subgroup given by the literal ATLAS words,
constructed from its certified matrix conjugation action. -/
public noncomputable def quotient :
    involutionLocalSubgroup →* alternatingGroup (Fin 11) :=
  quotientOfPairOrbit pairOrbitCertificate

/-- The image of the first literal subgroup generator. -/
public theorem quotient_A :
    quotient ⟨involutionLocalA, involutionLocalA_mem⟩ =
      ⟨letterA, letterA_even⟩ :=
  quotientOfPairOrbit_A pairOrbitCertificate

/-- The image of the second literal subgroup generator. -/
public theorem quotient_B :
    quotient ⟨involutionLocalB, involutionLocalB_mem⟩ =
      ⟨letterB, letterB_even⟩ :=
  quotientOfPairOrbit_B pairOrbitCertificate

/-- The concrete Lyons involution subgroup surjects onto A₁₁, with no additional
certificate, group-order or identification hypothesis. -/
public theorem quotient_surjective : Function.Surjective quotient :=
  quotientOfPairOrbit_surjective pairOrbitCertificate

end Lyons.SimplicityCertificate.AlternatingQuotient
