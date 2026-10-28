module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.LocalRestrictions.SecondExtension.ImagePowers
public import Theory.SpecificGroups.Tits.AmalgamRigidity.LocalRestrictions.SecondExtension.ImageConjugates
public import Theory.SpecificGroups.Tits.AmalgamRigidity.LocalRestrictions.SecondExtension.ImageCosets
public import Theory.SpecificGroups.Tits.AmalgamRigidity.LocalRestrictions.SecondExtension.ImageInverses
public import Theory.SpecificGroups.Tits.AmalgamRigidity.LocalRestrictions.SecondExtension.Transport
import Mathlib.Tactic.FinCases

/-!
# The two marked assignments satisfy collection and generation

The original equations come from the existing Atlas certificates. The proposed
images satisfy exactly the same equations by the new point certificates.
Explicit inverse words prove generation, so the graph construction will give
an automorphism, rather than only an endomorphism.
Source and discovery conventions: `Images` and Parrott (1972), §5, p.683.
-/

@[expose] public section
namespace Tits.AmalgamRigidity.SecondExtension
open ExceptionalParabolics RelativeSecondBlockLayers
open OuterOddSubgroups.OverlapCentralizers

theorem gen_sylowRelations : SylowRelations gen := by
  apply SylowRelations.of_injective perm perm_injective
  have he : perm ∘ gen = packedGen := funext perm_gen
  rw [he]
  constructor
  · simpa [packedGen, Packed.perm_eq, Packed.generator, parrottRelator,
      Atlas1600ParrottData.permutation] using
      Atlas1600ParrottData.relations .i_s1
  · simpa [packedGen, Packed.perm_eq, Packed.generator, parrottRelator,
      Atlas1600ParrottData.permutation] using
      Atlas1600ParrottData.relations .i_s2
  · simpa [packedGen, Packed.perm_eq, Packed.generator, parrottRelator,
      Atlas1600ParrottData.permutation] using
      Atlas1600ParrottData.relations .i_s3
  · simpa [packedGen, Packed.perm_eq, Packed.generator, parrottRelator,
      Atlas1600ParrottData.permutation] using
      Atlas1600ParrottData.relations .i_s4
  · simpa [packedGen, Packed.perm_eq, Packed.generator, parrottRelator,
      Atlas1600ParrottData.permutation] using
      Atlas1600ParrottData.relations .i_s5
  · simpa [packedGen, Packed.perm_eq, Packed.generator, parrottRelator,
      Atlas1600ParrottData.permutation] using
      Atlas1600ParrottData.relations .i_s6
  · simpa [packedGen, Packed.perm_eq, Packed.generator, parrottRelator,
      Atlas1600ParrottData.permutation] using
      Atlas1600ParrottData.relations .i_s7
  · simpa [packedGen, Packed.perm_eq, Packed.generator, parrottRelator,
      Atlas1600ParrottData.permutation] using
      Atlas1600ParrottData.relations .i_s8
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_2_1
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_3_1
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_3_2
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_4_1
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_4_2
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_4_3
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_5_1
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_5_2
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_5_3
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_5_4
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_6_1
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_6_2
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_6_3
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_6_4
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_6_5
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_7_1
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_7_2
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_7_3
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_7_4
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_7_5
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_7_6
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_8_1
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_8_2
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_8_3
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_8_4
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_8_5
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_8_6
  · simpa [packedGen, Packed.perm_eq, Packed.generator] using
      Atlas1600SylowTwoCertificate.conjugate_8_7

theorem images_sylowRelations : SylowRelations (images gen) := by
  apply SylowRelations.of_injective perm perm_injective
  have he : perm ∘ images gen = packedImage := funext perm_images
  rw [he]
  constructor
  · exact image_power_1
  · exact image_power_2
  · exact image_power_3
  · exact image_power_4
  · exact image_power_5
  · exact image_power_6
  · exact image_power_7
  · exact image_power_8
  · exact image_conjugate_2_1
  · exact image_conjugate_3_1
  · exact image_conjugate_3_2
  · exact image_conjugate_4_1
  · exact image_conjugate_4_2
  · exact image_conjugate_4_3
  · exact image_conjugate_5_1
  · exact image_conjugate_5_2
  · exact image_conjugate_5_3
  · exact image_conjugate_5_4
  · exact image_conjugate_6_1
  · exact image_conjugate_6_2
  · exact image_conjugate_6_3
  · exact image_conjugate_6_4
  · exact image_conjugate_6_5
  · exact image_conjugate_7_1
  · exact image_conjugate_7_2
  · exact image_conjugate_7_3
  · exact image_conjugate_7_4
  · exact image_conjugate_7_5
  · exact image_conjugate_7_6
  · exact image_conjugate_8_1
  · exact image_conjugate_8_2
  · exact image_conjugate_8_3
  · exact image_conjugate_8_4
  · exact image_conjugate_8_5
  · exact image_conjugate_8_6
  · exact image_conjugate_8_7

theorem gen_cosetRelations : CosetRelations gen := by
  intro a i
  apply Subtype.ext
  change SecondOrder.rep i * SecondOrder.generator a = _
  rw [Subgroup.coe_mul, word_gen_val, rep_gen_val]
  exact SecondOrder.step a i

theorem images_cosetRelations : CosetRelations (images gen) := by
  intro a i
  apply perm_injective
  simp only [map_mul, map_word, map_rep, perm_images]
  have he : perm ∘ images gen = packedImage := funext perm_images
  rw [he]
  fin_cases a
  · exact image_step_0 i
  · exact image_step_1 i
  · exact image_step_2 i
  · exact image_step_3 i
  · exact image_step_4 i
  · exact image_step_5 i
  · exact image_step_6 i
  · exact image_step_7 i
  · exact image_step_8 i

theorem images_inverse (a : Fin 9) :
    word (images gen) (inverseIndex a).1 * rep (images gen) (inverseIndex a).2 = gen a := by
  apply perm_injective
  simp only [map_mul, map_word, map_rep, perm_gen]
  have he : perm ∘ images gen = packedImage := funext perm_images
  rw [he]
  fin_cases a
  · exact image_inverse_0
  · exact image_inverse_1
  · exact image_inverse_2
  · exact image_inverse_3
  · exact image_inverse_4
  · exact image_inverse_5
  · exact image_inverse_6
  · exact image_inverse_7
  · exact image_inverse_8

theorem images_generate : Subgroup.closure (Set.range (images gen)) = ⊤ := by
  apply top_unique
  rw [← gen_generates]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨a, rfl⟩
  rw [← images_inverse a]
  exact normalForm_mem (images gen) (inverseIndex a)

end Tits.AmalgamRigidity.SecondExtension
