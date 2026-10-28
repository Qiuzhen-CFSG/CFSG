module

public import Theory.SpecificGroups.Lyons.GebhardtMatrixRealizationSetup
public import Theory.SpecificGroups.Lyons.GebhardtMatrixCertificateSetup

/-!
# Word certificates for realizing Gebhardt's presentation

Four words in the literal ATLAS local pair and one word in the ambient pair
specify candidate images of `a,b,c,d,z`. Two further words in these five
images recover the ambient generators. A certificate consists of the 25
relator identities and the two recovery identities in the faithful matrix
representation. The universal property of the presentation then gives a
surjective homomorphism; membership of the first four images in the specified
local subgroup follows directly from their words.

The explicit correspondence is in `GebhardtMatrixWords`. This module assembles
independent word-image and finite-product certificates; it does not assert that
these kernel certificates exist.

Source: V. Gebhardt, "Two Short Presentations for Lyons' Sporadic Simple
Group", Experimental Mathematics 9 (2000), 333–338, Section 3B. See
`GebhardtPresentation` for the literal relations and `Atlas111OrderSetup`
for the exact local pair. The source's five generators are distinct from
the two ATLAS standard generators.
-/

namespace Lyons.Gebhardt.MatrixRealization

/-- Faithfulness turns the matrix checks into the presentation's relations. -/
public theorem WordCertificate.relations_hold {w : WordData} (h : WordCertificate w) :
    ∀ r ∈ relators, FreeGroup.lift w.assignment r = 1 := by
  intro r hr
  apply matrixRepresentation_injective
  exact (h.relations r hr).trans (map_one matrixRepresentation).symm

/-- The universal homomorphism determined by a checked word certificate. -/
@[expose] public def WordCertificate.hom {w : WordData} (h : WordCertificate w) :
    Presentation →* LyonsGroup :=
  PresentedGroup.toGroup h.relations_hold

/-- The universal homomorphism has exactly the chosen generator images. -/
@[simp] public theorem WordCertificate.hom_generator {w : WordData} (h : WordCertificate w)
    (i : Alphabet) : h.hom (generator i) = w.assignment i :=
  PresentedGroup.toGroup.of h.relations_hold

/-- Evaluation commutes with passage to the presented group. -/
public theorem WordCertificate.hom_mk {w : WordData} (h : WordCertificate w)
    (v : FreeGroup Alphabet) :
    h.hom (PresentedGroup.mk relators v) = FreeGroup.lift w.assignment v := rfl

/-- The first recovery identity puts the first ATLAS generator in the image. -/
public theorem WordCertificate.generatorA_mem_range {w : WordData} (h : WordCertificate w) :
    generatorA ∈ h.hom.range := by
  refine ⟨PresentedGroup.mk relators w.recoverA, ?_⟩
  rw [h.hom_mk]
  apply matrixRepresentation_injective
  exact h.recoverA

/-- The second recovery identity puts the second ATLAS generator in the image. -/
public theorem WordCertificate.generatorB_mem_range {w : WordData} (h : WordCertificate w) :
    generatorB ∈ h.hom.range := by
  refine ⟨PresentedGroup.mk relators w.recoverB, ?_⟩
  rw [h.hom_mk]
  apply matrixRepresentation_injective
  exact h.recoverB

/-- Recovering the two fixed ATLAS generators proves surjectivity. -/
public theorem WordCertificate.surjective {w : WordData} (h : WordCertificate w) :
    Function.Surjective h.hom := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← OrderCertificate.closure_generators]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact h.generatorA_mem_range
  · exact Set.mem_singleton_iff.mp hx ▸ h.generatorB_mem_range

/-- The universal homomorphism sends the first four generators into the local subgroup. -/
public theorem WordCertificate.local_generator_mem {w : WordData} (h : WordCertificate w)
    (i : Alphabet) (hi : i.val < 4) :
    h.hom (generator i) ∈ OrderCertificate.localSubgroup := by
  rw [h.hom_generator]
  exact w.assignment_mem i hi

/-- The precise realization needed to transport the independent abstract cover. -/
public theorem realization_of_wordCertificate {w : WordData} (h : WordCertificate w) :
    ∃ f : Presentation →* LyonsGroup, Function.Surjective f ∧
      ∀ i : Alphabet, i.val < 4 → f (generator i) ∈ OrderCertificate.localSubgroup :=
  ⟨h.hom, h.surjective, h.local_generator_mem⟩

/-- Assemble the independently certifiable local images, outer image, and
finite products for the discovered concrete correspondence. -/
public theorem realization_of_matrixCertificates
    (hl : ∀ i : Alphabet, i.val < 4 → CertificateInputs.GeneratorImageCertificate i)
    (hz : CertificateInputs.GeneratorImageCertificate 4)
    (hp : CertificateInputs.ProductCertificate) :
    ∃ f : Presentation →* LyonsGroup, Function.Surjective f ∧
      ∀ i : Alphabet, i.val < 4 → f (generator i) ∈ OrderCertificate.localSubgroup :=
  realization_of_wordCertificate (CertificateInputs.wordCertificate_of_images_products
    (CertificateInputs.imageCertificate_of_local_outer hl hz) hp)

end Lyons.Gebhardt.MatrixRealization
