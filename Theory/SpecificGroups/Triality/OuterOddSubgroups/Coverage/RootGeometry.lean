module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.Basic
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.Generation
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.OppositeAlignment
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.SimpleRecognition

/-!
# Signed-root geometry for binary triality automorphisms

The four literal signed simple-root groups generate the genuine binary carrier.
Consequently agreement on their elements identifies automorphisms without an
additional generation premise.

For alignment, concrete Bruhat geometry conjugates the image of the opposite
unipotent subgroup back by an element of U. Intersections of the root
parabolics with that opposite subgroup recognize the negative simple roots;
opposition gives the positive roots. The root orders q³ and q remove the
possible node permutation, including at q = 2. Conjugation by the chosen
element of U retains the first Sylow normalization.

The final theorem discharges both geometric premises of the conditional
assembly below. Together with generation it supplies the two root-geometric
inputs to inner–coefficient coverage, without simplicity or perfectness
assumptions. The separate parameter-rigidity step remains with that consumer.

Source: Steinberg, Theorem 30(1) and Theorem 36,
`refs/KGroup/GLS3/Chapter2St1.tex`; GLS3 §§2.3–2.5,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace Triality.Standard.OuterOdd.Coverage.RootGeometry
open Parabolics ConcreteBruhat

/-- An actual application of the proved generation to the carrier automorphisms. -/
theorem ext_of_signed_roots (f : ℕ) (hf : 0 < f)
    {a b : MulAut (Carrier (binaryParameters f hf))}
    (h : ∀ s i t, a (rootElement (binaryParameters f hf) rfl s i t) =
      b (rootElement (binaryParameters f hf) rfl s i t)) : a = b :=
  ext_of_rootGenerators _ rfl (rootGenerators_closure_eq_top f hf) h

/-- The two independent geometric inputs yield the exact U-adjustment consumed
by automorphism coverage. The assembly owner must prove both inputs. -/
theorem exists_unipotent_rootFrame_of_opposition (f : ℕ) (hf : 0 < f)
    (halign : ∀ a : MulAut (Carrier (binaryParameters f hf)),
      (unipotent (binaryParameters f hf)).map a.toMonoidHom = unipotent (binaryParameters f hf) →
      ∃ u ∈ unipotent (binaryParameters f hf),
        (oppositeUnipotent (binaryParameters f hf) rfl).map
          (MulAut.conj u * a).toMonoidHom = oppositeUnipotent (binaryParameters f hf) rfl)
    (hrecognition : ∀ a : MulAut (Carrier (binaryParameters f hf)),
      (unipotent (binaryParameters f hf)).map a.toMonoidHom = unipotent (binaryParameters f hf) →
      (oppositeUnipotent (binaryParameters f hf) rfl).map a.toMonoidHom =
        oppositeUnipotent (binaryParameters f hf) rfl →
      ∀ s i, ∃ j, a '' Set.range (rootElement (binaryParameters f hf) rfl s i) =
        Set.range (rootElement (binaryParameters f hf) rfl s j))
    (a : MulAut (Carrier (binaryParameters f hf)))
    (ha : (unipotent (binaryParameters f hf)).map a.toMonoidHom =
      unipotent (binaryParameters f hf)) :
    ∃ u ∈ unipotent (binaryParameters f hf),
      PreservesRootFrame (binaryParameters f hf) rfl (MulAut.conj u * a) := by
  obtain ⟨u, hu, ho⟩ := halign a ha
  refine ⟨u, hu, preservesRootFrame_of_root_images _ rfl _ ?_⟩
  exact hrecognition _ (unipotent_invariant_after_conj _ a ha u hu) ho

/-- Every automorphism preserving U can be adjusted by an element of U to
preserve each literal signed simple-root group. This supplies the alignment
input to inner–coefficient coverage for every positive binary exponent,
including f = 1, with both geometric premises discharged. -/
theorem exists_unipotent_rootFrame (f : ℕ) (hf : 0 < f)
    (a : MulAut (Carrier (binaryParameters f hf)))
    (ha : (unipotent (binaryParameters f hf)).map a.toMonoidHom =
      unipotent (binaryParameters f hf)) :
    ∃ u ∈ unipotent (binaryParameters f hf),
      PreservesRootFrame (binaryParameters f hf) rfl (MulAut.conj u * a) :=
  exists_unipotent_rootFrame_of_opposition f hf
    (exists_unipotent_opposite_invariant f hf)
    (root_images_of_opposite_invariant f hf) a ha

end Triality.Standard.OuterOdd.Coverage.RootGeometry
