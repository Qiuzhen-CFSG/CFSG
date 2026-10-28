module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.ModelDefs

/-!
# Intrinsic preservation of the two marked cubic directions

A cover automorphism preserving the marked residual preserves its center
image in the two-core quotient. If the parabolic is the residual's intrinsic
normalizer, it also preserves the image of the parabolic's commutator.
These statements keep the actual restricted and quotient automorphisms.
The model normalizer equality itself is a separate geometric calculation.

Source use: Aschbacher–Smith, 13.8.16(1), printed p.952 (PDF p.969), with
Notation 13.2.1 and Lemma 13.2.2, pp.877–878.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer.Model

private theorem residualAut_preserves_subgroup (x : Theory.SpecificGroups.SymmetricSix.BinaryPoint)
    (a : MulAut Cover) (ha : (residual x).map a.toMonoidHom = residual x)
    (A : Subgroup Cover) (hA : A.map a.toMonoidHom = A) :
    (A.subgroupOf (residual x)).map (residualAut x a ha).toMonoidHom =
      A.subgroupOf (residual x) := by
  ext r
  rw [mem_map_equiv]
  change (↑((residualAut x a ha).symm r) : Cover) ∈ A ↔ (r : Cover) ∈ A
  have he : (↑((residualAut x a ha).symm r) : Cover) = a.symm (r : Cover) := by
    apply a.injective
    change (↑(residualAut x a ha ((residualAut x a ha).symm r)) : Cover) = _
    simp
  rw [he, ← mem_map_equiv, hA]

private theorem sectionAut_preserves_image (x : Theory.SpecificGroups.SymmetricSix.BinaryPoint)
    (a : MulAut Cover) (ha : (residual x).map a.toMonoidHom = residual x)
    (A : Subgroup Cover) (hA : A.map a.toMonoidHom = A) :
    ((A.subgroupOf (residual x)).map (QuotientGroup.mk' (pCore 2 (residual x)))).map
      (sectionAut x a ha).toMonoidHom =
      (A.subgroupOf (residual x)).map (QuotientGroup.mk' (pCore 2 (residual x))) := by
  have he : (sectionAut x a ha).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (residual x))) =
      (QuotientGroup.mk' (pCore 2 (residual x))).comp (residualAut x a ha).toMonoidHom := by
    ext r
    exact sectionAut_mk x a ha r
  rw [map_map, he, ← map_map, residualAut_preserves_subgroup x a ha A hA]

theorem sectionAut_scalarLine (x : Theory.SpecificGroups.SymmetricSix.BinaryPoint)
    (a : MulAut Cover) (ha : (residual x).map a.toMonoidHom = residual x) :
    (scalarLine x).map (sectionAut x a ha).toMonoidHom = scalarLine x :=
  sectionAut_preserves_image x a ha (center Cover)
    (characteristic_iff_map_eq.mp inferInstance a)

theorem sectionAut_derivedLine (x : Theory.SpecificGroups.SymmetricSix.BinaryPoint)
    (a : MulAut Cover) (ha : (residual x).map a.toMonoidHom = residual x)
    (hP : (parabolic x).map a.toMonoidHom = parabolic x) :
    (derivedLine x).map (sectionAut x a ha).toMonoidHom = derivedLine x := by
  apply sectionAut_preserves_image
  rw [map_subtype_commutator, map_commutator, hP]

theorem parabolic_preserved_of_normalizer_eq
    (x : Theory.SpecificGroups.SymmetricSix.BinaryPoint)
    (hN : normalizer (residual x : Set Cover) = parabolic x)
    (a : MulAut Cover) (ha : (residual x).map a.toMonoidHom = residual x) :
    (parabolic x).map a.toMonoidHom = parabolic x := by
  rw [← hN, map_normalizer_eq_of_bijective _ a.bijective, ha]

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer.Model

end
