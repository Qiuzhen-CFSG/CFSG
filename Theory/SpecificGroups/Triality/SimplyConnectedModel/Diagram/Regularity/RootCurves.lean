module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Diagram.Torus

/-!
# Regular restrictions of a pinned point map to every Spin root

Reflection induction expresses each signed root curve as a conjugate of a
signed simple root curve by the fixed source normalizer words. The pinned
point map is regular on simple curves; fixed conjugation therefore propagates
regularity to all 24 curves. The regular inverse of the root parametrization
then gives regularity on the corresponding closed root subgroup.

Source: GLS3, Theorems 1.12.1(h) and 1.15.2(a).
-/

@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.Diagram
open Theory Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Pinning
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

private def conjugateCurve (c : Points k)
    (g : AlgebraicGroup.Morphism (KPlus k) (groupVariety k)) :
    AlgebraicGroup.Morphism (KPlus k) (groupVariety k) where
  toVariety := (conjugationByMorphism (groupVariety k) c).comp g.toVariety
  map_one := by
    change (conjugationByMorphism (groupVariety k) c).toFun (g.onPoints 1) = 1
    rw [map_one, conjugationByMorphism_apply, mul_one, mul_inv_cancel]
  map_mul x y := by
    change (conjugationByMorphism (groupVariety k) c).toFun (g.onPoints (x*y)) =
      (conjugationByMorphism (groupVariety k) c).toFun (g.onPoints x) *
      (conjugationByMorphism (groupVariety k) c).toFun (g.onPoints y)
    simp only [map_mul, conjugationByMorphism_apply]
    group

/-- Regularity propagates from the signed simple roots to every root curve. -/
theorem IsPinned.exists_rootMorphism {f : Points k →* Points k}
    (hf : IsPinned k f) (r : RootIndex) :
    ∃ g : AlgebraicGroup.Morphism (KPlus k) (groupVariety k),
      ∀ a : k, g.onPoints (kPlusPoint a) = f (rootPoint k r a) := by
  let P (s : RootIndex) := ∃ g : AlgebraicGroup.Morphism (KPlus k) (groupVariety k),
    ∀ a : k, g.onPoints (kPlusPoint a) = f (rootPoint k s a)
  have h : P r ∧ P (negativeRoot r) := by
    apply (typeDRootPairing_base 2).induction_reflect r
    · intro s hs
      simpa only [reflection_self_negativeRoot, negativeRoot_negativeRoot] using hs.symm
    · intro s hs
      obtain ⟨i, hi⟩ := (typeDRootPairing_baseEquiv 2).surjective ⟨s, hs⟩
      have his : simpleRoot i = s := congrArg Subtype.val hi
      rw [← his]
      constructor
      · refine ⟨cliffordRootMorphism k (simpleRoot (typeD4DiagramPermutation i)), ?_⟩
        intro a
        rw [cliffordRootMorphism_kPlusPoint]
        exact (hf.1 i a).symm
      · refine ⟨cliffordRootMorphism k (negativeRoot (simpleRoot (typeD4DiagramPermutation i))), ?_⟩
        intro a
        rw [cliffordRootMorphism_kPlusPoint]
        exact (hf.2 i a).symm
    · intro s j hs hj
      obtain ⟨i, hi⟩ := (typeDRootPairing_baseEquiv 2).surjective ⟨j, hj⟩
      have hij : simpleRoot i = j := congrArg Subtype.val hi
      rw [← hij]
      have hconj (t : RootIndex) (ht : P t) :
          P ((typeDRootPairing 2).reflectionPerm (simpleRoot i) t) := by
        obtain ⟨g, hg⟩ := ht
        refine ⟨conjugateCurve k (f (Pinning.simpleNormalizer k i))⁻¹ g, ?_⟩
        intro a
        change (conjugationByMorphism (groupVariety k) (f (Pinning.simpleNormalizer k i))⁻¹).toFun
          (g.onPoints (kPlusPoint a)) = _
        rw [conjugationByMorphism_apply, hg, inv_inv,
          ← simpleNormalizer_rootPoint_conjugation, map_mul, map_mul, map_inv]
      refine ⟨hconj s hs.1, ?_⟩
      rw [← reflection_negativeRoot]
      exact hconj (negativeRoot s) hs.2
  exact h.1

/-- The regular restriction to the entire closed root subgroup, with exact
agreement on every point rather than only on a dense parameter set. -/
theorem IsPinned.exists_rootRestriction {f : Points k →* Points k}
    (hf : IsPinned k f) (r : RootIndex) :
    ∃ g : AlgebraicGroup.Morphism (rootClosedSubgroup k r).carrierVariety (groupVariety k),
      ∀ x, g.onPoints x = f ((rootClosedSubgroup k r).inclusion.onPoints x) := by
  obtain ⟨g, hg⟩ := hf.exists_rootMorphism k r
  refine ⟨g.comp (rootParameter k r), ?_⟩
  intro x
  change g.onPoints ((rootParameter k r).onPoints x) = _
  rw [← kPlusPoint_coordinate ((rootParameter k r).onPoints x), hg]
  have h := congrArg (rootClosedSubgroup k r).inclusion.onPoints
    (rootSubgroupPoint_rootParameter k r x)
  rw [rootSubgroupPoint_inclusion] at h
  exact congrArg f h

end Triality.SimplyConnected.Diagram
