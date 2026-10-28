module
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicSolvable
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup

/-!
# Two-local normalizers in the automorphism group of G₂(2)′

The actual conjugation equivalence identifies Aut(G₂(2)′) with G₂(2).
Every nonidentity two-subgroup of this full group has normalizer in a
conjugate of one of its two parabolics. Both binary parabolics are solvable,
so the automorphism normalizer is solvable. The two-subgroup may contain
outer automorphisms; no intersection with the derived group is assumed.

Source: Aschbacher--Smith F.1.12, pp.263--264, and the constrained
source exclusion in C.4.3--8 and 12.1.11, pp.152--154,794.
-/

public noncomputable section
open Subgroup
namespace Atlas.G2.BinaryAutomorphismTwoNormalizer
open LieParabolicSetup LieAutomorphismExtensions

private theorem solvable_of_image_le {G H : Type*} [Group G] [Group H]
    (A : Subgroup G) (B : Subgroup H) [Group.IsSolvable B]
    (f : G →* H) (hf : Function.Injective f) (hAB : A.map f ≤ B) :
    Group.IsSolvable A := by
  let j : A →* B := (f.comp A.subtype).codRestrict B
    (fun a => hAB (mem_map_of_mem f a.property))
  apply Group.isSolvable_of_isSolvable_injective (f := j)
  intro a b hab
  exact Subtype.ext (hf (congrArg Subtype.val hab))

/-- Every actual nontrivial two-subgroup of G₂(2) has solvable normalizer. -/
theorem normalizer_isSolvable (R : Subgroup (Model (ZMod 2)))
    (hR : R ≠ ⊥) (hpR : IsPGroup 2 R) :
    Group.IsSolvable (normalizer (R : Set (Model (ZMod 2)))) := by
  obtain ⟨g, hg | hg⟩ :=
    EvenLocal.NormalizerCover.normalizer_conjugate_le_parabolic R hR hpR
  · let : Group.IsSolvable (parabolic₁ (F := ZMod 2)) :=
      BinaryParabolicSolvable.parabolic_isSolvable (by simp) 0
    exact solvable_of_image_le _ _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective hg
  · let : Group.IsSolvable (parabolic₂ (F := ZMod 2)) :=
      BinaryParabolicSolvable.parabolic_isSolvable (by simp) 1
    exact solvable_of_image_le _ _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective hg

/-- This includes two-subgroups containing outer automorphisms of G₂(2)′. -/
theorem automorphism_normalizer_isSolvable
    (R : Subgroup (MulAut (commutator (Model (ZMod 2)))))
    (hR : R ≠ ⊥) (hpR : IsPGroup 2 R) :
    Group.IsSolvable (normalizer (R : Set (MulAut (commutator (Model (ZMod 2)))))) := by
  let e := binaryAutomorphismEquiv.symm
  let S := R.map e.toMonoidHom
  have hS : S ≠ ⊥ := fun h => hR ((R.map_eq_bot_iff_of_injective e.injective).mp h)
  let : Group.IsSolvable (normalizer (S : Set (Model (ZMod 2)))) :=
    normalizer_isSolvable S hS (hpR.map _)
  exact solvable_of_image_le _ _ e.toMonoidHom e.injective (R.le_normalizer_map _)

end Atlas.G2.BinaryAutomorphismTwoNormalizer
