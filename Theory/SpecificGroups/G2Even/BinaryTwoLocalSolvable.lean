module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicSolvable
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup

/-!
# Two-local solvability for binary G₂ and its derived automorphism group

Every nontrivial two-subgroup of G₂(2) has solvable normalizer: the normalizer
is conjugate into one of the two binary parabolics, both of which are solvable.
The actual isomorphism Aut(G₂(2)′) ≅ G₂(2) transports the same assertion to the
full automorphism group of the derived group.

This supplies the G₂(2)′ exclusion in Aschbacher–Smith C.4.1 and 4.3.7,
pp.151–153 and 615–616. The concrete octonion and parabolic results are inherited
from the licensed ATLAS port; see LICENSES/ATLAS.txt. No upstream code is copied.
-/

public section
open Subgroup Theory.GroupTheory
namespace Atlas.G2
open LieParabolicSetup

theorem binary_two_normalizer_solvable
    (R : Subgroup (Model (ZMod 2))) (hR : R ≠ ⊥) (hp : IsPGroup 2 R) :
    Group.IsSolvable (normalizer (R : Set (Model (ZMod 2)))) := by
  obtain ⟨g,hg⟩ := EvenLocal.NormalizerCover.normalizer_conjugate_le_parabolic R hR hp
  let N := normalizer (R : Set (Model (ZMod 2)))
  have hs : Group.IsSolvable (N.map (MulAut.conj g).toMonoidHom) := by
    rcases hg with hg | hg
    · let : Group.IsSolvable (parabolic₁ (F := ZMod 2)) :=
        BinaryParabolicSolvable.parabolic_isSolvable (by simp) 0
      exact Group.isSolvable_of_isSolvable_injective (inclusion_injective hg)
    · let : Group.IsSolvable (parabolic₂ (F := ZMod 2)) :=
        BinaryParabolicSolvable.parabolic_isSolvable (by simp) 1
      exact Group.isSolvable_of_isSolvable_injective (inclusion_injective hg)
  let := hs
  exact Group.isSolvable_of_isSolvable_injective
    (f := (N.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toMonoidHom)
    (N.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).injective

/-- Two-local solvability in the actual automorphism group of G₂(2)′. -/
theorem binaryDerived_aut_two_normalizer_solvable
    (R : Subgroup (MulAut (commutator (Model (ZMod 2)))))
    (hR : R ≠ ⊥) (hp : IsPGroup 2 R) :
    Group.IsSolvable (normalizer (R : Set (MulAut (commutator (Model (ZMod 2)))))) := by
  let e := LieAutomorphismExtensions.binaryAutomorphismEquiv.symm
  have hs := binary_two_normalizer_solvable (R.map e.toMonoidHom)
    (fun he => hR ((R.map_eq_bot_iff_of_injective e.injective).mp he)) (hp.map _)
  rw [← map_equiv_normalizer_eq R e] at hs
  let : Group.IsSolvable ((normalizer (R : Set _)).map e.toMonoidHom) := hs
  let f := (normalizer (R : Set _)).equivMapOfInjective e.toMonoidHom e.injective
  exact Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective

end Atlas.G2
