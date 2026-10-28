module
public import Theory.GroupTheory.CComponent.RadicalKernel
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel
public import Theory.GroupTheory.PPerfectHom

/-!
# Solvable two-perfect subgroups in a component action kernel

Let a finite intrinsic C-component have a nontrivial homomorphic image
covered by a perfect subgroup whose two-core quotient is simple. Every
normal solvable two-perfect subgroup lies in the homomorphism kernel.

The original kernel is proper and therefore solvable. Its restriction to
the covering subgroup is solvable, so the cover identifies the image's
two-core quotient with the original simple quotient. The image is perfect,
and hence its solvable radical is its two-core. The normal solvable
subgroup therefore has a two-group image, killed by two-perfectness.

Source application: Aschbacher–Smith 9.4.1, printed pp.735–736, after the
equality of the component and diagonal residual images on the reduced
center orbit. The proof uses C-component minimality from A.3.3(1), p.42.
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- A normal solvable two-perfect subgroup is invisible in a nontrivial
component image covered by a perfect subgroup with simple two-core quotient. -/
theorem solvable_twoPerfect_le_kernel_of_simple_twoCore_cover
    {G H : Type*} [Group G] [Finite G] [Group H] [Nontrivial H]
    (hG : (⊤ : Subgroup G).IsCComponent)
    (f : G →* H) (hf : Function.Surjective f)
    (B : Subgroup G) [Group.IsPerfect B] [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hB : B.map f = ⊤)
    (X : Subgroup G) [X.Normal] [Group.IsSolvable X] (hX : IsPPerfect 2 X) :
    X ≤ f.ker := by
  let : Finite H := Finite.of_surjective f hf
  have hproper : f.ker ≠ ⊤ := by
    intro ht
    have he : f = 1 := MonoidHom.ker_eq_top_iff.mp ht
    obtain ⟨y, hy⟩ := exists_ne (1 : H)
    obtain ⟨g, hg⟩ := hf y
    exact hy (hg.symm.trans (DFunLike.congr_fun he g))
  have hker := kernel_le_solvableRadical_of_top_isCComponent hG f hproper
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hker) (inclusion_injective hker)
  let b := f.comp B.subtype
  have hb : Function.Surjective b := MonoidHom.range_eq_top.mp (by
    simpa only [b, MonoidHom.range_comp, range_subtype] using hB)
  let j : b.ker →* f.ker :=
    { toFun := fun x => ⟨x.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (fun a : f.ker => (a : G)) hxy))
  let : Group.IsSolvable b.ker := Group.isSolvable_of_isSolvable_injective hj
  let e := PerfectCoreTwoExtension.solvableKernelQuotientEquiv b hb
  let : IsSimpleGroup (H ⧸ pCore 2 H) := e.symm.isSimpleGroup
  let : Group.IsPerfect H := Group.IsPerfect.ofSurjective hb
  let : (X.map f).Normal := (inferInstance : X.Normal).map f hf
  let : Group.IsSolvable (X.map f) := Group.isSolvable_of_surjective
    (f := f.subgroupMap X) (f.subgroupMap_surjective X)
  have himage : X.map f ≤ pCore 2 H := by
    rw [← PerfectCoreTwoExtension.radical_eq_core]
    exact le_solvableRadical _ inferInstance inferInstance
  let g : X →* pCore 2 H := (f.comp X.subtype).codRestrict _
    (fun x => himage (mem_map_of_mem f x.property))
  have hg := hX.hom_eq_one_of_isPGroup pCore_isPGroup g
  intro x hx
  exact congrArg (fun k : X →* pCore 2 H => ((k ⟨x, hx⟩ : pCore 2 H) : H)) hg

end Theory.GroupTheory
