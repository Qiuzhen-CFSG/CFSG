module
public import GorensteinWalter.SL2ProjectiveCover
public import Theory.GroupTheory.Commutator.TwoCoverComparison
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction

/-!
# An involution detects triviality of a perfect central two-cover of A₅

A nontrivial central two-kernel identifies the perfect cover with SL₂(5),
by comparison with its actual projective double cover. All square-one
matrices there are scalar. Thus an involution with nontrivial image in A₅
forces the original covering map to be injective. The proof retains the
actual surjection and does not assume a multiplier or cover classification.

Source application: Aschbacher–Smith, C.5.6(7), printed p.159.
-/

public section
open Subgroup
open scoped MatrixGroups
open Matrix
namespace alternatingGroup
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem injective_of_central_two_kernel_of_involution
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hp : IsPGroup 2 f.ker)
    (a : E) (ha : a ^ 2 = 1) (hne : f a ≠ 1) : Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  by_contra hk
  obtain ⟨b⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
  let f' := b.symm.toMonoidHom.comp f
  have hfk : f'.ker = f.ker := MonoidHom.ker_comp_of_injective _ _ b.symm.injective
  obtain ⟨hg,hgc,hgcard,hg2,hperfect,hdihedral⟩ :=
    GorensteinWalter.sl2_projective_cover_model (ZMod 5) (by norm_num) (by norm_num)
  let : Group.IsPerfect SL(2,ZMod 5) := hperfect
  obtain ⟨ec⟩ := CentralExtension.commutator_mulEquiv_of_central_two_covers
    f' (GorensteinWalter.sl2ProjectiveProjection (ZMod 5)) (b.symm.surjective.comp hf) hg
    (hfk ▸ hc) hgc (hfk ▸ hp) hg2
    (by rw [hfk,Group.IsPerfect.commutator_eq_top,inf_top_eq]; exact hk) hgcard hdihedral
  let e : E ≃* SL(2,ZMod 5) := (Subgroup.topEquiv.symm.trans
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top.symm)).trans ec
  have hs : e a ^ 2 = 1 := by rw [← map_pow,ha,map_one]
  have hdet : (SpecialLinearGroup.toGL (e a)).det = 1 := by
    apply Units.ext
    exact (e a).property
  have hcSL : e a ∈ center SL(2,ZMod 5) := by
    rcases GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one
      (by decide : (2 : ZMod 5) ≠ 0) (SpecialLinearGroup.toGL (e a))
      (by rw [← map_pow,hs,map_one]) hdet with h1 | h1
    · have he1 : e a = 1 := SpecialLinearGroup.toGL_injective (by simpa using h1)
      rw [he1]
      exact one_mem _
    · have he1 : e a = -1 := Subtype.ext (congrArg Units.val h1)
      rw [he1,mem_center_iff]
      intro y
      simp
  have haC : a ∈ center E := by
    rw [mem_center_iff]
    intro y
    apply e.injective
    simpa only [map_mul] using mem_center_iff.mp hcSL (e y)
  have himage : f a ∈ center (alternatingGroup (Fin 5)) := by
    rw [mem_center_iff]
    intro z
    obtain ⟨y,rfl⟩ := hf z
    exact (map_mul f y a).symm.trans ((congrArg f (mem_center_iff.mp haC y)).trans (map_mul f a y))
  rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at himage
  exact hne himage

end alternatingGroup
