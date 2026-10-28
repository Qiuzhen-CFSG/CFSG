module

public import Theory.SpecificGroups.BinaryLinear.PerfectRadicalRows
public import Theory.SpecificGroups.PSL3Two.ProperSubgroups

/-!
# Recognition of the full marked binary 2+3 parabolic

A subgroup containing the radical and a nontrivial perfect subgroup is the
whole parabolic as soon as it induces the full action on the marked plane.
The perfect subgroup fixes the plane. Its image on the three-dimensional
quotient is nontrivial and perfect, hence full: every proper subgroup of
SL₃(2) is solvable. This supplies the second diagonal factor independently
of the given action on the plane.
-/

public noncomputable section

open Subgroup
namespace BinaryLinear
open SmallParabolicLevi OuterCyclic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A subgroup of the marked 2+3 parabolic containing its radical and a
nontrivial perfect subgroup is full if its action on the plane is full. -/
theorem parabolic_eq_top_of_perfect_subgroup_of_subspaceAction_surjective
    (W : Submodule (ZMod 2) V)
    (hV : Module.finrank (ZMod 2) V = 5)
    (hW : Module.finrank (ZMod 2) W = 2)
    (M J : Subgroup (parabolic W)) [Group.IsPerfect J]
    (hJ : J ≠ ⊥) (hJM : J ≤ M)
    (hR : (radical W).subgroupOf (parabolic W) ≤ M)
    (hM : Function.Surjective ((subspaceAction W).comp M.subtype)) :
    M = ⊤ := by
  let : Nontrivial J := (nontrivial_iff_ne_bot J).mpr hJ
  have hs := perfect_subspaceAction_eq_one W J.subtype hW
  have hQ : Module.finrank (ZMod 2) (V ⧸ W) = 3 := by
    have hd := W.finrank_quotient_add_finrank
    omega
  let b : (V ⧸ W) ≃ₗ[ZMod 2] Space 3 :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hQ)
  let e := (linearGroupCongr b).trans (slEquivLinear 3).symm
  let f := e.toMonoidHom.comp ((quotientAction W).comp J.subtype)
  have hf : f ≠ 1 := by
    intro hf
    have hjrad (j : J) : (j.val : BinaryLinear.GL V) ∈ radical W := by
      have hj : j.val ∈ (blockAction W).ker := by
        apply MonoidHom.mem_ker.mpr
        apply Prod.ext
        · exact DFunLike.congr_fun hs j
        · apply e.injective
          change f j = e 1
          rw [hf, MonoidHom.one_apply, map_one]
      rw [ker_blockAction] at hj
      exact hj
    let r : J →* radical W :=
      ((parabolic W).subtype.comp J.subtype).codRestrict _ hjrad
    let : Group.IsSolvable (radical W) := Group.isSolvable_of_comm (by
      intro x y
      exact Subtype.ext (radical_commute W x.property y.property))
    let : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective
      (f := r) (by
        intro x y h
        have hxy : (x.val : BinaryLinear.GL V) = (y.val : BinaryLinear.GL V) :=
          congrArg (fun z : radical W => (z : BinaryLinear.GL V)) h
        exact Subtype.ext (Subtype.ext hxy))
    exact Group.IsPerfect.not_isSolvable J inferInstance
  have hfs : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    by_contra hproper
    let : Group.IsSolvable f.range :=
      Matrix.PSL3Two.isSolvable_subgroup_SL_of_ne_top f.range hproper
    let : Group.IsPerfect f.range := Group.IsPerfect.range f
    let : Nontrivial f.range := (nontrivial_iff_ne_bot _).mpr
      (fun h => hf (MonoidHom.range_eq_bot_iff.mp h))
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  have hqs : Function.Surjective ((quotientAction W).comp J.subtype) := by
    intro q
    obtain ⟨j, hj⟩ := hfs (e q)
    exact ⟨j, e.injective hj⟩
  apply eq_top_iff.mpr
  intro g _
  obtain ⟨m, hm⟩ := hM (subspaceAction W g)
  obtain ⟨j, hj⟩ := hqs ((quotientAction W m.val)⁻¹ * quotientAction W g)
  have hblock : blockAction W (m.val * j.val) = blockAction W g := by
    apply Prod.ext
    · change subspaceAction W (m.val * j.val) = subspaceAction W g
      rw [map_mul, show subspaceAction W j.val = 1 from DFunLike.congr_fun hs j,
        mul_one]
      exact hm
    · change quotientAction W (m.val * j.val) = quotientAction W g
      rw [map_mul, show quotientAction W j.val = _ from hj,
        mul_inv_cancel_left]
  have hk : (m.val * j.val)⁻¹ * g ∈ (blockAction W).ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_inv, hblock, inv_mul_cancel]
  rw [ker_blockAction] at hk
  have hh := M.mul_mem (M.mul_mem m.property (hJM j.property)) (hR hk)
  simpa only [mul_inv_cancel_left] using hh

end BinaryLinear
