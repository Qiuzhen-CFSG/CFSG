module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionEndpointsPoint
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.PointInvolution
/-!
# The ordinary point graph centralizer

Transport the binary fixed-point group through the literal projective and
completion maps, obtaining D₁ ≃ C₂ × S₄ as in F.5.3, p.300.
-/
noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
private def ordinaryPointFixedEquiv : modelFixed false ≃* graphFixedPoint := by
  let e : pointParabolicSU F (form F σ hσ) ≃* ordinaryEndpoint false :=
    UnitaryTwo.PointInvolution.matrixPointEquiv
  have hm (a : pointParabolicSU F (form F σ hσ)) :
      e a ∈ modelFixed false ↔ a ∈ graphFixedPoint := by
    change ordinaryInclusion false (e a) ∈ centralizer ({modelGraph false} : Set (modelEndpoint false)) ↔ _
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro h
      have hh := congrArg (fun x : modelEndpoint false => x.val.left) h
      change projection 1 hn a.val * Extension.projectiveAction 1 hn 1 1 =
        1 * Extension.projectiveAction 1 hn UnitaryFourOuter.generator (projection 1 hn a.val) at hh
      have he : Extension.projectiveAut 1 hn (projection 1 hn a.val) = projection 1 hn a.val := by
        simpa only [map_one, MulAut.one_apply, one_mul, mul_one,
          Extension.projectiveAction_generator] using hh.symm
      change UnitaryFourOuter.matrixHom F σ hσ a.val = a.val
      apply (projection_injective 1 hn)
      exact (Extension.projectiveAut_project 1 hn a.val).symm.trans he
    · intro h
      have he : Extension.projectiveAut 1 hn (projection 1 hn a.val) = projection 1 hn a.val :=
        (Extension.projectiveAut_project 1 hn a.val).trans (congrArg (projection 1 hn) h)
      apply Subtype.ext
      apply SemidirectProduct.ext
      · change projection 1 hn a.val * Extension.projectiveAction 1 hn 1 1 =
          1 * Extension.projectiveAction 1 hn UnitaryFourOuter.generator (projection 1 hn a.val)
        simpa only [map_one, MulAut.one_apply, one_mul, mul_one,
          Extension.projectiveAction_generator] using he.symm
      · exact one_mul _ |>.trans (mul_one _).symm
  refine {
    toFun := fun a => ⟨e.symm a.val, (hm _).mp (by rw [e.apply_symm_apply]; exact a.property)⟩
    invFun := fun a => ⟨e a.val, (hm a.val).mpr a.property⟩
    left_inv := ?_
    right_inv := ?_
    map_mul' := ?_ }
  · intro a; apply Subtype.ext; exact e.apply_symm_apply a.val
  · intro a; apply Subtype.ext; exact e.symm_apply_apply a.val
  · intro a b; apply Subtype.ext; exact map_mul e.symm a.val b.val

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
    (Extension.amalgam 1 hn) (G := G0)) (i : G0 →* G)
public def source_D_point_equiv (hi : Function.Injective i) :
    Dendpoint c i false ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4) :=
  ((modelFixed false).equivMapOfInjective (ordinaryMap c i false)
    (ordinaryMap_injective c i hi false)).symm.trans
    (ordinaryPointFixedEquiv.trans (graphFixedPointEquivLocal.trans
      EndpointPoint.graphFixedLocalEquivProduct))
/-- The inverse fixed-point identification retains the actual ordinary endpoint. -/
public theorem source_D_point_equiv_symm_val (hi : Function.Injective i)
    (a : Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) :
    ((source_D_point_equiv c i hi).symm a).val =
      ordinaryMap c i false (UnitaryTwo.PointInvolution.matrixPointEquiv
        (graphFixedPointEquivLocal.symm (EndpointPoint.graphFixedLocalEquivProduct.symm a)).val) := by
  rfl

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
