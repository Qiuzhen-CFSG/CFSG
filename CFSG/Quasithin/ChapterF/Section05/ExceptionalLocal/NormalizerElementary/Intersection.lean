module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerElementary.PlaneMarking

/-!
# Intersection of the two literal mixed elementary cores

The marked Sylow equivalence sends A₂ to a mixed coordinate subgroup.
Conjugation outside C_T(t) exchanges the two factors, whose intersection
is the center together with the short axis. Mapping back uses the proved
source identity Z(T)=⟨z⟩, giving A₂∩A₂ʸ=⟨z,t⟩.

Source: Aschbacher–Smith F.5.4(4), printed p.301, used in F.5.5.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open BinaryPermutation.AlternatingFiveExtension
open SylowModel SylowCommutator ElementaryCoordinates
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
  (t : G) (hf : FusionFacts c i z t)
local notation "T" => Source.sylowImage c i

private theorem map_center_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (center X).map e.toMonoidHom = center Y := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    apply mem_center_iff.mpr
    intro b
    obtain ⟨b,rfl⟩ := e.surjective b
    change e b * e a = e a * e b
    simpa only [map_mul] using congrArg e (mem_center_iff.mp ha b)
  · intro hx
    refine ⟨e.symm x,mem_center_iff.mpr ?_,e.apply_symm_apply x⟩
    intro a
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using mem_center_iff.mp hx (e a)

include h hf in
/-- The two conjugate mixed cores meet in the literal four-group generated
by the source root and short involutions. -/
theorem normalizer_plane_A_intersection (y : G) (hy : y∈T)
    (hyt : y∉Tcentralizer c i t) :
    A c i true ⊓ (A c i true).map (MulAut.conj y).toMonoidHom =
      zpowers (rootElement c i z) ⊔ zpowers t := by
  obtain ⟨e,j,hQ,ht,hA⟩ := exists_plane_A_coordinates c i z h t hf
  let J : PlaneWreath →* G := (T).subtype.comp e.symm.toMonoidHom
  have hJ : Function.Injective J := (T).subtype_injective.comp e.symm.injective
  have hcomp : J.comp e.toMonoidHom = (T).subtype := by
    ext x
    exact congrArg Subtype.val (e.symm_apply_apply x)
  have hAT : A c i true ≤ T :=
    (A_le_TfImage c i z t hf true).trans ((TfImage_eq c i) ▸ inf_le_left)
  have hAm : (mixed j).map J = A c i true := by
    rw [←hA,map_map,hcomp,map_subgroupOf_eq_of_le hAT]
  have htJ : J (baseMap (axis j)) = t := by
    rw [←ht]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨t,hf.t_mem⟩)
  let Y : PlaneWreath := e ⟨y,hy⟩
  have hYJ : J Y = y := congrArg Subtype.val (e.symm_apply_apply ⟨y,hy⟩)
  have hYr : Y.right ≠ 1 := by
    intro hr
    have hcomm := (centralizer_axis_test j Y).mpr hr
    have he : y*t=t*y := by
      simpa only [map_mul,hYJ,htJ] using congrArg J hcomm
    exact hyt ⟨hy,mem_centralizer_singleton_iff.mpr he⟩
  have hconj : ((mixed j).map (MulAut.conj Y).toMonoidHom).map J =
      (A c i true).map (MulAut.conj y).toMonoidHom := by
    rw [←hAm,map_map,map_map]
    congr 1
    ext a
    change J (Y*a*Y⁻¹) = y*J a*y⁻¹
    rw [map_mul,map_mul,map_inv,hYJ]
  have hcenter : (center PlaneWreath).map J = zpowers (rootElement c i z) := by
    rw [←map_center_equiv e,map_map,hcomp,source_sylowImage_center_eq_pointRoot c i z h,
      pointRootImage_eq_zpowers c i z h]
  calc
    _ = ((mixed j) ⊓ (mixed j).map (MulAut.conj Y).toMonoidHom).map J := by
      rw [map_inf _ _ _ hJ,hAm,hconj]
    _ = centralFour.map J := by
      rw [mixed_conjugate,if_neg hYr,mixed_inf_opposite]
    _ = _ := by
      rw [centralFour_eq_center_sup_axis j,Subgroup.map_sup,hcenter,MonoidHom.map_zpowers,htJ]

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
