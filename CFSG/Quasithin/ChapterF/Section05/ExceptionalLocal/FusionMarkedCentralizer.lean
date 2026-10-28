module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionLocalTable
public import Theory.Representation.BinaryAlternatingFiveExtension.SylowCommutator.MarkedCentralizer
/-!
# The two marked centers in the source short centralizer

The original source Sylow comparison retains the plane core, so its exact
cyclic graph commutator selects one factor-center line. The source central
root maps to the unique nonidentity center of the wreath Sylow. Restriction
to the short centralizer, followed by a fixed factor swap, sends the literal
short root to `(r 2,1)` and the literal central root to `(r 2,r 2)`.

These two marks are needed for the quotient of the graph-centralizer Sylow
by its central graph involution in Aschbacher--Smith F.5.5, pp.301--302.
Only the original source hypotheses are used.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open BinaryPermutation.AlternatingFiveExtension SylowModel SylowCommutator
open scoped commutatorElement
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

/-- The short-centralizer comparison sends the literal short and central roots to the first and diagonal factor centers. -/
theorem source_short_Tcentralizer_marked_iso (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) :
    ∃ d : Tcentralizer c i (sourceMarkedShort c i) ≃* DihedralGroup 4 × DihedralGroup 4,
      (∀ x, x.val=sourceMarkedShort c i → d x=(DihedralGroup.r 2,1)) ∧
      (∀ x, x.val=rootElement c i z → d x=(DihedralGroup.r 2,DihedralGroup.r 2)) := by
  let T := Source.sylowImage c i
  let fT : T := ⟨Source.graphElement c i,source_graph_mem_sylowImage c i⟩
  let tT : T := ⟨sourceMarkedShort c i,source_short_mem_sylowImage c i⟩
  let zT : T := ⟨rootElement c i z,source_root_mem_sylowImage c i z h⟩
  obtain ⟨e,he⟩ := exists_source_marked_sylow_equiv c i h.embedding_injective
  have hcomm : ⁅(Q c i true).subgroupOf T,zpowers fT⁆=zpowers tT := by
    apply map_injective T.subtype_injective
    rw [map_commutator,subgroupOf_map_subtype,
      inf_eq_left.mpr (source_Q_plane_le_sylowImage c i),
      MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    exact source_short_commutator c i h.embedding_injective
  have hcomm' := congrArg (fun K : Subgroup T => K.map e.toMonoidHom) hcomm
  rw [map_commutator,he,MonoidHom.map_zpowers,MonoidHom.map_zpowers] at hcomm'
  obtain ⟨u,hu⟩ : e tT∈baseMap.range := by
    rw [←he]
    exact mem_map_of_mem _ (source_short_mem_Q c i)
  have huo : orderOf (baseMap u)=2 := by
    rw [hu,e.orderOf_eq]
    exact (orderOf_injective T.subtype T.subtype_injective tT).symm.trans
      (source_short_order c i h.embedding_injective)
  change ⁅baseMap.range,zpowers (e fT)⁆=zpowers (e tT) at hcomm'
  rw [←hu] at hcomm'
  have hzT : zT∈center T := by
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp
      ((source_root_centralizer c i z h).symm ▸ (sylowImage_le_M c i false x.property))
  have hzE : e zT∈center PlaneWreath := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hzT x)
  have hz1 : e zT≠1 := by
    intro hh
    have hz0 : rootElement c i z=1 := congrArg Subtype.val (e.injective (hh.trans e.map_one.symm))
    have ho := source_root_order c i z h
    rw [hz0,orderOf_one] at ho
    omega
  obtain ⟨d,htd,hzd⟩ := exists_marked_cyclic_centralizer (e fT) (e zT) u huo hcomm' hzE hz1
  let a : Tcentralizer c i (sourceMarkedShort c i) ≃* centralizer ({tT} : Set T) := {
    toFun x := ⟨⟨x.val,x.property.1⟩,mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2))⟩
    invFun x := ⟨x.val.val,x.val.property,mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  let b : centralizer ({tT} : Set T) ≃* centralizer ({e tT} : Set PlaneWreath) := {
    toFun x := ⟨e x.val,mem_centralizer_singleton_iff.mpr (by
      simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp x.property))⟩
    invFun y := ⟨e.symm y.val,mem_centralizer_singleton_iff.mpr (by
      apply e.injective
      simpa only [map_mul,e.apply_symm_apply] using mem_centralizer_singleton_iff.mp y.property)⟩
    left_inv x := Subtype.ext (e.symm_apply_apply x.val)
    right_inv y := Subtype.ext (e.apply_symm_apply y.val)
    map_mul' x y := Subtype.ext (e.map_mul x.val y.val) }
  let q := MulEquiv.subgroupCongr (congrArg (fun v => centralizer ({v} : Set PlaneWreath)) hu.symm)
  let E := a.trans (b.trans (q.trans d))
  have hval (x : Tcentralizer c i (sourceMarkedShort c i)) :
      (q (b (a x))).val=e ⟨x.val,x.property.1⟩ := rfl
  refine ⟨E,?_,?_⟩
  · intro x hx
    apply htd
    change (q (b (a x))).val=baseMap u
    rw [hval,hu]
    apply congrArg e
    exact Subtype.ext hx
  · intro x hx
    apply hzd
    change (q (b (a x))).val=e zT
    rw [hval]
    apply congrArg e
    exact Subtype.ext hx

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
