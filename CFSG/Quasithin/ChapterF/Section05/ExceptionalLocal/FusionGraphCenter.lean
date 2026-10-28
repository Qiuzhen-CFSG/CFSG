module
public import Theory.Representation.BinaryAlternatingFiveExtension.SylowGraphCenter
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionLocalTable
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionRootFusion

/-!
# The original graph-centralizer center and short-root fusion

The marked affine comparison of the source Sylow preserves its literal plane
core. Transporting `[Q₂,f] = <t>` and `|C_T(f)| = 32` through that comparison
identifies the eight possible elements of `Z(Tf)`. The unique nontrivial
Sylow-central involution is the original source root. The model factor swap
also supplies an explicit element of the source Sylow conjugating `t` to `tz`.

The final theorem applies both facts to the exceptional root-moving normalizer
argument, retaining the conjugator inside `R ∨ Q₂`. The independent endpoint
Sylow and graph-to-short fusion inputs remain explicit for their producers.
Source: Aschbacher--Smith F.4.37, printed p.293, and F.5.3, printed p.300.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open BinaryPermutation.AlternatingFiveExtension
open SylowModel SylowCommutator SylowGraphCenter
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)
local notation "T" => Source.sylowImage c i

private def graphInT : T := ⟨Source.graphElement c i,source_graph_mem_sylowImage c i⟩
private def shortInT : T := ⟨sourceMarkedShort c i,source_short_mem_sylowImage c i⟩
private def rootInT (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z) : T :=
  ⟨rootElement c i z,source_root_mem_sylowImage c i z h⟩

variable [Finite G]

private theorem source_marked_coordinates (hi : Function.Injective i)
    (e : T ≃* PlaneWreath)
    (he : ((Q c i true).subgroupOf T).map e.toMonoidHom = baseMap.range) :
    ∃ u : V4, e (shortInT c i) = baseMap u ∧ orderOf (baseMap u) = 2 ∧
      ⁅baseMap.range,zpowers (e (graphInT c i))⁆ = zpowers (baseMap u) := by
  have hcomm : ⁅(Q c i true).subgroupOf T,zpowers (graphInT c i)⁆ =
      zpowers (shortInT c i) := by
    apply map_injective (T).subtype_injective
    rw [map_commutator,subgroupOf_map_subtype,
      inf_eq_left.mpr (source_Q_plane_le_sylowImage c i),
      MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    exact source_short_commutator c i hi
  have hcomm' := congrArg (fun U : Subgroup T => U.map e.toMonoidHom) hcomm
  rw [map_commutator,he,MonoidHom.map_zpowers,MonoidHom.map_zpowers] at hcomm'
  obtain ⟨u,hu⟩ : e (shortInT c i) ∈ baseMap.range := by
    rw [←he]
    exact mem_map_of_mem _ (source_short_mem_Q c i)
  have huo : orderOf (baseMap u) = 2 := by
    rw [hu,e.orderOf_eq]
    exact (orderOf_injective (T).subtype (T).subtype_injective (shortInT c i)).symm.trans
      (source_short_order c i hi)
  change ⁅baseMap.range,zpowers (e (graphInT c i))⁆ = zpowers (e (shortInT c i)) at hcomm'
  rw [←hu] at hcomm'
  exact ⟨u,hu.symm,huo,hcomm'⟩

private theorem source_mapped_root_center (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) (e : T ≃* PlaneWreath) :
    e (rootInT c i z h) ∈ center PlaneWreath ∧ e (rootInT c i z h) ≠ 1 := by
  have hzc : rootInT c i z h ∈ center T := by
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp
      ((source_root_centralizer c i z h).symm ▸ (sylowImage_le_M c i false x.property))
  constructor
  · apply mem_center_iff.mpr
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hzc x)
  · intro he
    have hz1 : rootInT c i z h = 1 := e.injective (he.trans (map_one e).symm)
    have hz1' : rootElement c i z = 1 := congrArg Subtype.val hz1
    have ho := source_root_order c i z h
    rw [hz1',orderOf_one] at ho
    omega

private def sourceGraphCentralizerEquiv :
    centralizer ({graphInT c i} : Set T) ≃ Tf c i where
  toFun x := ⟨⟨x.val.val,mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩,x.val.property⟩
  invFun x := ⟨⟨x.val.val,x.property⟩,mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property))⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Finite G] in
private theorem source_mapped_graph_centralizer_card (hi : Function.Injective i)
    (e : T ≃* PlaneWreath) :
    Nat.card (centralizer ({e (graphInT c i)} : Set PlaneWreath)) = 32 := by
  rw [←Nat.card_congr (CentralizerSmallKernelTransport.centralizerEquiv e (graphInT c i)).toEquiv,
    Nat.card_congr (sourceGraphCentralizerEquiv c i),source_Tf_card c i hi]

/-- The original graph-centralizer center has the source's eight-element
product table, with all three involutions marked by the completion maps. -/
theorem source_Tf_center_cases (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) (x : G) (hx : x ∈ TfCenterImage c i) :
    x = 1 ∨ x = rootElement c i z ∨ x = sourceMarkedShort c i ∨
    x = sourceMarkedShort c i * rootElement c i z ∨ x = Source.graphElement c i ∨
    x = Source.graphElement c i * sourceMarkedShort c i ∨
    x = Source.graphElement c i * rootElement c i z ∨
    x = Source.graphElement c i * sourceMarkedShort c i * rootElement c i z := by
  obtain ⟨e,he⟩ := exists_source_marked_sylow_equiv c i h.embedding_injective
  obtain ⟨u,hu,huo,hcomm⟩ := source_marked_coordinates c i h.embedding_injective e he
  obtain ⟨x,hx,rfl⟩ := hx
  have hxT : x.val ∈ T := (TfImage_eq c i).le x.property |>.1
  let xT : T := ⟨x.val,hxT⟩
  have hxcomm (y : PlaneWreath) (hy : y * e (graphInT c i) = e (graphInT c i) * y) :
      e xT * y = y * e xT := by
    obtain ⟨a,rfl⟩ := e.surjective y
    have haf : a * graphInT c i = graphInT c i * a :=
      e.injective (by simpa only [map_mul] using hy)
    have haTf : a.val ∈ TfImage c i := by
      rw [TfImage_eq]
      exact ⟨a.property,mem_centralizer_singleton_iff.mpr (congrArg Subtype.val haf)⟩
    have hh := congrArg Subtype.val (mem_center_iff.mp hx (⟨a.val,haTf⟩ : TfImage c i))
    simpa only [map_mul] using congrArg e
      (show xT * a = a * xT from Subtype.ext hh.symm)
  have hfo : orderOf (e (graphInT c i)) = 2 := by
    rw [e.orderOf_eq]
    exact (orderOf_injective (T).subtype (T).subtype_injective (graphInT c i)).symm.trans
      (source_graph_order c i h.embedding_injective)
  obtain ⟨hz,hz1⟩ := source_mapped_root_center c i z h e
  have hcases := center_centralizer_cases (e (graphInT c i)) (e (rootInT c i z h)) u
    hfo huo hcomm (source_mapped_graph_centralizer_card c i h.embedding_injective e) hz hz1
    (e xT) hxcomm
  rw [←hu] at hcases
  simpa only [←map_mul,←map_one e,e.injective.eq_iff,Subtype.ext_iff,
    Subgroup.coe_one,Subgroup.coe_mul,Subgroup.subtype_apply,xT,rootInT,shortInT,graphInT] using hcases

/-- A conjugator inside the literal source Sylow exchanges t and tz. -/
theorem source_short_root_conjugator (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) :
    ∃ y ∈ T, y * sourceMarkedShort c i * y⁻¹ = sourceMarkedShort c i * rootElement c i z := by
  obtain ⟨e,he⟩ := exists_source_marked_sylow_equiv c i h.embedding_injective
  obtain ⟨u,hu,huo,hcomm⟩ := source_marked_coordinates c i h.embedding_injective e he
  obtain ⟨hz,hz1⟩ := source_mapped_root_center c i z h e
  obtain ⟨y,hy⟩ := exists_conjugator_short_root (e (graphInT c i)) (e (rootInT c i z h)) u
    huo hcomm hz hz1
  refine ⟨(e.symm y).val,(e.symm y).property,?_⟩
  have hh : e.symm y * shortInT c i * (e.symm y)⁻¹ =
      shortInT c i * rootInT c i z h := by
    apply e.injective
    simpa only [map_mul,map_inv,e.apply_symm_apply,hu] using hy
  exact congrArg Subtype.val hh

/-- The eight-element calculation discharges both concrete center-table inputs
of the exceptional root-fusion argument, retaining its located conjugator. -/
theorem source_root_fusion_from_graph_fusion (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z)
    (hpoint : ∃ S : Sylow 2 (E c i false),
      (S : Subgroup (E c i false)).map (E c i false).subtype = TfImage c i)
    (R : Sylow 2 (C c i)) (hR : Tf c i < (R : Subgroup (C c i)))
    (hft : IsConj (Source.graphElement c i) (sourceMarkedShort c i)) :
    ∃ g ∈ Rimage c i R ⊔ Q c i true,
      g * rootElement c i z * g⁻¹ = Source.graphElement c i * rootElement c i z := by
  obtain ⟨y,_,hy⟩ := source_short_root_conjugator c i z h
  exact source_root_fuses_graph_root_of_center_table c i z h hpoint R hR hft
    (isConj_iff.mpr ⟨y,hy⟩) (source_Tf_center_cases c i z h)

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
