module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionResidualGenerators
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionResidualDihedralFinite
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionOrdinaryQuotient
/-!
# The residual dihedral join and its literal graph-quotient image

The four endpoint generator comparisons identify O₂(O²(D₁)) and
O₂(O²(D₂)) with the two Klein four-groups of the faithful eight-matrix
model. Their join is D₈, lies in T_f and O²(C_G(f)), and injects into the
actual quotient by the graph involution. The endpoint S₄ conjugators show
that every involution of its quotient image is conjugate to the image of
tz. The dihedral equivalence sends this precise element to r².

The final theorem packages the literal subgroup, quotient maps, central
mark, and fusion needed by the successive-transfer step of F.5.5.
Source: Aschbacher–Smith, printed pp.301–302.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open ResidualJoinModel
local notation "hn" => Nat.le_refl 1
local notation "D8" => DihedralGroup 4
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0)) (i : G0 →* G)

theorem sourceEndpointResidualCore_point (hi : Function.Injective i) :
    sourceEndpointResidualCore c i false=pointFour.map (sourceHom c i) := by
  rw [sourceEndpointResidualCore_eq_map c i hi false]
  exact core_map_eq_pointFour_map _ _ (sourceEndpointCoreMap_point0 c i hi)
    (sourceEndpointCoreMap_point1 c i hi)

theorem sourceEndpointResidualCore_plane (hi : Function.Injective i) :
    sourceEndpointResidualCore c i true=planeFour.map (sourceHom c i) := by
  rw [sourceEndpointResidualCore_eq_map c i hi true]
  exact core_map_eq_planeFour_map _ _ (sourceEndpointCoreMap_plane0 c i hi)
    (sourceEndpointCoreMap_plane1 c i hi)

theorem sourceResidualJoin_eq_range (hi : Function.Injective i) :
    sourceResidualJoin c i=(sourceHom c i).range := by
  rw [sourceResidualJoin,sourceEndpointResidualCore_point c i hi,
    sourceEndpointResidualCore_plane c i hi,four_map_sup_eq_range]

def sourceResidualJoinEquiv (hi : Function.Injective i) : sourceResidualJoin c i ≃* D8 :=
  (MulEquiv.subgroupCongr (sourceResidualJoin_eq_range c i hi)).trans
    (MonoidHom.ofInjective (sourceHom_injective c i hi)).symm

theorem sourceResidualJoin_le_ordinary (hi : Function.Injective i) :
    sourceResidualJoin c i≤sourceOrdinaryUpper c i := by
  rw [sourceResidualJoin_eq_range c i hi]
  rintro _ ⟨a,rfl⟩
  exact sourceHom_mem_ordinary c i a

theorem sourceResidualJoin_le_Tf (hi : Function.Injective i) :
    sourceResidualJoin c i≤TfImage c i := by
  intro x hx
  exact ⟨⟨x,sourceResidualJoin_le_C c i hx⟩,
    sourceOrdinaryUpper_le_sylowImage c i (sourceResidualJoin_le_ordinary c i hi hx),rfl⟩

def sourceResidualJoinQuotientEquiv (hi : Function.Injective i) :
    sourceResidualJoinQuotient c i ≃* D8 :=
  (sourceOrdinaryGraphQuotientEquiv c i hi (sourceResidualJoin c i)
    (sourceResidualJoin_le_ordinary c i hi) (sourceResidualJoin_le_C c i)).symm.trans
      (sourceResidualJoinEquiv c i hi)

theorem sourceResidualJoin_involution_conjugate (hi : Function.Injective i)
    (x : G) (hx : x∈sourceResidualJoin c i) (hx2 : x^2=1) (hx1 : x≠1) :
    ∃ g∈C c i, g*x*g⁻¹=sourceHom c i (.r 2) := by
  rw [sourceResidualJoin_eq_range c i hi] at hx
  obtain ⟨a,rfl⟩ := hx
  have ha2 : a^2=1 := sourceHom_injective c i hi (by simpa only [map_pow,map_one] using hx2)
  have hz1 : sourceHom c i (.r 2)≠1 := by
    intro hh
    exact common_center_mem.2.2 (sourceHom_injective c i hi (hh.trans (map_one _).symm))
  have hf (b : Bool) (ha : sourceHom c i a∈sourceEndpointResidualCore c i b)
      (hz : sourceHom c i (.r 2)∈sourceEndpointResidualCore c i b) :
      ∃g∈C c i,g*sourceHom c i a*g⁻¹=sourceHom c i (.r 2) := by
    obtain ⟨g,hg,he⟩ := sourceEndpointResidualCore_conjugate c i hi b _ ha hx1 _ hz hz1
    exact ⟨g,((Dendpoint_le_E c i b).trans inf_le_right) hg,he⟩
  rcases involution_mem_four a ha2 with hp | hp
  · apply hf false
    · rw [sourceEndpointResidualCore_point c i hi]
      exact mem_map_of_mem _ hp
    · rw [sourceEndpointResidualCore_point c i hi]
      exact mem_map_of_mem _ common_center_mem.1
  · apply hf true
    · rw [sourceEndpointResidualCore_plane c i hi]
      exact mem_map_of_mem _ hp
    · rw [sourceEndpointResidualCore_plane c i hi]
      exact mem_map_of_mem _ common_center_mem.2.1

def sourceResidualCenterInC (hi : Function.Injective i) : C c i :=
  ⟨sourceHom c i (.r 2),sourceResidualJoin_le_C c i
    ((sourceResidualJoin_eq_range c i hi).symm ▸ ⟨.r 2,rfl⟩)⟩

def sourceResidualQuotientCenter (hi : Function.Injective i) : graphCentralQuotient c i :=
  QuotientGroup.mk' (zpowers (graphInCentralizer c i)) (sourceResidualCenterInC c i hi)

theorem sourceResidualQuotientCenter_mem (hi : Function.Injective i) :
    sourceResidualQuotientCenter c i hi∈sourceResidualJoinQuotient c i := by
  refine ⟨sourceResidualCenterInC c i hi,?_,rfl⟩
  change sourceHom c i (.r 2)∈sourceResidualJoin c i
  rw [sourceResidualJoin_eq_range c i hi]
  exact ⟨.r 2,rfl⟩

theorem sourceResidualJoinQuotient_involution_conjugate (hi : Function.Injective i)
    (x : graphCentralQuotient c i) (hx : x∈sourceResidualJoinQuotient c i)
    (hx2 : orderOf x=2) : IsConj x (sourceResidualQuotientCenter c i hi) := by
  obtain ⟨a,ha,rfl⟩ := hx
  let u : sourceResidualJoin c i := ⟨a.val,ha⟩
  let q := sourceOrdinaryGraphQuotientMap c i (sourceResidualJoin c i) (sourceResidualJoin_le_C c i)
  have hq : Function.Injective q := sourceOrdinaryGraphQuotientMap_injective c i hi _
    (sourceResidualJoin_le_ordinary c i hi) (sourceResidualJoin_le_C c i)
  have huo : orderOf u=2 := (orderOf_injective q hq u).symm.trans hx2
  have hao : orderOf a.val=2 := (orderOf_coe u).trans huo
  have ha2 : a.val^2=1 := by rw [←hao]; exact pow_orderOf_eq_one _
  have ha1 : a.val≠1 := by intro he; rw [he,orderOf_one] at hao; omega
  obtain ⟨g,hg,he⟩ := sourceResidualJoin_involution_conjugate c i hi a.val ha ha2 ha1
  let gC : C c i := ⟨g,hg⟩
  have hC : gC*a*gC⁻¹=sourceResidualCenterInC c i hi := Subtype.ext he
  exact (QuotientGroup.mk' (zpowers (graphInCentralizer c i))).map_isConj
    (isConj_iff.mpr ⟨gC,hC⟩)

theorem sourceResidualJoinQuotient_le_R (hi : Function.Injective i)
    (R : Sylow 2 (C c i)) (hR : Tf c i≤R) :
    sourceResidualJoinQuotient c i≤(R : Subgroup (C c i)).map
      (QuotientGroup.mk' (zpowers (graphInCentralizer c i))) := by
  apply map_mono
  intro x hx
  apply hR
  have hh := sourceResidualJoin_le_Tf c i hi hx
  exact (mem_map_iff_mem (C c i).subtype_injective).mp hh

theorem sourceResidualCenterInC_val (hi : Function.Injective i)
    (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z) :
    (sourceResidualCenterInC c i hi).val=sourceMarkedShort c i*rootElement c i z :=
  sourceHom_center c i z h

theorem sourceResidualJoinQuotientEquiv_center (hi : Function.Injective i) :
    sourceResidualJoinQuotientEquiv c i hi
      ⟨sourceResidualQuotientCenter c i hi,sourceResidualQuotientCenter_mem c i hi⟩ = .r 2 := by
  let e : sourceResidualJoin c i ≃* sourceResidualJoinQuotient c i := sourceOrdinaryGraphQuotientEquiv c i hi (sourceResidualJoin c i)
    (sourceResidualJoin_le_ordinary c i hi) (sourceResidualJoin_le_C c i)
  let u : sourceResidualJoin c i := ⟨sourceHom c i (.r 2),
    (sourceResidualJoin_eq_range c i hi).symm ▸ ⟨.r 2,rfl⟩⟩
  have he : e u=⟨sourceResidualQuotientCenter c i hi,sourceResidualQuotientCenter_mem c i hi⟩ :=
    Subtype.ext rfl
  change sourceResidualJoinEquiv c i hi (e.symm _) = _
  rw [←he,e.symm_apply_apply]
  change (MonoidHom.ofInjective (sourceHom_injective c i hi)).symm
    ((MonoidHom.ofInjective (sourceHom_injective c i hi)) (.r 2)) = .r 2
  exact MulEquiv.symm_apply_apply _ _

/-- The literal F.5.5 input to successive transfer, with its central mark. -/
theorem source_residualJoin_transfer_data (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) (R : Sylow 2 (C c i)) (hR : Tf c i≤R) :
    ∃ e : sourceResidualJoinQuotient c i ≃* D8,
    ∃ u : sourceResidualJoinQuotient c i,
      e u=.r 2 ∧
      sourceResidualJoinQuotient c i≤(R : Subgroup (C c i)).map
        (QuotientGroup.mk' (zpowers (graphInCentralizer c i))) ∧
      sourceResidualJoinQuotient c i≤pResidual 2 (graphCentralQuotient c i) ∧
      (∀ x∈sourceResidualJoinQuotient c i, orderOf x=2 → IsConj x u.val) ∧
      ∃ v : C c i, v.val=sourceMarkedShort c i*rootElement c i z ∧
        QuotientGroup.mk' (zpowers (graphInCentralizer c i)) v=u.val := by
  let hi := h.embedding_injective
  refine ⟨sourceResidualJoinQuotientEquiv c i hi,
    ⟨sourceResidualQuotientCenter c i hi,sourceResidualQuotientCenter_mem c i hi⟩,
    sourceResidualJoinQuotientEquiv_center c i hi,
    sourceResidualJoinQuotient_le_R c i hi R hR,
    sourceResidualJoinQuotient_le_twoResidual c i,
    sourceResidualJoinQuotient_involution_conjugate c i hi,?_⟩
  exact ⟨sourceResidualCenterInC c i hi,sourceResidualCenterInC_val c i hi z h,rfl⟩

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
