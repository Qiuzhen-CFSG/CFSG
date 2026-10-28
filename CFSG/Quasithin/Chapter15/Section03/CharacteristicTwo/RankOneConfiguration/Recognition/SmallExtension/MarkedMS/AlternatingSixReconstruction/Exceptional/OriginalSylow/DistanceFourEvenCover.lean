module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.CubicAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Graph
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The retained even cover of the original exceptional actor

Write M = LR, K = L inside M and Q = O₂(M). The subgroup H = KQ
has quotient H/Q equal to the original triple cover of A₆. Restricting
the literal quotient M → M/Q to its component image constructs the
surjection onto the even hexacode group with kernel exactly Q. The cubic
permutation projection is used only to identify H as its even preimage.

The embedding into the original base stabilizer carries O²(H) onto the
stabilizer's two-residual. These pointwise maps and the image-cardinality
formula supply the actor and kernel premises of the terminal moving
quotient recognition without removing the cubic covering center.

Source: Meierfrankenfeld--Stellmacher (1993), (5.12)(2), pp.925--926;
Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "Q₀" => pCore 2 M
local notation "Rg" => edge L R

abbrev evenCoverGroup (L R : Subgroup G) : Subgroup (L ⊔ R : Subgroup G) :=
  L.subgroupOf (L ⊔ R) ⊔ pCore 2 (L ⊔ R : Subgroup G)

variable (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
local notation "H" => evenCoverGroup L R

include h in
theorem evenCoverGroup_eq_residual_sup_core : H = pResidual 2 M ⊔ Q₀ := by
  rw [h.relative_residual]

include h in
theorem evenCoverGroup_map : (H).map (embedM Rg) = Ltilde Rg (alpha Rg) ⊔ Q Rg (alpha Rg) := by
  rw [evenCoverGroup,Subgroup.map_sup,←graph_component h,
    ←Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le]

/-- The even cover embeds in the literal base stabilizer through the graph embedding. -/
@[expose] def evenCoverEmbedding : H →* stabilizer Rg (alpha Rg) :=
  ((embedM Rg).comp (H).subtype).codRestrict (stabilizer Rg (alpha Rg)) (by
    intro x
    have hx : embedM Rg x ∈ Ltilde Rg (alpha Rg) ⊔ Q Rg (alpha Rg) :=
      evenCoverGroup_map h ▸ mem_map_of_mem (embedM Rg) x.property
    exact (sup_le (Ltilde_le_stabilizer (alpha Rg)) (show Q Rg (alpha Rg) ≤ stabilizer Rg (alpha Rg) from fun _ hy => hy.1)) hx)

theorem evenCoverEmbedding_apply (x : H) :
    (evenCoverEmbedding h x : FreeAmalgam Rg) = embedM Rg x := by rfl

theorem evenCoverEmbedding_injective : Function.Injective (evenCoverEmbedding h) := by
  intro x y he
  exact Subtype.ext ((embedM_injective Rg) (congrArg Subtype.val he))

theorem evenCoverEmbedding_map :
    (⊤ : Subgroup H).map (evenCoverEmbedding h) =
      (Ltilde Rg (alpha Rg) ⊔ Q Rg (alpha Rg)).subgroupOf (stabilizer Rg (alpha Rg)) := by
  apply Subgroup.map_injective (stabilizer Rg (alpha Rg)).subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le
    (sup_le (Ltilde_le_stabilizer (alpha Rg)) (show Q Rg (alpha Rg) ≤ stabilizer Rg (alpha Rg) from fun _ hy => hy.1)), Subgroup.map_map]
  change (⊤ : Subgroup H).map ((embedM Rg).comp (H).subtype) = _
  rw [←Subgroup.map_map, ←MonoidHom.range_eq_map, range_subtype, evenCoverGroup_map h]


include h in
theorem evenCoverGroup_residual : pResidual 2 H = (K).subgroupOf H := by
  let := h.relative_normal
  have hp : IsPPerfect 2 ((K).subgroupOf H) :=
    h.relative_twoPerfect.of_surjective (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)).symm.surjective
  exact pResidual_eq_of_isPPerfect_sup ((K).subgroupOf H) ((Q₀).subgroupOf H) hp
    pCore_isPGroup.comap_subtype (by
      rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self])

include h in
theorem evenCoverGroup_residual_map : (pResidual 2 H).map (H).subtype = K := by
  rw [evenCoverGroup_residual h,map_subgroupOf_eq_of_le le_sup_left]

include h in
theorem evenCoverGroup_twoCore : pCore 2 H = (Q₀).subgroupOf H := by
  let := h.relative_normal
  exact pCore_subnormal_eq_comap 2 (inferInstance : (H).Normal).isSubnormal

theorem evenCoverEmbedding_residual_map :
    (pResidual 2 H).map (evenCoverEmbedding h) = pResidual 2 (stabilizer Rg (alpha Rg)) := by
  apply Subgroup.map_injective (stabilizer Rg (alpha Rg)).subtype_injective
  rw [Subgroup.map_map]
  change (pResidual 2 H).map ((embedM Rg).comp (H).subtype) = Ltilde Rg (alpha Rg)
  rw [←Subgroup.map_map, evenCoverGroup_residual_map h, ←graph_component h]


omit [Finite G] in
theorem evenCoverGroup_image : (H).map (QuotientGroup.mk' Q₀) = componentImage L R := by
  rw [evenCoverGroup,Subgroup.map_sup,QuotientGroup.map_mk'_self,sup_bot_eq]

def evenCoverToComponent : H →* componentImage L R :=
  ((QuotientGroup.mk' Q₀).comp (H).subtype).codRestrict (componentImage L R) (by
    intro x
    rw [←evenCoverGroup_image]
    exact mem_map_of_mem (QuotientGroup.mk' Q₀) x.property)

omit [Finite G] in
theorem evenCoverToComponent_apply (x : H) :
    (evenCoverToComponent (L := L) (R := R) x : M ⧸ Q₀) = QuotientGroup.mk' Q₀ x := by rfl

omit [Finite G] in
theorem evenCoverToComponent_surjective : Function.Surjective (evenCoverToComponent (L := L) (R := R)) := by
  intro y
  obtain ⟨k,hk,hky⟩ := y.property
  exact ⟨⟨k,mem_sup_left hk⟩,Subtype.ext hky⟩

omit [Finite G] in
theorem evenCoverToComponent_kernel : (evenCoverToComponent (L := L) (R := R)).ker = (Q₀).subgroupOf H := by
  ext x
  change evenCoverToComponent x = 1 ↔ (x : M) ∈ Q₀
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff (x : M)

def evenCoverMarking : componentImage L R ≃* Atlas.Codes.HexEvenAutomorphisms :=
  let a := Classical.choose (exists_quotient_hexacode_equiv h e hz)
  let f := subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)
  (cComponentTwoCoreQuotientEquiv h.component).symm.trans
    ((QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans a)

@[expose] def evenCoverProjection : H →* Atlas.Codes.HexEvenAutomorphisms :=
  (evenCoverMarking h e hz).toMonoidHom.comp evenCoverToComponent

theorem evenCoverProjection_surjective : Function.Surjective (evenCoverProjection h e hz) :=
  (evenCoverMarking h e hz).surjective.comp evenCoverToComponent_surjective

theorem evenCoverProjection_kernel : (evenCoverProjection h e hz).ker = (Q₀).subgroupOf H := by
  rw [evenCoverProjection,MonoidHom.ker_comp_of_injective _ _ (evenCoverMarking h e hz).injective,
    evenCoverToComponent_kernel]

theorem evenCoverProjection_kernel_isPGroup : IsPGroup 2 (evenCoverProjection h e hz).ker := by
  rw [evenCoverProjection_kernel]
  exact pCore_isPGroup.comap_subtype

/-- Image order under the retained cover is the original index modulo Q. -/
theorem evenCoverProjection_image_card (A : Subgroup M) (hA : A ≤ H) :
    Nat.card ((A.subgroupOf H).map (evenCoverProjection h e hz)) = (Q₀).relIndex A := by
  rw [←relIndex_ker, evenCoverProjection_kernel,
    ←relIndex_map_map_of_injective _ _ (H).subtype_injective,
    map_subgroupOf_eq_of_le le_sup_right, map_subgroupOf_eq_of_le hA]

/-- On a graph subgroup the same image order is its index modulo the original neighborhood kernel. -/
theorem evenCoverProjection_graph_image_card (A : Subgroup (FreeAmalgam Rg))
    (hAG : A ≤ stabilizer Rg (alpha Rg)) (hAH : A.comap (embedM Rg) ≤ H) :
    Nat.card (((A.comap (embedM Rg)).subgroupOf H).map (evenCoverProjection h e hz)) =
      (Q Rg (alpha Rg)).relIndex A := by
  rw [evenCoverProjection_image_card h e hz _ hAH,
    ←relIndex_map_map_of_injective _ _ (embedM_injective Rg),
    ←Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le,
    map_comap_eq_self (hAG.trans_eq (stabilizer_m_base Rg))]

def evenCoverQuotientEquiv : (H ⧸ (Q₀).subgroupOf H) ≃* Atlas.Codes.HexEvenAutomorphisms :=
  (QuotientGroup.quotientMulEquivOfEq (evenCoverProjection_kernel h e hz).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (evenCoverProjection h e hz)
      (evenCoverProjection_surjective h e hz))

theorem evenCoverQuotientEquiv_apply (x : H) :
    evenCoverQuotientEquiv h e hz (QuotientGroup.mk' ((Q₀).subgroupOf H) x) =
      evenCoverProjection h e hz x := by rfl

theorem evenCoverProjection_component (k : K) :
    evenCoverProjection h e hz (inclusion (show K ≤ H from le_sup_left) k) =
      evenCoverMarking h e hz ((QuotientGroup.mk' Q₀).subgroupMap K k) := by rfl

theorem evenCoverProjection_residual_image :
    (pResidual 2 H).map (evenCoverProjection h e hz) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨c,rfl⟩ := (evenCoverMarking h e hz).surjective x
  obtain ⟨k,rfl⟩ := (QuotientGroup.mk' Q₀).subgroupMap_surjective K c
  refine ⟨inclusion (show K ≤ H from le_sup_left) k,?_,rfl⟩
  rw [evenCoverGroup_residual h]
  exact k.property

theorem evenCoverGroup_eq_even_preimage
    (hk : layerKernel L R = extensionKernel h) :
    H = (alternatingGroup (Fin 6)).comap (CubicAction.projection h e hz hk) := by
  rw [←CubicAction.component_image h e hz hk,comap_map_eq,CubicAction.projection_kernel]
  exact le_antisymm (sup_le le_sup_left (le_sup_right.trans le_sup_right))
    (sup_le le_sup_left (sup_le ((map_subtype_le _).trans le_sup_left) le_sup_right))

theorem le_evenCoverGroup_of_even_image
    (hk : layerKernel L R = extensionKernel h) (A : Subgroup M)
    (hA : A.map (CubicAction.projection h e hz hk) ≤ alternatingGroup (Fin 6)) : A ≤ H := by
  rw [evenCoverGroup_eq_even_preimage h e hz hk]
  exact map_le_iff_le_comap.mp hA

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
