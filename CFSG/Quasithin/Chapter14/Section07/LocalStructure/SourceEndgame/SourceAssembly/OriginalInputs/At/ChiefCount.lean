module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion.Count
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion.Commutator
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.ChiefCoordinates

/-!
# The 14.7.71 count and commutator at the fixed group

Refine the five actual intervals on S/V. Three are noncentral and the
remaining two central. The reverse product and residual perfection
then give the commutator containment [Q,L] ≤ S.
Only the structural input at the original G,T is used. Earlier-source
construction and final discharge remain with qt-d-14775-source.
Source: Aschbacher–Smith 14.7.71–75, printed pp.1075–1078.
-/
@[expose] public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
open SteinbergRecognition.ModuleRecognition BinaryLinearThree.ParabolicCyclic.ChiefCounts
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
  [(V.subgroupOf (SteinbergRecognition.S F L)).Normal]
  [IsElementaryAbelian 2 (SteinbergRecognition.S F L ⧸ V.subgroupOf (SteinbergRecognition.S F L))]

private theorem image_seed_bot (a : QuotientAction d)
    (hV : F.Li L 1 ≤ normalizer (V:Set G)) : imageNode d a V hV = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  ext v
  constructor
  · intro hv
    obtain ⟨s,hs,rfl⟩ := (mem_subgroupImage V v).mp hv
    exact (QuotientGroup.eq_one_iff s).mpr hs
  · intro hv
    change v = 0 at hv
    rw [hv]
    exact Submodule.zero_mem _

private theorem image_span_top (a : QuotientAction d)
    (hS : F.Li L 1 ≤ normalizer (SteinbergRecognition.S F L:Set G)) :
    imageNode d a (SteinbergRecognition.S F L) hS = ⊤ := by
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  intro v _
  obtain ⟨s,hs⟩ := quotientCoordinates_surjective (Multiplicative.ofAdd v)
  exact (mem_subgroupImage _ v).mpr ⟨s,s.property,congrArg Multiplicative.toAdd hs⟩

omit d [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  [(V.subgroupOf (SteinbergRecognition.S F L)).Normal]
  [IsElementaryAbelian 2 (SteinbergRecognition.S F L ⧸ V.subgroupOf (SteinbergRecognition.S F L))] in
private theorem left_normalizes_core : F.Li L 1 ≤ normalizer (F.H.pCoreIn 2:Set G) := by
  have hn : F.H ≤ normalizer (F.H.pCoreIn 2:Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore 2 F.H).le_normalizer_map F.H.subtype
  exact ((F.Li_le L 1).trans inf_le_right).trans hn

include d in
omit [(V.subgroupOf (SteinbergRecognition.S F L)).Normal]
  [IsElementaryAbelian 2 (SteinbergRecognition.S F L ⧸ V.subgroupOf (SteinbergRecognition.S F L))] in
private theorem left_normalizes_c : F.Li L 1 ≤ normalizer (C F:Set G) := by
  exact ((F.Li_le L 1).trans inf_le_right).trans
    ((normal_subgroupOf_iff_le_normalizer (inf_le_left : C F ≤ F.H)).mp (C_normal d))

omit [Finite G]
  [(V.subgroupOf (SteinbergRecognition.S F L)).Normal]
  [IsElementaryAbelian 2 (SteinbergRecognition.S F L ⧸ V.subgroupOf (SteinbergRecognition.S F L))] in
private theorem left_normalizes_inf (A B : Subgroup G)
    (hA : F.Li L 1 ≤ normalizer (A:Set G)) (hB : F.Li L 1 ≤ normalizer (B:Set G)) :
    F.Li L 1 ≤ normalizer ((A⊓B):Set G) :=
  (le_inf hA hB).trans inf_normalizer_le_normalizer_inf

/-- The source chief count on the literal quotient and original L₁ map. -/
theorem source_71_count_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d)
    (hp : d.U₀ = F.Vi 1) (b : QKDualCoordinates d) (a : QuotientAction d) :
    HasCount (a.representation.comp (d.qL.comp (inclusion ((F.Li_le L 1).trans inf_le_left)))) 3 := by
  let hb := compatibleBorel_of_upperMarking_at d structural mark
  let m := leftBorelMap_at d hb
  have hm : ∀l,(m l).val = d.qH (inclusion ((F.Li_le L 1).trans inf_le_right) l) := leftBorelMap_val_at d hb
  have hms := leftBorelMap_surjective_at d hb
  have hS : F.Li L 1 ≤ normalizer (SteinbergRecognition.S F L:Set G) :=
    ((F.Li_le L 1).trans inf_le_left).trans (le_normalizer_conjugateSpanBy _ _)
  have hV : F.Li L 1 ≤ normalizer (V:Set G) :=
    ((F.Li_le L 1).trans inf_le_left).trans d.natural.chosen.normalizes
  have hU : F.Li L 1 ≤ normalizer (F.U:Set G) :=
    ((F.Li_le L 1).trans inf_le_right).trans d.conjugationSection.normalized
  have hC := left_normalizes_inf (SteinbergRecognition.S F L) (C F) hS (left_normalizes_c d)
  have hK := left_normalizes_inf (SteinbergRecognition.S F L) (QK F) hS
    (((F.Li_le L 1).trans inf_le_right).trans b.qSection.normalized)
  have hQ := left_normalizes_inf (SteinbergRecognition.S F L) (F.H.pCoreIn 2) hS left_normalizes_core
  let P₁ := imageNode d a F.U hU
  let P₂ := imageNode d a (SteinbergRecognition.S F L ⊓ C F) hC
  let P₃ := imageNode d a (SteinbergRecognition.S F L ⊓ QK F) hK
  let P₄ := imageNode d a (SteinbergRecognition.S F L ⊓ F.H.pCoreIn 2) hQ
  have hUS : F.U ≤ SteinbergRecognition.S F L := U_le_S
  have hVC : V ≤ SteinbergRecognition.S F L ⊓ C F :=
    le_inf ((Data.V_le_U F).trans hUS) ((Data.V_le_U F).trans (U_le_C d))
  have hCQ : C F ≤ F.H.pCoreIn 2 := C_le_QH d e.sectionCentralizer
  have hVQ : V ≤ SteinbergRecognition.S F L ⊓ F.H.pCoreIn 2 :=
    le_inf (hVC.trans inf_le_left) ((hVC.trans inf_le_right).trans hCQ)
  let := firstTarget_irreducible d m hms
  obtain ⟨hfirst,hfirstnc⟩ := imageNode_chief d a F.U V hU hV hUS (Data.V_le_U F) le_rfl
    (firstTarget d m) (firstCoordinates d) (firstCoordinates_surjective d)
    (firstCoordinates_kernel_at d structural c e mark hp)
    (firstCoordinates_equivariant d m hm) (firstTarget_noncentral d m hms)
  rw [image_seed_bot d a hV] at hfirst hfirstnc
  let := middleTarget_irreducible d m hms
  obtain ⟨hmid,hmidnc⟩ := imageNode_chief d a (SteinbergRecognition.S F L ⊓ QK F)
    (SteinbergRecognition.S F L ⊓ C F) hK hC inf_le_left
    (inf_le_inf_left _ le_sup_right) hVC (middleTarget d m)
    (middleCoordinates_at d structural c e mark b) (middleCoordinates_surjective_at d structural c e mark b)
    (middleCoordinates_kernel_at d structural c e mark b)
    (middleCoordinates_equivariant_at d m hm structural c e mark b)
    (middleTarget_noncentral d m hms)
  let := rootRepresentation_irreducible_at d hb
  obtain ⟨hlast,hlastnc⟩ := imageNode_chief d a (SteinbergRecognition.S F L)
    (SteinbergRecognition.S F L ⊓ F.H.pCoreIn 2) hS hQ le_rfl inf_le_left hVQ
    (rootRepresentation_at d hb) (rootCoordinate_at d structural c e mark)
    (rootCoordinate_surjective_at d structural c e mark)
    (fun x => (rootCoordinate_kernel_at d structural c e mark x).trans (by simp only [mem_inf, x.property, true_and]))
    (rootCoordinate_equivariant_at d structural c e mark hb)
    (rootRepresentation_noncentral_at d hb)
  rw [image_span_top d a hS] at hlast hlastnc
  apply hasCount_three_of_five_intervals P₁ P₂ P₃ P₄ hfirst
    (imageNode_mono d a (le_inf hUS (U_le_C d))) hmid
    (imageNode_mono d a (inf_le_inf_left _ (QK_le_QH d e.sectionCentralizer))) hlast
    hfirstnc ?_ hmidnc ?_ hlastnc
  · apply imageNode_central
    exact (commutator_mono L₁_le_K inf_le_right).trans (centralizer_commutator d c e)
  · apply imageNode_central
    apply le_inf
    · rw [commutator_comm]
      exact (commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hS)
    · apply (commutator_mono L₁_le_K inf_le_right).trans
      rw [commutator_comm]
      exact le_sup_left

/-- Construct the needed dual coordinates from the original section kernel.
Only the earlier source commutator identity remains explicit. -/
theorem source_71_count_of_source_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d)
    (hp : d.U₀ = F.Vi 1) (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (a : QuotientAction d) :
    HasCount (a.representation.comp
      (d.qL.comp (inclusion ((F.Li_le L 1).trans inf_le_left)))) 3 := by
  obtain ⟨X, aX, mX, hs⟩ := CriticalIntersections.exists_sourceDuality d e.sectionCentralizer
  let := aX
  let := mX
  obtain ⟨s⟩ := hs
  obtain ⟨b⟩ := HAccounting.exists_qKDualCoordinates d e.sectionCentralizer s hcomm
  exact source_71_count_at d structural c e mark hp b a

/-- The count required by the Steinberg consumer, with the descended action
constructed on the literal S/V carrier rather than supplied independently. -/
theorem source_71_count_canonical_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d)
    (hp : d.U₀ = F.Vi 1) (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hSQ : ⁅SteinbergRecognition.S F L, Q T L⁆ ≤ V) :
    HasCount ((quotientAction d hTL hSQ).representation.comp
      (d.qL.comp (inclusion ((F.Li_le L 1).trans inf_le_left)))) 3 :=
  source_71_count_of_source_at d structural c e mark hp hcomm (quotientAction d hTL hSQ)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion

public section
noncomputable section
open Subgroup Representation
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source SteinbergRecognition
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
  (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
  (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d)
include d structural c e mark

private theorem Q_le_span_sup_core : Q T L ≤ S F L ⊔ F.H.pCoreIn 2 := by
  have hQ : ((Q T L).subgroupOf F.H).map d.qH =
      ((S F L).subgroupOf F.H).map d.qH := by
    have hr : ((S F L).subgroupOf F.H).map d.qH =
        Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements.root d.naturalQuotient :=
      root_image_at d structural c e mark
    rw [hr]
    have hm (A : Subgroup G) : (star F A).map d.model.toMonoidHom =
        (A.subgroupOf F.H).map d.qH := by
      rw [CriticalFusion.Source.star, map_map]
      rfl
    rw [← hm, e.images.image_eq, hm]
    exact mark
  intro q hq
  let qH : F.H := ⟨q, Q_le_H F hq⟩
  have hm : d.qH qH ∈ ((S F L).subgroupOf F.H).map d.qH :=
    hQ ▸ mem_map_of_mem d.qH hq
  obtain ⟨s, hs, he⟩ := hm
  have hk : (s⁻¹ * qH : F.H) ∈ d.qH.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  rw [d.qH_ker] at hk
  have hp := (S F L ⊔ F.H.pCoreIn 2).mul_mem (mem_sup_left hs)
    (mem_sup_right hk)
  change (s : G) * ((s : G)⁻¹ * q) ∈ S F L ⊔ F.H.pCoreIn 2 at hp
  simpa only [mul_inv_cancel_left] using hp

/-- The source product and actual root image force the full original Q-L bound. -/
theorem commutator_Q_L_le_S_at (b : QKDualCoordinates d) : ⁅Q T L,L⁆ ≤ S F L := by
  have hSQ := S_le_Q_at d structural e.separation
  have hQT : Q T L ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hQHT : F.H.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
      (map_subgroupOf_eq_of_le (F.invariant 1))
  have hTN : (T : Subgroup G) ≤ normalizer (S F L : Set G) :=
    T_normalizes_S d (d.natural.sylow_normalizes_at structural)
  have hTSQK : (T : Subgroup G) ≤ normalizer ((S F L ⊔ QK F : Subgroup G) : Set G) :=
    (le_inf hTN ((F.invariant 1).trans b.qSection.normalized)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hL₁N : F.Li L 1 ≤ normalizer (S F L : Set G) :=
    ((F.Li_le L 1).trans inf_le_left).trans L_normalizes_S
  have hfirst : ⁅Q T L,F.Li L 1⁆ ≤ S F L ⊔ QK F := by
    let P := commutatorPreimage (T : Subgroup G) (F.Li L 1) (S F L ⊔ QK F)
    have hsP : S F L ≤ P := le_commutatorPreimage (hSQ.trans hQT)
      ((le_normalizer_iff_commutator_le_left.mp hL₁N).trans le_sup_left)
    have hqP : F.H.pCoreIn 2 ≤ P := le_commutatorPreimage hQHT
      ((commutator_mono le_rfl L₁_le_K).trans (le_sup_left.trans le_sup_right))
    have hQP : Q T L ≤ P := (Q_le_span_sup_core d structural c e mark).trans (sup_le hsP hqP)
    exact (commutator_mono hQP le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hTSQK)
  have hLQ : L ≤ normalizer (Q T L : Set G) :=
    le_sup_left.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hinQ : ⁅Q T L,F.Li L 1⁆ ≤ Q T L :=
    le_normalizer_iff_commutator_le_left.mp (((F.Li_le L 1).trans inf_le_left).trans hLQ)
  have hfirstC : ⁅Q T L,F.Li L 1⁆ ≤ S F L ⊔ C F := by
    intro x hx
    have hm : x ∈ ((S F L : Set G) * (QK F : Set G)) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _
        (((QK_le_QH d e.sectionCentralizer).trans hQHT).trans hTN)]
      exact hfirst hx
    obtain ⟨s, hs, q, hq, he⟩ := hm
    have hqQ : q ∈ Q T L := by
      have hh := (Q T L).mul_mem ((Q T L).inv_mem (hSQ hs)) (hinQ hx)
      rw [← he, inv_mul_cancel_left] at hh
      exact hh
    have hp : q ∈ (S F L ⊓ QK F) ⊔ C F :=
      (reverse_product_at d structural c e mark b) ▸ (show q ∈ QK F ⊓ Q T L from ⟨hq,hqQ⟩)
    exact he ▸ mul_mem (mem_sup_left hs)
      ((show (S F L ⊓ QK F) ⊔ C F ≤ S F L ⊔ C F from sup_le_sup inf_le_left le_rfl) hp)
  have hsecond : ⁅S F L ⊔ C F,F.Li L 1⁆ ≤ S F L := by
    let P := commutatorPreimage (T : Subgroup G) (F.Li L 1) (S F L)
    have hsP : S F L ≤ P := le_commutatorPreimage (hSQ.trans hQT)
      (le_normalizer_iff_commutator_le_left.mp hL₁N)
    have hcP : C F ≤ P := le_commutatorPreimage ((C_le_QH d e.sectionCentralizer).trans hQHT)
      (by rw [commutator_comm]; exact ((commutator_mono L₁_le_K le_rfl).trans
        (centralizer_commutator d c e)).trans U_le_S)
    exact (commutator_mono (sup_le hsP hcP) le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hTN)
  have hperfect : IsPPerfect 2 (F.Li L 1) := by
    change IsPPerfect 2 ((pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)).map (L ⊓ F.Gi 1).subtype)
    exact isPPerfect_embedded_pResidual 2 (L ⊓ F.Gi 1)
  have hidem := commutator_isPPerfect_idempotent (F.Li L 1) (Q T L) hperfect
    (isPGroup_pCoreIn 2 _) (((F.Li_le L 1).trans inf_le_left).trans hLQ)
  have hpoint : ⁅Q T L,F.Li L 1⁆ ≤ S F L :=
    hidem.symm.le.trans ((commutator_mono hfirstC le_rfl).trans hsecond)
  let P := commutatorPreimage L (Q T L) (S F L)
  have hLP : L ≤ normalizer (P : Set G) :=
    commutatorPreimage_normalized _ _ _ _ L_normalizes_S L.le_normalizer hLQ L_normalizes_S
  have h₁P : F.Li L 1 ≤ P := le_commutatorPreimage ((F.Li_le L 1).trans inf_le_left)
    (by rwa [commutator_comm])
  have hle : L ≤ P := (SourceGeneration.point_residual_normal_span d).symm.le.trans
    (conjugateSpanBy_le h₁P hLP)
  rw [commutator_comm]
  exact (commutator_mono hle le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ L_normalizes_S)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion
