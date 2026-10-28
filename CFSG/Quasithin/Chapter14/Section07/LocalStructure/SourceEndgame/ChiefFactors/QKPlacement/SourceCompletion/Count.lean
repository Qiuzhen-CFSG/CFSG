module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion.Maps
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion.Root
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Refinement

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.CriticalIntersections.Construction

/-!
# The three actual noncentral chief factors in S/V

The invariant filtration is the image of
`V ≤ U ≤ S ∩ C_H(U) ≤ S ∩ Q_K ≤ S ∩ Q_H ≤ S`.
The first, middle and last noncentral intervals have respectively the
Borel quotient, its dual annihilator, and the root group as coordinates.
The other two intervals are central by the earlier commutator identities.
Refining those central gaps yields exactly three noncentral chief factors
for the original L₁ action induced through qL. This argument does not
require S to lie in L₁, or any prior Steinberg recognition.

The final adapter constructs the dual coordinates from the earlier source
pairing and applies the result to the canonical quotient action.
Source: Aschbacher–Smith 14.7.71–72, printed pp.1075–1076.
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
theorem source_71_count
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d)
    (hp : d.U₀ = F.Vi 1) (b : QKDualCoordinates d) (a : QuotientAction d) :
    HasCount (a.representation.comp (d.qL.comp (inclusion ((F.Li_le L 1).trans inf_le_left)))) 3 := by
  let hb := compatibleBorel_of_upperMarking d structural mark
  let m := leftBorelMap d hb
  have hm : ∀l,(m l).val = d.qH (inclusion ((F.Li_le L 1).trans inf_le_right) l) := leftBorelMap_val d hb
  have hms := leftBorelMap_surjective d hb
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
    (firstCoordinates_kernel d structural c e mark hp)
    (firstCoordinates_equivariant d m hm) (firstTarget_noncentral d m hms)
  rw [image_seed_bot d a hV] at hfirst hfirstnc
  let := middleTarget_irreducible d m hms
  obtain ⟨hmid,hmidnc⟩ := imageNode_chief d a (SteinbergRecognition.S F L ⊓ QK F)
    (SteinbergRecognition.S F L ⊓ C F) hK hC inf_le_left
    (inf_le_inf_left _ le_sup_right) hVC (middleTarget d m)
    (middleCoordinates d structural c e mark b) (middleCoordinates_surjective d structural c e mark b)
    (middleCoordinates_kernel d structural c e mark b)
    (middleCoordinates_equivariant d m hm structural c e mark b)
    (middleTarget_noncentral d m hms)
  let := rootRepresentation_irreducible d hb
  obtain ⟨hlast,hlastnc⟩ := imageNode_chief d a (SteinbergRecognition.S F L)
    (SteinbergRecognition.S F L ⊓ F.H.pCoreIn 2) hS hQ le_rfl inf_le_left hVQ
    (rootRepresentation d hb) (rootCoordinate d structural c e mark)
    (rootCoordinate_surjective d structural c e mark)
    (fun x => (rootCoordinate_kernel d structural c e mark x).trans (by simp only [mem_inf, x.property, true_and]))
    (rootCoordinate_equivariant d structural c e mark hb)
    (rootRepresentation_noncentral d hb)
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
theorem source_71_count_of_source
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
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
  exact source_71_count d structural c e mark hp b a

/-- The count required by the Steinberg consumer, with the descended action
constructed on the literal S/V carrier rather than supplied independently. -/
theorem source_71_count_canonical
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d)
    (hp : d.U₀ = F.Vi 1) (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hSQ : ⁅SteinbergRecognition.S F L, Q T L⁆ ≤ V) :
    HasCount ((quotientAction d hTL hSQ).representation.comp
      (d.qL.comp (inclusion ((F.Li_le L 1).trans inf_le_left)))) 3 :=
  source_71_count_of_source d structural c e mark hp hcomm (quotientAction d hTL hSQ)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion
