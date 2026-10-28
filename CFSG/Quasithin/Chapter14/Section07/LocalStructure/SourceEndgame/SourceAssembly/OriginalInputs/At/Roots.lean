module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.SourceCompletion.Quotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Steinberg

/-!
# The original 14.7.73 roots at the fixed group

The original point normalizer and marked Sylow image feed the projective
root proof. The resulting natural quotient, products, orders and literal
six-dimensional indecomposable quotient use the same qK map.
Only the structural input at the original G,T is used. Earlier-source
construction and final discharge remain with qt-d-14775-source.
Source: Aschbacher–Smith 14.7.71–75, printed pp.1075–1078.
-/
public section
noncomputable section
open Subgroup Representation
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

include d in
private theorem left_intersection_le
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    L ⊓ F.H ≤ F.Li L 1 ⊔ (T : Subgroup G) := by
  let N := L ⊓ F.H
  let J := N ⊔ (T : Subgroup G)
  have hTN : (T : Subgroup G) ≤ normalizer (N : Set G) :=
    (le_inf (d.natural.sylow_normalizes_at structural)
      ((F.invariant 1).trans F.H.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  let : (N.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le N.le_normalizer hTN)
  obtain ⟨R, hR⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_subgroupOf_eq_of_normal (N.subgroupOf J)
  have hs := congrArg (fun B : Subgroup (N.subgroupOf J) =>
    (B.map (N.subgroupOf J).subtype).map J.subtype) (pResidual_sup_sylow_eq_top R)
  rw [Subgroup.map_sup, Subgroup.map_sup, map_embedded_pResidual,
    map_subgroupOf_eq_of_le (show N ≤ J from le_sup_left),
    ← MonoidHom.range_eq_map, range_subtype,
    map_subgroupOf_eq_of_le (show N ≤ J from le_sup_left), hR, subgroupOf_map_subtype] at hs
  apply le_trans hs.symm.le
  apply sup_le
  · have he : F.Li L 1 = (pResidual 2 N).map N.subtype := by
      simp only [InvariantFlag.Li, show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide, if_false]
      rfl
    rw [← he]
    exact le_sup_left
  · exact (map_mono inf_le_left).trans (by
      rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right)]
      exact le_sup_right)

theorem source_point_normalizer_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (sep : d.ModuleSeparation) :
    F.H ⊓ normalizer (V : Set G) = F.Li L 1 ⊔ (T : Subgroup G) := by
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ ((T : Subgroup G) : Set G) * (L : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right _ _ (d.natural.sylow_normalizes_at structural),
        sup_comm, d.lemma_14_7_67_five sep]
      exact hx.2
    obtain ⟨t,ht,l,hl,he⟩ := hx'
    have hlH : l ∈ F.H := by
      have h := F.H.mul_mem (F.H.inv_mem (F.invariant 1 ht)) hx.1
      rwa [← he, inv_mul_cancel_left] at h
    rw [← he]
    exact mul_mem (mem_sup_right ht) (left_intersection_le d structural ⟨hl,hlH⟩)
  · apply sup_le
    · exact le_inf ((F.Li_le L 1).trans inf_le_right)
        (((F.Li_le L 1).trans inf_le_left).trans d.natural.chosen.normalizes)
    · exact le_inf (F.invariant 1) (d.natural.sylow_normalizes_seed_at structural)

theorem source_geometry_earlier_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (sep : d.ModuleSeparation) (mark : UpperMarking d) : Geometry.Images.Earlier d where
  sylow_normalizes := d.natural.sylow_normalizes_at structural
  separation := sep
  point_normalizer := source_point_normalizer_at d structural sep
  sylow := source_starred_sylow d (compatibleBorel_of_upperMarking_at d structural mark)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.SourceCompletion

public section
noncomputable section
open Subgroup Representation
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

theorem roots_of_source_sections_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c) (mark : UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (hS : S L F = L.pCoreIn 2)
    (hcenter : (center (S L F)).map (S L F).subtype = V)
    (hPhi : (frattini (S L F)).map (S L F).subtype = V)
    (hp : d.U₀ = F.Vi 1)
    (s : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL))
    (recognition : Geometry.NaturalRecognition.{u}) (k : K F)
    (hk : (k : G) ∉ F.Li L 1 ⊔ (T : Subgroup G)) : Conclusion73 d k := by
  let earlier := source_geometry_earlier_at d structural e.separation mark
  have himage : Geometry.Images.TwoCoreImage (L := L) (F := F) :=
    Geometry.Images.twoCoreImage_iff.mpr (ChiefFactors.QKPlacement.star_twoCore_le_S_at d structural c e mark)
  obtain ⟨X,aX,mX,hd⟩ := CriticalIntersections.exists_sourceDuality d e.sectionCentralizer
  let := aX
  let := mX
  obtain ⟨dual⟩ := hd
  obtain ⟨b⟩ := ChiefFactors.HAccounting.exists_qKDualCoordinates d e.sectionCentralizer dual hcomm
  have hcentralizer := ChiefFactors.centralizer_commutator d c e
  obtain ⟨⟨n⟩,hE,hgen,hP₀,hproduct,helem,hcommP,hprod,_⟩ :=
    Geometry.Source.quotient_outputs d earlier k hk hS hcenter hPhi hp himage b hcentralizer s recognition
  obtain ⟨R,hR⟩ := Geometry.Images.exists_sylow_image d hS (le_sup_left.trans hgen.ge) earlier.sylow himage
  obtain ⟨g,hmark⟩ := Geometry.Images.exists_point_residual_image d
  let B : Sylow 3 (F.Li L 1) := Classical.choice inferInstance
  obtain ⟨hSP,hTK,hSyl,hindex,_,_,_,_,_,hEU,hcard⟩ :=
    ParabolicCounting.source_parabolic_outputs d k hS hPhi earlier.sylow_normalizes hgen R hR hp s n g hmark B
  exact {
    natural := ⟨n⟩
    generation := hgen
    sylow_image := ⟨R,hR⟩
    product_eq_core := hP₀
    ordered_product := hproduct
    intersection := hE
    parabolic := hSP
    sylow_intersection := hTK
    sylow_witness := hSyl
    index := hindex
    elementary := helem
    commutator_generation := hcommP
    root_product := hprod
    fixed_counts := ParabolicCounting.source_fixed_counts d hS
      ((U_le_E d k).trans (n.kernel_le.trans (pCoreIn_le 2 _))) hp s
      (ParabolicCounting.SteinbergGeneration.marked_image_card d g hmark)
    kernel_index := hEU
    card := hcard }


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.SourceCompletion

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

include d in
/-- The original K contains an element outside the source point normalizer. -/
theorem exists_root_conjugator_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    ∃ k : K F, (k : G) ∉ F.Li L 1 ⊔ (T : Subgroup G) := by
  have hTL := d.natural.sylow_normalizes_at structural
  have hH : ¬ F.H ≤ normalizer (L : Set G) := by
    have hh : F.H ∈ F.Hz L (normalizer (L : Set G)) := by
      rw [d.unique_Hz]
      exact Set.mem_singleton _
    exact hh.2.2
  by_contra hk
  push Not at hk
  have hK : K F ≤ normalizer (L : Set G) := fun x hx =>
    sup_le (((F.Li_le L 1).trans inf_le_left).trans L.le_normalizer) hTL (hk ⟨x,hx⟩)
  exact hH (d.residual_product ▸ sup_le hK hTL)

/-- Apply the original72 outputs, without assuming a section, natural root
coordinates, generation, Sylow placement or any count from73. -/
theorem finish_roots_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c) (mark : UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h72 : SourceAssembly.Conclusion72 d)
    (recognition : Geometry.NaturalRecognition.{u}) (k : K F)
    (hk : (k : G) ∉ F.Li L 1 ⊔ (T : Subgroup G)) : Conclusion73 d k := by
  obtain ⟨s⟩ := h72.steinberg
  exact roots_of_source_sections_at d structural c e mark hcomm h72.core h72.center_eq
    h72.frattini_eq h72.fixed_kernel (s.toSection (h72.core.le.trans (pCoreIn_le 2 L)))
    recognition k hk

/-- A genuine source conjugator and all its root conclusions exist. -/
theorem exists_roots_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c) (mark : UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h72 : SourceAssembly.Conclusion72 d) (recognition : Geometry.NaturalRecognition.{u}) :
    ∃ k : K F, (k : G) ∉ F.Li L 1 ⊔ (T : Subgroup G) ∧ Conclusion73 d k := by
  obtain ⟨k,hk⟩ := exists_root_conjugator_at d structural
  exact ⟨k,hk,finish_roots_at d structural c e mark hcomm h72 recognition k hk⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.SourceCompletion

@[expose] public section
noncomputable section
open Subgroup Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation

/-- All root conclusions, together with the actual six-dimensional
indecomposable quotient, constructed from the original72 record. -/
theorem finish_roots_with_quotient_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c) (mark : UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h72 : SourceAssembly.Conclusion72 d)
    (recognition : Geometry.NaturalRecognition.{u}) (k : K F)
    (hk : (k : G) ∉ F.Li L 1 ⊔ (T : Subgroup G)) :
    ∃ h : Conclusion73 d k,
      letI : (F.U.subgroupOf ((K F).pCoreIn 2)).Normal :=
        normal_subgroupOf_of_le_normalizer
          ((pCoreIn_le 2 (K F)).trans ((K_le_H F).trans d.conjugationSection.normalized))
      letI := h.elementary
      Nonempty (QuotientCoordinates d k) := by
  let h := finish_roots_at d structural c e mark hcomm h72 recognition k hk
  exact ⟨h,quotient_coordinates d k h (h72.derived_eq.le.trans (Data.V_le_U F))⟩

/-- Feed the literal RuTwo consumer after74, constructing the conjugator
and all natural-section, generation, Sylow and cardinality data here. -/
theorem ruTwo_of_source72_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c) (mark : UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h72 : SourceAssembly.Conclusion72 d) (recognition : Geometry.NaturalRecognition.{u})
    (hz : ChapterJ.sylowCenter T = F.Vi 1)
    (hcore : F.H.pCoreIn 2 = (K F).pCoreIn 2) : Nonempty (ChapterJ.RuTwo V T) := by
  obtain ⟨k,hk,h⟩ := exists_roots_at d structural c e mark hcomm h72 recognition
  exact ruTwo_of_roots d k h h72.core h72.frattini_eq
    (d.natural.sylow_normalizes_at structural) h72.fixed_kernel hz hcore

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.SourceCompletion
