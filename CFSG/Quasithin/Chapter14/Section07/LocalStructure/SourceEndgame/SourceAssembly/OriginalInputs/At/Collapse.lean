module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.SourceCompletion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Roots

/-!
# The original 14.7.74 collapse at the fixed group

Gaschütz lifting and the marked Borel cocycle calculation centralize
the fixed subgroup. Natural-extension displacement then gives M=L and
the equality of the two original cores.
Only the structural input at the original G,T is used. Earlier-source
construction and final discharge remain with qt-d-14775-source.
Source: Aschbacher–Smith 14.7.71–75, printed pp.1075–1078.
-/
public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source ChiefFactors
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
  (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
  (a : Prior d) (c : CriticalPath (L := L) F) (e : Earlier d c)
  (mark : UpperMarking d)
  {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

include d structural a c e mark

/-- Gaschütz on the original finite Q_H/C_H(U) section. -/
theorem QC_K_le_C_at (s : CriticalIntersections.SourceDuality F X Y)
    (b : QKDualCoordinates d) : ⁅QC T L V,K F⁆ ≤ C F := by
  let := ProjectiveFixedDetection.section_finite s
  apply ProjectiveFixedDetection.QC_K_le_C_of_fixed_lift d a c e s b
    (compatibleBorel_of_upperMarking_at d structural mark).left_image
  intro N hN P y hy
  exact SL2FourNaturalBorelFixedLifting.exists_fixed_lift
    (FixedDetection.sectionAction s) N hN P y hy

/-- The actual source commutator bound, with both coordinate sections constructed. -/
theorem QC_K_le_U_at (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1) :
    ⁅QC T L V,K F⁆ ≤ F.U := by
  obtain ⟨X,aX,mX,hs⟩ := CriticalIntersections.exists_sourceDuality d e.sectionCentralizer
  let := aX
  let := mX
  obtain ⟨s⟩ := hs
  obtain ⟨b⟩ := HAccounting.exists_qKDualCoordinates d e.sectionCentralizer s hcomm
  exact QC_K_le_U_of_centralizer_bound d c e (QC_K_le_C_at d structural a c e mark s b)

/-- The bound is consumed on the original span S=⟨U^L⟩. -/
theorem QC_centralizes_S_at (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1) :
    QC T L V ≤ centralizer (S L F : Set G) :=
  LocalCollapse.QC_centralizes_S d a (QC_K_le_U_at d structural a c e mark hcomm)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.SourceCompletion

public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
  (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
  (a : Prior d) (mark : UpperMarking d)

private theorem natural_actor_eq : d.KSL2FourMap = RootRecognition.qK d := by
  apply MonoidHom.ext
  intro k
  apply d.naturalQuotient.marking.injective
  apply Subtype.val_injective
  exact (d.KSL2FourMap_apply k).trans (RootRecognition.qK_marking d k)

omit [Finite G] in
private theorem QL_le_QC : QL T L ≤ QC T L V := by
  apply le_commutatorPreimage inf_le_left
  exact (commutator_eq_bot_iff_le_centralizer.mpr
    (show QL T L ≤ centralizer (L : Set G) from inf_le_right)).le.trans bot_le

include d structural a mark in
/-- The actual displacement of Q_L lies in the original point kernel. -/
theorem QL_K_le_point_at (hKC : ⁅QC T L V,K F⁆ ≤ F.U) :
    ⁅QL T L,K F⁆ ≤ F.Vi 1 := by
  let s := d.KNaturalSection d.U_eq_commutator_K
  have hdisp : ⁅K F,QL T L⁆ ≤ F.U := by
    rw [commutator_comm]
    exact (commutator_mono (QL_le_QC (T := T) (L := L) (V := V)) le_rfl).trans hKC
  let B := ProjectiveFixedDetection.parabolic (L := L) (F := F)
  obtain ⟨P,hP⟩ := ProjectiveFixedDetection.parabolic_contains_sylow d a
  have hm : B.map d.KSL2FourMap = Matrix.SpecialLinearGroup.rankOneBorel SL2FourNatural.F := by
    rw [natural_actor_eq d]
    exact ProjectiveFixedDetection.parabolic_marking d
      (compatibleBorel_of_upperMarking_at d structural mark).left_image
  rw [commutator_comm]
  apply commutator_le.mpr
  intro k hk x hx
  let f := s.commutatorCocycle d.KSL2FourMap (QL T L) hdisp ⟨x,hx⟩
  have hf : ∀ b ∈ B, f.val b = 0 := by
    intro b hb
    have hbx : ⁅(b : G),x⁆ = 1 := by
      apply commutatorElement_eq_one_iff_mul_comm.mpr
      exact mem_centralizer_iff.mp hx.2 b ((F.Li_le L 1 hb).1)
    have he : (⟨⁅(b : G),x⁆,hdisp (commutator_mem_commutator b.property hx)⟩ : F.U) = 1 :=
      Subtype.ext hbx
    change (s.coordinates _).toAdd = 0
    rw [he, map_one]
    rfl
  have hz := SL2FourNaturalBorelFixedLifting.cocycle_eq_zero_of_borel
    d.KSL2FourMap d.KSL2FourMap_surjective B P hP hm f hf
  have he : f.val ⟨k,hk⟩ = 0 := congrArg (fun z => z.val ⟨k,hk⟩) hz
  have hu : ⁅k,x⁆ ∈ d.U₀ := (s.coordinates_eq_one_iff _).mp
    (Multiplicative.toAdd.injective he)
  rwa [a.point_kernel] at hu

include d structural a mark in
/-- Perfection removes the remaining central point displacement. -/
theorem K_centralizes_QL_at (hKC : ⁅QC T L V,K F⁆ ≤ F.U) :
    K F ≤ centralizer (QL T L : Set G) := by
  let M := (QL T L).subgroupOf F.H
  let A := (K F).subgroupOf F.H
  let Z := (F.Vi 1).subgroupOf F.H
  let : Group.IsPerfect A := d.component.perfect
  have hMZ : ⁅M,A⁆ ≤ Z := by
    apply commutator_le.mpr
    intro x hx y hy
    exact QL_K_le_point_at d structural a mark hKC (commutator_mem_commutator hx hy)
  have hZA : ⁅Z,A⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro z hz k hk
    apply Subtype.ext
    exact (d.H_centralizes_point (K_le_H F hk) z hz).symm
  have hzero : ⁅⁅M,A⁆,A⁆ = ⊥ :=
    eq_bot_iff.mpr ((commutator_mono hMZ le_rfl).trans hZA.le)
  have hfirst := commutator_eq_bot_of_iterated_eq_bot M A hzero
  have hm := congrArg (Subgroup.map F.H.subtype) hfirst
  dsimp only [M,A] at hm
  rw [map_commutator, map_subgroupOf_eq_of_le (show QL T L ≤ F.H from
    inf_le_left.trans (Q_le_H F)), map_subgroupOf_eq_of_le (K_le_H F),Subgroup.map_bot] at hm
  rw [commutator_comm] at hm
  exact commutator_eq_bot_iff_le_centralizer.mp hm

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.SourceCompletion

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- The74 conclusion from genuine preceding source inputs, with every module
step discharged and all groups and quotient maps unchanged. -/
theorem source_lemma_14_7_74_at (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (a : Prior d) (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c)
    (mark : UpperMarking d) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1) :
    Conclusion74 d := by
  have hKC := QC_K_le_U_at d structural a c e mark hcomm
  have hKQL := K_centralizes_QL_at d structural a mark hKC
  obtain ⟨hm,hs,hh,hp,hz,hc,hS,hQ⟩ := source_conclusions_of_module_steps d a
    (Q_eq_QC_sup_S d a) hKC hKQL
    (fun hQL hlt => NaturalRigidity.Displacement.QC_parabolic_displacement d a hKC hQL hlt)
  exact ⟨hm,hs,hh,hp,hz,hc,hS,hQ⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.SourceCompletion
