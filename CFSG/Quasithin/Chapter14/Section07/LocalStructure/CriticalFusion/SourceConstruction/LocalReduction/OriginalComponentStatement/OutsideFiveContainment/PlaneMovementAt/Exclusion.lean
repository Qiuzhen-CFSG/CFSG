module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.PlaneMovementAt.Contained
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.BinaryThreeContainment.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.EarlierModules

/-!
# Contrary plane centrality leaves only outside alternating-five components

A component containing the original point residual supplies a genuine chosen
module with a nonzero fixed point. The original fixed-module clause forces
an alternating-six faithful quotient, contradicting the earlier faithful
component orders. Under contrary centrality every component is alternating
five or linear three over two; the latter already contains the point residual.
Source: Aschbacher–Smith 13.3.2(3), 13.3.14(g), 14.3.4 and 14.7.4.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.PlaneMovementAt
open Chapter12.Section08 CriticalFusion.Source
open Chapter12.Section02 Chapter13.Section03.SourceCompletion
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- No full-point component can contain the point residual if the original
point core centralizes the plane and the original fixed-module theorem holds. -/
theorem contained_component_impossible_of_plane_centralized_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (fixed : OriginalFixedModule1332At T L)
    (C : Subgroup F.H) (hC : C.IsCComponent)
    (hin : F.Li L 1 ≤ C.map F.H.subtype)
    (hc : ⁅F.Vi 2,F.H.pCoreIn 2⁆ = ⊥) : False := by
  obtain ⟨hf,hfixed,⟨D⟩⟩ := contained_component_chosen_of_plane_centralized_at
    d h hab structural previous faithful earlier C hC hin hc
  let B := C.map F.H.subtype
  let W := ⁅(reducedTwoSubgroup (B ⊔ (T : Subgroup G) : Subgroup G)).map
    (B ⊔ (T : Subgroup G) : Subgroup G).subtype,B⁆
  let := D.actionCentralizer_normal
  obtain ⟨e⟩ := fixed (Chapter14.Section03.FaithfulSource.hypothesis1331 d)
    B hf W D hfixed
  have hcard : Nat.card (B ⧸ (centralizer (W : Set G)).subgroupOf B) = 360 := by
    rw [Nat.card_congr e.groupEquiv.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    norm_num
  have hle := Nat.card_le_card_of_surjective D.coreToFaithful D.coreToFaithful_surjective
  change Nat.card (B ⧸ (centralizer (W : Set G)).subgroupOf B) ≤
    Nat.card (B ⧸ pCore 2 B) at hle
  rw [hcard] at hle
  obtain ⟨hBL,hBf⟩ :=
    (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T B).mp hf
  rcases (faithful B hBL hBf).1 with ha | ha
  · obtain ⟨a⟩ := ha
    have hh := Nat.card_congr a.toEquiv
    rw [nat_card_alternatingGroup,Nat.card_fin] at hh
    norm_num at hh
    omega
  · obtain ⟨a⟩ := ha
    have hh := (Nat.card_congr a.toEquiv).trans Matrix.PSL3Two.card_PSL
    omega

/-- Every actual full-point component in the contrary-centrality branch
has alternating-five core quotient and lies outside the original point residual. -/
theorem all_components_outside_five_of_plane_centralized_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (fixed : OriginalFixedModule1332At T L)
    (hc : ⁅F.Vi 2,F.H.pCoreIn 2⁆ = ⊥) :
    ∀ C : Subgroup F.H, C.IsCComponent →
      Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) ∧
        ¬ F.Li L 1 ≤ C.map F.H.subtype := by
  intro C hC
  have hout : ¬ F.Li L 1 ≤ C.map F.H.subtype := fun hin =>
    contained_component_impossible_of_plane_centralized_at d h hab structural previous
      faithful earlier fixed C hC hin hc
  refine ⟨?_,hout⟩
  rcases component_small_of_plane_centralized_at h structural previous faithful hc C hC
    with hA | he
  · exact hA
  · obtain ⟨e⟩ := he
    exact (hout (local_binaryThree_component_contains_point_at d h hab structural previous
      faithful earlier F.H (h.point_mem_Hz_at F previous) C hC e)).elim

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.PlaneMovementAt
