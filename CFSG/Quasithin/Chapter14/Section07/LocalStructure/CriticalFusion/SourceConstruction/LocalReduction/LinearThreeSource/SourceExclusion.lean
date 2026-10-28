module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LinearThreeSource.ThompsonEntry
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.EarlierModules

/-!
# Original plane movement from the earlier fixed-module source

Contrary plane centrality constructs an actual chosen module for the full
point component, with a nonzero fixed part. The original 13.3.2(3) source
identifies its faithful actor as A₆. The literal surjection from the
component's two-core quotient would then require a quotient of order 360
of A₅ or SL₃(2), which is impossible.

The earlier fixed-module implication remains an explicit source input.
This theorem does not assert that the narrower faithful quotient list
alone supplies plane movement, and it uses no downstream Data record.
Source: Aschbacher--Smith 13.3.2(3), 13.3.14(g), and 14.3.4(1), printed
pp.885,893,990.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LinearThreeSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter12.Section02 Chapter13.Section03.SourceCompletion
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The richer original source prefix forces movement of the original plane
by the complete original point core. -/
theorem original_plane_moved_of_fixed_module_source_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (fixed : OriginalFixedModule1332At T L) :
    ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥ := by
  intro hc
  have hH := h.point_mem_Hz_at F previous
  obtain ⟨C,hC,_,_⟩ := GuardedSource.local_exists_quasisimple_component
    d h hab structural previous faithful earlier F.H hH
  obtain ⟨hf,hfixed,⟨D⟩⟩ := original_point_chosen_of_plane_centralized_at
    d h hab structural previous faithful earlier source47 C hC hc
  let B := C.map F.H.subtype
  let W := ⁅(reducedTwoSubgroup F.H).map F.H.subtype,B⁆
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

/-- The actual point is the exact core commutator, with movement derived
from the original fixed-module source rather than assumed. -/
theorem original_core_commutator_eq_point_of_fixed_module_source_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (fixed : OriginalFixedModule1332At T L) :
    ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1 :=
  EightSource.core_commutator_eq_point_of_plane_moved h hab
    (original_plane_moved_of_fixed_module_source_at d h hab structural previous
      faithful earlier source47 fixed)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LinearThreeSource
