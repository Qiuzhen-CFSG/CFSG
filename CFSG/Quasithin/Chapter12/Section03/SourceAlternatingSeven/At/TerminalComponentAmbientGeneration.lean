module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentAmbientGeneration
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNormalizer
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentProperRigidity

/-!
# TerminalComponentAmbientGeneration at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalComponentAmbientGeneration`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V Y W : Subgroup G}

variable {S : Setup T L V} {D : S.LocalAnalysis}

namespace Setup

variable (SY : Setup T Y W)

include SY in

private theorem omega_sylow_le_core_omega_at :
    omegaCenterIn (T : Subgroup G) ≤
      omegaCenterIn ((Y ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let H := Y ⊔ (T : Subgroup G)
  have hHe : H ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_4_6 T (SY.hypothesis.simpleQTKE.evenCharacteristic T)
      ⟨SY.hypothesis.maximal_faithful.1.1.2.2,
        (show (T : Subgroup G) ≤ H from le_sup_right)⟩
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [H, Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow H (T.subtype le_sup_right)
  intro z hz
  obtain ⟨hzT, hzC, hz2⟩ := (mem_omegaCenterIn_iff _ _).mp hz
  have hzQ : z ∈ centralizer (H.pCoreIn 2 : Set G) := centralizer_le hQT hzC
  exact (mem_omegaCenterIn_iff _ _).mpr
    ⟨hHe ⟨(show (T : Subgroup G) ≤ H from le_sup_right) hzT, hzQ⟩, hzQ, hz2⟩

end Setup

namespace TerminalPoint

variable {P : TerminalPoint S D}

theorem overcomponent_le_normalizer_of_point_generation_at
    (F : P.Overcomponents) {W : Subgroup G} (SY : Setup T F.Y W)
    (hmovement : P.WeightSixMovement) (hmax : SY.CentralVectorMaximality)
    (hLe : P.Le ≤ F.Y) : F.Y ≤ normalizer (L : Set G) := by
  obtain ⟨f, hf, hweight, hcentral, hmove⟩ := hmovement
  have hYmove : ¬ F.Y ≤ centralizer ({(f : G)} : Set G) :=
    fun h => hmove (hLe.trans h)
  exact le_of_maximal_pointCentralizer (hmax f hcentral hYmove)
    hLe ((Le_le_original (P := P)).trans L.le_normalizer)
    (inf_le_right.trans (D.pointCentralizers f hf (Or.inr hweight))) hmove

theorem ambientA5Uniqueness_of_point_generation_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : P.Overcomponents) (hmovement : P.WeightSixMovement)
    (hmax : ∀ {W : Subgroup G} (SY : Setup T F.Y W),
      SY.CentralVectorMaximality) : AmbientA5Uniqueness (P := P) F := by
  intro W SY _ hLe
  have hYM := overcomponent_le_normalizer_of_point_generation_at F SY
    hmovement (hmax SY) hLe
  exact False.elim (P.residual_escape_at structural
    (F.residual_le.trans (F.le_maximal.trans hYM)))

theorem proper_component_eq_residual_of_point_generation_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (R : P.ResidualAnalysis) (F : P.Overcomponents)
    (hKY : P.K < F.Y) {W : Subgroup G} (SY : Setup T F.Y W)
    (A : A314RestrictionInput (P := P))
    (hLe : F.E = F.Y → P.Le ≤ F.Y)
    (hmovement : P.WeightSixMovement)
    (hmax : ∀ {W' : Subgroup G} (SY' : Setup T F.Y W'),
      SY'.CentralVectorMaximality) : F.E = P.K :=
  proper_component_eq_residual_at structural R F hKY SY A hLe
    (ambientA5Uniqueness_of_point_generation_at structural F hmovement hmax)

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

