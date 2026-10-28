module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FullActions
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Assembly
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Generation

/-!
# The actual local actions in the large extraspecial branch

The completed A/C source theorems give component generation in each literal
local subgroup. The original counterexample gives the unique maximal two-local
over LT. Together with the extraspecial calculation, these construct every
field of LocalSourceData, including the full action for each original Y-member.

The final consumer removes the local-action callback from the three-vertex
assembly. The marked-model partner remains with this large-branch owner;
the genuine A₃ incidence theorem is owned by qt-d-12213-three-recognition.
The earlier faithful classification is owned by qt-d-1434-source. This is
not yet the unconditional 14.4.13 contradiction.

Source: Aschbacher--Smith, 1.2.1(1), 1.2.7, 14.3.3 and 14.4.8,
printed pp.503,506,990,1009.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.LocalAction LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Generation in every source local subgroup, with the A/C inputs discharged. -/
theorem source_component_generation (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) :
    EarlierComponentGeneration G := by
  intro A hA
  exact Chapter1.Section02.proposition_1_2_1_one_of_A_3_9
    (fun X _ _ hX hO => ChapterA.Section03.SourceComponents.generation
      (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
      (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
        (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y))) hX hO)
    (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hA)

/-- Construct full local action and ambient uniqueness on the original flag. -/
def source_local_data (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    LocalSourceData T L V F g := by
  have hlocal := source_full_actions d earlier hq chosen structural alternatives
    (source_component_generation d.qtke) classification F hne hZ g hg hgP hgH
  refine ⟨fun X hX => (hlocal X hX).1.some, ?_⟩
  let h := higherRankHypothesis d earlier hq chosen
  have unique : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S A hA
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hA
  intro K hK hLK
  exact Set.mem_singleton_iff.mp ((h.maximal_unique structural unique).2 ▸
    show K ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
      from ⟨hK, hLK⟩)

/-- The literal overgroup consumer with its local-action premise discharged. -/
theorem source_large_exclusion_of_partner (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (partnerSource : ∀ g : G, g ∈ L → g ∈ F.P L → g ∉ F.H →
      LocalSourceData T L V F g → Partner T L V F g)
    (incidence : ∀ (K : Subgroup G) (S : Quasithin.I5.DSystem .A3 K), S.Q 0 ≠ ⊥ →
      Nonempty (Quasithin.I5.A3Recognition.GeometryData S)) : False := by
  exact source_large_exclusion_of_inputs d earlier hq chosen structural alternatives F hne hZ hlarge
    (fun g hg hgP hgH => ⟨source_local_data d earlier hq chosen structural alternatives
      classification F hne hZ g hg hgP hgH⟩) partnerSource incidence
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
