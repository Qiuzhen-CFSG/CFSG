module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLocalRight
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightBender

/-!
# The normalized Bender source branch in Chapter 12

Both single and exchanged Bender rows construct the right factor on the
original H, S, and compatible Cartans. The single row uses the proved
intrinsic PSL₂/Suzuki/SU₃/PSU₃ quotient; the exchanged row keeps the
original component and uses the odd left-Cartan orbit bound in N_G(O²(H)).
Thus the local preparation requires no Bender-selection callback.

The remaining diagram selection and uniqueness over L are explicit in the
last theorem. Uniqueness is produced by qt-d-1222-rankone-global-uniqueness;
qt-d-1222-rankone-generic-global retains the diagram construction and final
completion recognition. No ambient model is inferred from this local pair.
Source: Aschbacher--Smith 5.1.10--11 and 5.2.4--5, pp.634--635,649--650;
the Chapter 12 application is on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original Bender source alternatives supply every right-factor field
for each compatible Cartan pair in the normalized Chapter 12 setup. -/
theorem rankOne_rightFactor_of_bender_source
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hs : Global.RightRankOneSource T L H)
    {A B : Subgroup G} (c : CartanPair T L H A B) :
    ∃ R : Subgroup G, Global.RightFactor T L H A B R :=
  Global.rankOne_source_rightFactor (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hgen c hN hs

/-- Local preparation is complete in both Bender rows once the independent
original uniqueness-over-L implication is supplied. -/
theorem rankOne_global_preparation_of_bender_source
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hs : Global.RightRankOneSource T L H) :
    ∃ A B R : Subgroup G, Global.Preparation T L H A B R :=
  D.rankOne_global_preparation_of_rightFactor h hmany hn hpsl hH hgen hN hunique
    (fun _ _ c => D.rankOne_rightFactor_of_bender_source h hmany hn hpsl hH hgen hN hs c)

/-- The actual source dispatcher leaves only the diagram family construction;
all Bender geometry is discharged. Uniqueness retains its original implication. -/
theorem rankOne_global_preparation_of_diagram_selection
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hnot : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hdiagram : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
      Global.RightDiagramSource T L H →
      ∃ ℛ : Set (Subgroup G), Global.RightGeometry T L H ℛ) :
    ∃ A B R : Subgroup G, Global.Preparation T L H A B R := by
  rcases Global.right_source_cases h.simpleQTKE D.sylow_normalizes_component hH hgen with hs | hs
  · exact D.rankOne_global_preparation_of_bender_source h hmany hn hpsl hH hgen hN hunique hs
  · obtain ⟨ℛ,d⟩ := hdiagram hnot hs
    exact D.rankOne_global_preparation_of_rightFactor h hmany hn hpsl hH hgen hN hunique
      (fun _ _ c => D.rankOne_rightFactor_of_geometry hH hN d c)

/-- Apply the completed Bender branch to the original global-exit consumer.
The diagram construction, original uniqueness, and completion recognition
remain explicit and must be discharged by the source assembly owner. -/
theorem rankOne_globalExit_of_diagram_and_recognition
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
      normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hdiagram : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
      Global.RightDiagramSource T L H →
      ∃ ℛ : Set (Subgroup G), Global.RightGeometry T L H ℛ)
    (hrecognize : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n →
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      1 < ChapterE.generationParameter H →
      ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
      localBorel T L ≤ normalizer (residual H : Set G) →
      ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      ChapterF.Source.HypothesisF11 ![L, R] (Global.sourceS L H) →
      RankOneModule.GlobalExit G) : RankOneModule.GlobalExit G := by
  apply D.rankOne_globalExit_of_local_sources_of_many h hmany hn hpsl hH hgen hthree hN
  · intro _ hH' hgen' hthree' hN'
    exact D.rankOne_global_preparation_of_diagram_selection h.toHypothesis1221 hmany hn hpsl
      hH' hgen' hthree' hN' hunique hdiagram
  · exact hrecognize

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
