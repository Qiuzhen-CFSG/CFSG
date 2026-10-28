module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLocal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightGeometry
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightQuotient

/-!
# Applying the common right-factor construction in Chapter 12

The genuine E.2.2 dispatcher reduces the local source to independent
Bender-component and diagram-parabolic selections. Each producer must
construct the geometric family, including the actual O₂ quotient. The
common odd-Cartan and Hall argument then supplies every `RightFactor`
field for the chosen A and B, discharging the local-preparation `hright`
argument. The PSL₃(4) exclusion is passed explicitly to the diagram
producer, where it is required for S-normalization.

The exchanged row's intrinsic and ambient two-core quotient models are
proved in `RightQuotient`; its remaining family geometry is still required.

These are conditional assembly theorems. Neither selection producer is
asserted here, and uniqueness over L remains with its independent owner.
Source: Aschbacher--Smith 5.1.10--11,5.2.1,5.2.4, pp.634--635,646,649--650;
the Chapter 12 application is on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Every member of the source family gives the actual right factor;
no uniqueness-over-L hypothesis enters this construction. -/
theorem rankOne_rightFactor_of_geometry
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    {ℛ : Set (Subgroup G)} (d : Global.RightGeometry T L H ℛ)
    {A B : Subgroup G} (c : CartanPair T L H A B) :
    ∃ L₂ : Subgroup G, Global.RightFactor T L H A B L₂ :=
  d.exists_rightFactor c D.sylow_normalizes_component hH hN

/-- Conditional right-factor assembly from the two genuine source rows.
The diagram producer receives the precise excluded residual quotient. -/
theorem rankOne_rightFactor_of_source_cases
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hnot : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hrank : Global.RightRankOneSource T L H →
      ∃ ℛ : Set (Subgroup G), Global.RightGeometry T L H ℛ)
    (hdiagram : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
      Global.RightDiagramSource T L H →
      ∃ ℛ : Set (Subgroup G), Global.RightGeometry T L H ℛ)
    {A B : Subgroup G} (c : CartanPair T L H A B) :
    ∃ L₂ : Subgroup G, Global.RightFactor T L H A B L₂ := by
  have hgeom : ∃ ℛ : Set (Subgroup G), Global.RightGeometry T L H ℛ := by
    rcases Global.right_source_cases h.simpleQTKE D.sylow_normalizes_component hH hgen with hg | hg
    · exact hrank hg
    · exact hdiagram hnot hg
  obtain ⟨ℛ,d⟩ := hgeom
  exact D.rankOne_rightFactor_of_geometry hH hN d c

/-- The actual local-preparation consumer: the Cartan/Hall construction
discharges `hright`, retaining the two source selections and uniqueness. -/
theorem rankOne_global_preparation_of_right_source_cases
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
    (hrank : Global.RightRankOneSource T L H →
      ∃ ℛ : Set (Subgroup G), Global.RightGeometry T L H ℛ)
    (hdiagram : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
      Global.RightDiagramSource T L H →
      ∃ ℛ : Set (Subgroup G), Global.RightGeometry T L H ℛ) :
    ∃ A B L₂ : Subgroup G, Global.Preparation T L H A B L₂ := by
  exact D.rankOne_global_preparation_of_rightFactor h hmany hn hpsl hH hgen hN hunique
    (fun _ _ c => D.rankOne_rightFactor_of_source_cases h hH hgen hnot hN hrank hdiagram c)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
