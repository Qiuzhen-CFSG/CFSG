module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.ComponentStatement
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Bender
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.AlternatingSmall
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.PSL3Two.Parabolics.SolvableOvergroups

/-!
# The proper A₅ overcomponent in the surviving source carriers

The binary rank-one row has solvable proper Sylow overgroups. The same
holds for the small alternating rows; binary dimensions four and five
are excluded by their actual full-Sylow local geometry. The remaining
binary dimension-three and G₂(2)' orders are prime to five. Hence a proper
local A₅ section in these actual carriers forces precisely A₇.
Source: Aschbacher–Smith 14.7.45(2), printed pp.1062–1063, using A.3.14.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.OvercomponentsAt
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G] [IsQuasisimple G]

/-- Only A₇ can properly contain the actual full-Sylow A₅ section among
binary rank-one and permitted source carriers. -/
theorem proper_five_section_rows_seven
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    (hne : B ≠ ⊤) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hm : (∃ n, 2 ≤ n ∧ ClassicalGroup.IsPSL G 2 (2^n)) ∨
      WholeResidualAssembly.ComponentRows G) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) := by
  have ht : (⊤ : Subgroup G).IsCComponent :=
    (show IsComponent G ⊤ from ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  have h5 : 5 ∣ Nat.card G :=
    (FiveLocalFF.SolvableQuotients.five_dvd_card B eB).trans B.card_subgroup_dvd_card
  rcases hm with ⟨n,hn,hm⟩ | hm
  · exact (hne (eq_of_bender_containing_component S hB ht le_top
      (.linear n hn (hm.of_mulEquiv topEquiv)))).elim
  rcases hm with ⟨n,hn,hn',⟨e⟩⟩ | ⟨n,hn,hn',⟨e⟩⟩ | he
  · have hn0 : n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn0 with rfl | hn0
    · have hc : Nat.card G = 168 :=
        (Nat.card_congr (e.trans Matrix.PSL3Two.equiv).toEquiv).trans Matrix.PSL3Two.card_PSL
      norm_num [hc] at h5
    · apply (FiveLocalFF.BinaryLinear.not_section_binary_linear S B hB eB hn0 ?_).elim
      exact ⟨ZMod 2,inferInstance,inferInstance,by simp,
        ⟨e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega)).symm⟩⟩
  · have hn0 : n = 5 ∨ n = 6 ∨ n = 7 := by omega
    rcases hn0 with rfl | rfl | rfl
    · exact (FiveLocalFF.AlternatingSmall.not_proper_five S B hB hne e).elim
    · exact (FiveLocalFF.AlternatingSmall.not_proper_six S B hB hne e).elim
    · exact ⟨e⟩
  · obtain ⟨e⟩ := he
    have hc : Nat.card G = 6048 := (Nat.card_congr e.toEquiv).trans
      (Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp))
    norm_num [hc] at h5

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideFiveContainment.OvercomponentsAt
