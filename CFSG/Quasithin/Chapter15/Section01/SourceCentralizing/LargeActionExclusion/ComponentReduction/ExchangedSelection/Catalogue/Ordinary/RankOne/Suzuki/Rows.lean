module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.Suzuki.Simple
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.Suzuki.Normalized

/-!
# Applying the Suzuki exclusions to the full ordinary rank-one row

The Bender constructor's Suzuki branch is excluded without assuming component
normality. The exceptional Sz(8)-quotient branch can remain only if S does
not normalize the component and its central two-core is nontrivial. The
actual Borel equality is retained in both applications. The linear and
unitary branches still require their own model geometry; this theorem is
not a full 15.1.21 exclusion.

Source: Aschbacher--Smith 15.1.20(3a) and 15.1.21(i), pp.1097--1098.
The remaining rank-one and early quotient assembly stays with
`qt-e-15121-ordinary-rankone`.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The exact alternatives left in the full source row after the proved
Suzuki exclusions, retaining nonsplit central covers. -/
theorem PreExclusionSource.rankOne_after_suzuki
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hmodel : IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1))
    (hB : d.ML = d.ordinaryBorel) :
    (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSL d.L 2 (2 ^ f)) ∨
    (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSU d.L 3 (2 ^ f)) ∨
    (Nonempty ((d.L ⧸ pCore 2 d.L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1) ∧
      ¬ d.S ≤ normalizer (d.L : Set G) ∧ pCore 2 d.L ≠ ⊥) := by
  rcases hmodel with hmodel | he
  · cases hmodel with
    | linear f hf he => exact .inl ⟨f,hf,he⟩
    | unitary f hf he => exact .inr (.inl ⟨f,hf,he⟩)
    | suzuki m hm he =>
        obtain ⟨e⟩ := he
        exact (s.false_of_suzuki_simple (h := h) hG hM hJ hL (by omega) e hB).elim
  · obtain ⟨e⟩ := he
    refine .inr (.inr ⟨⟨e⟩,?_,?_⟩)
    · intro hn
      exact s.false_of_suzuki_normalized (h := h) hG hM hJ hL hn (by decide) e hB
    · intro hz
      let q : d.L ≃* (d.L ⧸ pCore 2 d.L) :=
        ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm
      exact s.false_of_suzuki_simple (h := h) hG hM hJ hL (by decide) (q.trans e) hB

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
