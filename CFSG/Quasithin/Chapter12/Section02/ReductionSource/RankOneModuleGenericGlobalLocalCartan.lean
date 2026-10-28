module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalCartan
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobal

/-!
# Source Cartan preparation on the original Chapter 12 configuration

Uniqueness of the maximal two-local over LT excludes L ≤ H for the
actual outside H. The characteristic-two PSL₂ quotient and original
E.2.2 construction now prove all three inputs of 5.1.5. Hall existence
therefore supplies the compatible Cartans before either residual branch
is chosen. The core S has exactly the source intersection with L.

Source: Aschbacher--Smith, 5.1.5, 5.1.9 and 5.1.11(2), printed
pp.631,634--635; the Chapter 12 application is on p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Uniqueness over LT, from the genuine 1.2.7 theorem, excludes L ≤ H.
This does not use or assert the stronger uniqueness over L in 4.3.2. -/
theorem rankOne_not_le_hstar
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ¬ L ≤ H := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have he : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl
      D.sylow_normalizes_component) (le_componentOrbit L T)
  have hc : pCore 2 H ≠ ⊥ := by
    intro hb
    apply hH.1.1.1
    simp only [Subgroup.pCoreIn, hb, Subgroup.map_bot]
  obtain ⟨X, hX, hHX⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot H hc
  intro hLH
  have hx := hu.normalizer_unique X hX
  rw [he] at hx
  have hXM := hx ((sup_le hLH hH.1.1.2).trans hHX)
  exact hH.1.2 (hXM ▸ hHX)

/-- All common hypotheses of the compatible-Hall construction, without a
residual-normalization assumption or a prescribed Hall subgroup. -/
theorem rankOne_cartanPreparation
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) : CartanPreparation T L H := by
  exact ⟨localBorel_isSolvable hn hpsl D.sylow_normalizes_component,
    hstar_intersection_isSolvable h.simpleQTKE D.sylow_normalizes_component hH hgen,
    intersection_normalizes_localBorel hpsl D.sylow_normalizes_component
      hH.1.1.2 (D.rankOne_not_le_hstar h hH)⟩

/-- The genuine odd Hall subgroups of both literal source groups, with the
right Hall subgroup normalizing the left one, as in Notation 5.1.9. -/
theorem rankOne_exists_cartanPair
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) :
    ∃ A B : Subgroup G, CartanPair T L H A B :=
  (D.rankOne_cartanPreparation h hn hpsl hH hgen).exists_cartanPair

/-- Original 5.1.11(2) on the source core S=O₂(N_G(L)∩H). -/
theorem rankOne_sourceS_intersection_left
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Global.sourceS L H ⊓ L = (T : Subgroup G) ⊓ L ∧
      ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = Global.sourceS L H ⊓ L := by
  have he := sourceS_intersection_left hpsl D.sylow_normalizes_component
    hH.1.1.2 (D.rankOne_not_le_hstar h hH)
  exact ⟨he, he.symm ▸ exists_sylow_component D.sylow_normalizes_component⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
