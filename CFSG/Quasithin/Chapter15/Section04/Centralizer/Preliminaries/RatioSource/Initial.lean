module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.TheoremCInputs
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.SmallRatio
public import Theory.Representation.NormalElementaryQuotient
public import Theory.GroupTheory.ReducedNormal.Defs

/-!
# The initial solvability input to the cubic-ratio argument

The genuine universal A/C implications supply the component containment and
generation results used in 15.4.2(1),(2). This application stops before the
Xi-minus argument. Solvability then passes to M₀ and its actual centralizer
quotient, where the proved solvable dual-FF theorem gives the cubic bound.

Source: Aschbacher–Smith, 15.4.2(1),(2),(4), printed pp.1155–1156.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.RatioSource
open MaximalPrimeSource
universe u
variable {G : Type u} [Group G] [Finite G]

variable
  (hA : ∀ (X : Type u) [Group X] [Finite X],
    ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
  (hC : ∀ (X : Type u) [Group X] [Finite X],
    ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)

include hA hC in
/-- Parts (1),(2), before any use of 3.2.13 or part (3). -/
theorem initial_conclusions (T : Sylow 2 G) (h : SourceHypotheses T) :
    Chapter1.L G (T : Subgroup G) = ∅ ∧
      ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
        Group.IsSolvable M := by
  have hs := ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC hC
  have h312 := fun (X : Type u) [Group X] [Finite X] =>
    ChapterA.Section03.SourceComponents.containment (G := X) hA hs
  have h39 := fun (X : Type u) [Group X] [Finite X] =>
    ChapterA.Section03.SourceComponents.generation (G := X) hA hs
  have h36 := ChapterA.Section03.CComponentCommutation.noncentralStructureInput
    KnownSimple.IsKnownSimple.{u}
  exact ⟨InitialSource.source_lemma_15_4_2_one h312 h36 T h,
    fun _ hM hTM => InitialSource.source_lemma_15_4_2_two h312 h36 h39 T h hM hTM⟩

include hA hC in
/-- Every member of the actual local family over T is solvable. -/
theorem solvable_of_mem_HOver (T : Sylow 2 G) (h : SourceHypotheses T)
    {H : Subgroup G} (hH : H ∈ Chapter1.HOver G (T : Set G)) :
    Group.IsSolvable H := by
  have hc : pCore 2 H ≠ ⊥ := by
    intro he
    exact hH.1 (by simp only [Subgroup.pCoreIn, he, Subgroup.map_bot])
  obtain ⟨M, hM, hHM⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot H hc
  let : Group.IsSolvable M := (initial_conclusions hA hC T h).2 M hM (hH.2.trans hHM)
  exact Group.isSolvable_of_isSolvable_injective (f := inclusion hHM)
    (inclusion_injective hHM)

include hA hC in
/-- The dual-FF case on the original faithful quotient; part (3) is not an input. -/
theorem cubicRatio_le_two_of_dualFF
    (T : Sylow 2 G) (h : SourceHypotheses T) (M₀ : Subgroup G)
    (hM₀ : M₀ ∈ Chapter1.HOver G (T : Set G))
    (V : Subgroup M₀) (hV : IsPReduced 2 V) :
    letI := hV.normal
    letI := hV.elementary
    let ρ := Representation.NormalElementaryQuotient.representation V
      (QuotientGroup.mk' (centralizer (V : Set M₀)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    IsFFModule ρ.dual → cubicRatio ρ ≤ 2 := by
  let := hV.normal
  let := hV.elementary
  let : Group.IsSolvable M₀ := solvable_of_mem_HOver hA hC T h hM₀
  dsimp only
  intro hff
  exact ChapterB.SolvableDualFF.cubicRatio_le_two _ inferInstance
    hV.quotient_pCore_eq_bot
    (Representation.NormalElementaryQuotient.representation_injective V _
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) hff

end CFSG.Quasithin.Chapter15.Section04.RatioSource
