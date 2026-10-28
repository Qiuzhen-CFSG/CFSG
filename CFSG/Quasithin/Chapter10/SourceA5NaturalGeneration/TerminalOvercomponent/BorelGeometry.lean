module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SylowBorel
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.CrossCentralization
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.TerminalOvercomponent.OriginalSetup

/-!
# The original terminal component from the paired Borel geometry

The opposite commutator is a full Sylow subgroup of a centerless short block.
Consequently its cubic acts faithfully and the opposite Borel has nontrivial
two-core. The cubic fixing the common block Sylow centralizes the second block,
so the whole opposite Borel centralizes it. The original fundamental setup then
constructs the actual proper common component with three-rank at most one.

This removes the separate Borel-core, faithful-action and second-block
normalizer premises of the terminal construction. The common Sylow and paired
block geometry remain earlier source inputs. Source: Aschbacher–Smith
10.2.3(4), printed p.747.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open ChapterC Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual paired Sylow geometry supplies all Borel hypotheses for the
original proper common-component construction. -/
theorem source_original_natural_pair_borel_component
    (D₀ : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (L₂ K P D₁ D₂ : Subgroup G)
    (hL₂ : IsShort L₂) (hz₂ : center L₂ = ⊥) (hK : IsL2EvenBlock K 2)
    (hcomm : L₂ ≤ centralizer (L : Set G))
    (hP : Chapter1.IsSylowIn 2 P K) (hPL : P ≤ L)
    (hD₁L : D₁ ≤ L) (hD₁K : D₁ ≤ K) (hD₁ : Nat.card D₁ = 3)
    (hD₂L : D₂ ≤ L₂) (hD₂ : Nat.card D₂ = 3)
    (hD₂K : D₂ ≤ normalizer (K : Set G))
    (hSK : ChapterB.baumann (T : Subgroup G) ≤ normalizer (K : Set G))
    (hP₂ : Chapter1.IsSylowIn 2 ⁅ChapterB.baumann (T : Subgroup G),D₂⁆ L₂)
    (hR : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤
      normalizer ((⁅ChapterB.baumann (T : Subgroup G),D₂⁆ ⊔ D₂ : Subgroup G) : Set G))
    (hout : ¬ K ≤ D₀.maximalLocal) :
    ∃! C : Subgroup G,
      C ∈ Chapter1.cComponentsIn
        (normalizer ((⁅ChapterB.baumann (T : Subgroup G),D₂⁆ ⊔ D₂ : Subgroup G) : Set G)) ∧
      L < C ∧ K ≤ C ∧
      C ≤ centralizer ((⁅ChapterB.baumann (T : Subgroup G),D₂⁆ ⊔ D₂ : Subgroup G) : Set G) ∧
      primeRank 3 C ≤ 1 := by
  let S := ChapterB.baumann (T : Subgroup G)
  let S₂ := ⁅S,D₂⁆
  have hA : pCore 2 (S₂ ⊔ D₂ : Subgroup G) ≠ ⊥ :=
    IsShort.borel_core_ne_bot L₂ S₂ D₂ hL₂ hP₂ (normalizer_commutator_ge_right S D₂)
  have hf : D₂ ⊓ centralizer (S₂ : Set G) = ⊥ :=
    IsShort.cubic_sylow_action_faithful L₂ S₂ D₂ hL₂ hP₂ hz₂ hD₂L hD₂
  have hAL₂ : S₂ ⊔ D₂ ≤ L₂ := sup_le (Chapter1.isSylowIn_iff.mp hP₂).2.1 hD₂L
  have hLA : L ≤ centralizer ((S₂ ⊔ D₂ : Subgroup G) : Set G) :=
    le_centralizer_iff.mp (hAL₂.trans hcomm)
  have hKA : K ≤ normalizer ((S₂ ⊔ D₂ : Subgroup G) : Set G) :=
    (le_centralizer_iff.mp (source_natural_opposite_borel_centralizes
      L L₂ K P S D₂ hK.2.1 hP hPL hcomm hD₂ hD₂L hD₂K hSK).2).trans
        (Subgroup.centralizer_le_normalizer _)
  exact source_original_natural_borel_proper_common_component D₀ e hn S₂ D₂ K D₁
    hA hLA hR hKA hout hK hD₁L hD₁K hD₁ hf hD₂

end CFSG.Quasithin.Chapter10
