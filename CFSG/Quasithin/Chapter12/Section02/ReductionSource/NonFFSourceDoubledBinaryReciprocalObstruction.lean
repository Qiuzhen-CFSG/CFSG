module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryReciprocalEscape
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedExcluded

/-!
# The original H-star actor with reciprocal escape

The actual odd prime-order actor selected in the multiple-overgroup branch
cannot have a unique residual normalizer: the placed-component reduction
would give an excluded native configuration. Apply reciprocal escape to that
same actor and retain the entire doubled orbit in the same selected core.

The J₄ maximal-two-local cover remains an explicit independent premise. The
Rudvalis exclusion is already proved. C.4.8/4.2.13 module forcing is still
needed to exclude the resulting pushing-up configuration.
Source: Aschbacher--Smith 4.2.5--13, 4.4.3--6 and 7.6.1.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Representation Representation.BinaryOffender
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- After the native J₄ cover, the original H-star odd actor has reciprocal
escape with the whole orbit in the same selected core. -/
theorem sourceOrbit_binary_reciprocal_obstruction_of_janko_cover
    (hnative : Janko4.LocalStructure.LargeCenterRadicals.MaximalTwoLocalCover)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : D.SourceOrbitNonFF)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ A : Subgroup G,
        A ≤ H ∧ A ≤ centralizer (D.sourceOrbit : Set G) ∧ Nat.card A = p ∧
        ¬ H ⊓ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
        ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
        ∃ J P W : Subgroup G, Witness L V A J P W ∧
          D.sourceOrbit ≤ J.pCoreIn 2 ∧
          J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L ∧
          ¬ (generalizedFitting (P ⧸ pCore 2 P)).comap
            (QuotientGroup.mk' (pCore 2 P)) ≤ (normalizer (L : Set G)).subgroupOf P := by
  obtain ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,hcases⟩ :=
    D.sourceOrbit_binary_native_oddLocal_obstruction h hd hmany hnon F hF hmodel
  have ho : Odd (Nat.card A) := hcard.symm ▸ hpo
  let : Fact p.Prime := ⟨hp⟩
  let : IsCyclic A := isCyclic_of_prime_card hcard
  have hne : A ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hcard
    have := hp.one_lt
    omega
  have hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) := by
    intro hu
    apply D.binaryPlacedNativeCase_false_of_janko_cover hnative A
    apply D.sourceOrbit_binary_placed_native_case h hd F hF hmodel A hAC ho
    exact D.sourceOrbit_binary_oddNormalizer_placed_jankoRudvalis
      h hd F hF hmodel A hne hAC ho hu (fun he => hout (inf_le_right.trans he))
  exact ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,hnot,
    D.sourceOrbit_binary_reciprocal_escape_witness h hd F hF hmodel A hAC ho hnot⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
