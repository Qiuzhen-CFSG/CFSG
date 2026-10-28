module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSelectionOrbit
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSelectionInversion
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSource

/-!
# Source applications of the pair splitting and prime-order selection

The constructed seed supplies the actual splitting W = U ⊕ C_W(I) and
[W,I] = [W,⟨g⟩] = U. In the prime-order case, invariant selection now
feeds the existing linear-block recognition, giving CyclicLocalAnalysis
on the same original H. The remaining conditional source assembly needs
selection only in the nonprime case.

Nonprime invariant Sylow selection, the extraspecial numerical reduction,
and its terminal binary-three contradiction remain with
qt-d-12213-cyclic-block. No unconditional 12.2.21–24 theorem is asserted.
Source: Aschbacher–Smith, printed pp.802–804.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d p : ℕ} {g : G}

/-- A prime-order initial odd Sylow gives the actual cyclic pair and linear block. -/
theorem cyclicLocalAnalysis_of_prime_constructionSeed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (hTI : IsTISubgroup V)
    (S : CyclicConstructionSeed T L V d p H P U g) (hc : Nat.card P = p) :
    ∃ P' U', CyclicLocalAnalysis T L V d H P' U' := by
  have hTV := ((structural G T L h).2.2 V D).1
  obtain ⟨P', U', g', v, R⟩ := S.invariantSelection_of_prime_order D A hTV hTI hc
  let : Fact p.Prime := ⟨S.prime⟩
  have hcard : Nat.card P' = p := by
    obtain ⟨Q, hQ⟩ := S.sylow
    obtain ⟨Q', hQ'⟩ := R.sylow
    rw [← hQ', card_map_of_injective H.subtype_injective,
      Nat.card_congr (Q'.equiv Q).toEquiv, ← card_map_of_injective H.subtype_injective,
      hQ, hc]
  have B := R.invariantOddLocalAnalysis D A hTV hTI
  exact ⟨P', U', B.cyclic_of_prime_order hcard hTV
    (linearTwoBlock_of_cyclic_core_displacement h D structural A B hcard
      (B.core_displacement_of_prime_order hcard hTV))⟩


/-- The final source consumer now requires invariant selection only for nonprime P. -/
theorem cyclicLocalAnalysis_of_nonprime_selection_and_extraspecial_steps
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (selectionStep : ∀ p H P U g, CyclicConstructionSeed T L V d p H P U g →
      Nat.card P ≠ p → ∃ P' U' g' v, CyclicInvariantSelection T L V d p H P' U' g' v)
    (numerical : ∀ p H P U W g v,
      InvariantOddLocalAnalysis T L V d p H P U W g v →
      IsExtraspecial p P → Nat.card P = p ^ 3 → Monoid.exponent P = p →
      W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥ →
      p = 3 ∧ d = 3 ∧ Nat.card W = 64)
    (terminal : ∀ p H P U W g v,
      InvariantOddLocalAnalysis T L V d p H P U W g v →
      IsExtraspecial p P → Nat.card P = p ^ 3 → Monoid.exponent P = p →
      W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥ →
      p = 3 → d = 3 → Nat.card W = 64 → False) :
    ∃ H P U, CyclicLocalAnalysis T L V d H P U := by
  have hTV := ((structural G T L h).2.2 V D).1
  apply cyclicLocalAnalysis_of_selection_and_extraspecial_steps h D structural A hnone hTI
    _ numerical terminal
  intro p H P U g S
  by_cases hc : Nat.card P = p
  · exact S.invariantSelection_of_prime_order D A hTV hTI hc
  · exact selectionStep p H P U g S hc


/-- Apply all pair-module identities to the seed constructed from the original
natural action. The extraspecial implication retains its exact branch hypothesis. -/
theorem exists_cyclicConstructionSeed_with_pair_splitting
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V) :
    ∃ p H P U g v, ∃ _S : CyclicConstructionSeed T L V d p H P U g,
      orderOf g = p ∧ v ∈ V ∧ v ∉ U ∧ v * g * v⁻¹ = g⁻¹ ∧
      (let W := componentOrbit (H.pCoreIn 2 ⊓ V) H
       let I := cyclicPairJoin (zpowers g) U V
       ⁅W, I⁆ = U ∧ ⁅W, zpowers g⁆ = U ∧
         W = U ⊔ (W ⊓ centralizer (I : Set G)) ∧
         Disjoint U (W ⊓ centralizer (I : Set G))) ∧
      (IsExtraspecial p P → (frattini P).map P.subtype ≤ normalizer (U : Set G)) := by
  obtain ⟨H, hH⟩ := A.exists_hstar
  obtain ⟨p, P, U, g, v, S, hg, hv, _, hvU, hi⟩ :=
    chosen_hstar_exists_cyclicConstructionSeed D A hTV hTI hH
  have hm := S.orbit_commutator_pair D A hTV
  have hs := S.orbit_split_pair D A hTV hTI hv hvU hi
  exact ⟨p, H, P, U, g, v, S, hg, hv, hvU, hi, ⟨hm.1, hm.2, hs⟩,
    S.frattini_normalizes_core_of_extraspecial D A hTV⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
