module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.LinearThreeExclusion.EvenModels
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.ModelCases
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.StarTransport
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.ExceptionalG2

/-!
# Excluding odd-characteristic linear-three models from the full sieve

For p > 3, neither SL₃(p) nor PSL₃(p) occurs in the complete model
projection of C.2.7. Fixed exceptional groups are excluded by their actual
orders, and even-field groups by elementary abelian two-rank followed by
order comparison. Every constructor of `ModelCases` is retained in the
case split, including the full triple cover and the derived group G₂(2)′.

The two non-block constructors describe the star image, not K/O₂(K).
The source kernel bound makes the actual comparison a nontrivial perfect
central cover. We compare the quotients by their centers through that
cover; we do not identify SL₃(p) with its projective quotient.

This proves the conditional comparison consumed by the proof of 1.3.8.
The source assembly must derive `StarKernelBound` and `ModelCases` from
the complete C.2.7 statement.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 1.3.8, printed p.514; C.2.7(3), printed pp.145–147.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve
open LinearThreeExclusion
variable {G : Type*} [Group G] [Finite G]

/-- Every model in the full C.2.7 projection is incompatible with either
odd-prime linear-three cover, using the actual star comparison. -/
theorem ModelCases.not_linearThree {p : ℕ} [Fact p.Prime]
    {H₀ K R : Subgroup G} (hc : ModelCases H₀ K R)
    (hp : 5 ≤ p) (ho : Odd p) (hRK : R ≤ normalizer K)
    (hq : IsQuasisimple (XiQuotient K)) (hb : StarKernelBound K R) :
    ¬ XiEmbedding.LinearThreeModel p (XiQuotient K) := by
  intro hm
  have hstar : ClassicalGroup.IsPSL
      ((starImage K R K) ⧸ center (starImage K R K)) 3 p :=
    (linearThree_center_model hm).of_mulEquiv
      (coreStarCenterEquiv hRK hq (starImage_ne_bot_of_bound hRK hq hb)).symm
  cases hc with
  | binary _ hmodel =>
    obtain ⟨n, _, _, F, _, _, _, hmodel, _⟩ := hmodel
    exact not_even_rankOne_model hp ho hm hmodel
  | alternating n hlo hhi _ hmodel =>
    obtain ⟨e⟩ := hmodel.2.2.quotient_iso
    have hcard : Nat.card (XiQuotient K) ≤ 20160 := by
      let _ : NeZero n := ⟨by omega⟩
      let _ : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      interval_cases n <;> norm_num
    exact not_linearThree_of_small_order hp hcard hm
  | ahatSix hmodel =>
    obtain ⟨e⟩ := hmodel.2.2.2.1
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (center (XiQuotient K))
    rw [Nat.card_congr e.toEquiv, hmodel.2.2.1, nat_card_alternatingGroup,
      Nat.card_fin] at hcard
    exact not_linearThree_of_small_order hp (by norm_num at hcard ⊢; omega) hm
  | exceptionalSeven hmodel =>
    obtain ⟨e⟩ := hmodel.2.1
    have hcard : Nat.card (XiQuotient K) ≤ 20160 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    exact not_linearThree_of_small_order hp hcard hm
  | symplecticFour hmodel =>
    obtain ⟨_, F, _, _, hF, rho, ⟨model⟩, _⟩ := hmodel
    have hcard : Nat.card (XiQuotient K) = 979200 := by
      rw [Nat.card_congr model.quotientIso.toEquiv,
        Theory.SpecificGroups.SymplecticFour.card_sp F, hF]
      norm_num
    exact not_linearThree_of_large_exceptional_order hp (Or.inl hcard) hm
  | binaryG2 hmodel =>
    obtain ⟨e⟩ := hmodel
    have hcard : Nat.card (XiQuotient K) = 6048 := by
      rw [Nat.card_congr e.toEquiv,
        Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
      exact Atlas.G2.BinaryException.card_H
    exact not_linearThree_of_small_order hp (by omega) hm
  | linearThree hmodel =>
    obtain ⟨n, _, F, _, _, hF, he⟩ := hmodel
    have heven : ClassicalGroup.IsPSL
        ((starImage K R K) ⧸ center (starImage K R K)) 3 (2 ^ n) :=
      linearThree_center_model (Or.inl ⟨F, inferInstance, inferInstance, hF, he⟩)
    exact not_even_projective_model hp ho hstar heven
  | binaryLinear n hn hmodel =>
    have hcenter := projective_center_model (n := n) (by rcases hn with rfl | rfl <;> decide) hmodel
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hcenter
    rcases hn with rfl | rfl
    · have hcard := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
      rw [← Nat.card_congr e.toEquiv, hF] at hcard
      norm_num [Fin.prod_univ_succ] at hcard
      exact not_linearThree_of_small_order hp (by omega) (Or.inr hstar)
    · have hcard := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
      rw [← Nat.card_congr e.toEquiv, hF] at hcard
      norm_num [Fin.prod_univ_succ] at hcard
      exact not_linearThree_of_large_exceptional_order hp (Or.inr hcard) (Or.inr hstar)

/-- The linear-three branch of 1.3.4 is excluded once the two displayed
consequences of C.2.7 have been established for the pushing-up component. -/
theorem not_linearThreeModel {κ : GroupClass} {p : ℕ}
    {T X P M H₀ K : Subgroup G}
    (h : PushingUpComponent κ p T X P M H₀ K) (hp : 3 < p)
    (hb : StarKernelBound K ((X ⊔ T).pCoreIn 2))
    (hc : ModelCases H₀ K ((X ⊔ T).pCoreIn 2)) :
    ¬ XiEmbedding.LinearThreeModel p (XiQuotient K) := by
  let _ : Fact p.Prime := ⟨h.local_input.prime⟩
  have hp5 : 5 ≤ p := by
    obtain ⟨a, ha⟩ := h.local_input.odd
    omega
  exact hc.not_linearThree hp5 h.local_input.odd h.radical_normalizes h.quasisimple hb

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve
