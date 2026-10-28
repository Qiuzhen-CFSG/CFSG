module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter.Commutator
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter.Marking

/-!
# Normal generation on a Fitting subgroup of prime order

For a normal subgroup F of order dividing a prime, [F,A] is either trivial
or all of F. In the former case the normal centralizer of F contains the
full ambient conjugate span of A. Thus if N is that span, [F,N,A]=[F,N].
The specialization to the actual Thompson image uses its published Sylow
marking. Model branches must prove the Fitting order bound separately.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6, printed p.105, and the paragraph after 13.6.13, printed p.929.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FittingCenter.Generation
variable {D : Type*} [Group D] [Finite D]
theorem commutator_generation_of_card_dvd_prime
    (F N A : Subgroup D) [F.Normal] {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card F ∣ p) (hN : N = conjugateSpanBy A ⊤) :
    ⁅⁅F, N⁆, A⁆ = ⁅F, N⁆ := by
  have hAN : A ≤ N := hN ▸ le_conjugateSpanBy A ⊤
  by_cases hz : ⁅F, A⁆ = ⊥
  · have hAC : A ≤ centralizer (F : Set D) :=
      commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm A F).trans hz)
    have hNC : N ≤ centralizer (F : Set D) := by
      rw [hN]
      exact conjugateSpanBy_le hAC (by rw [normalizer_eq_top])
    have hFN : ⁅F, N⁆ = ⊥ := by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hNC
    rw [hFN, commutator_bot_left]
  · have he : ⁅F, A⁆ = F := by
      apply eq_of_le_of_card_ge (commutator_le_left F A)
      have hc := (Nat.dvd_prime hp).mp
        ((card_dvd_of_le (commutator_le_left F A)).trans hcard)
      rcases hc with hc | hc
      · exact (hz (card_eq_one.mp hc)).elim
      · rw [hc]
        exact Nat.le_of_dvd hp.pos hcard
    have hFN : ⁅F, N⁆ = F := le_antisymm (commutator_le_left _ _)
      (he.symm.le.trans (commutator_mono le_rfl hAN))
    rw [hFN, he]

theorem fittingCommutator_generation_of_card_dvd_prime
    (N A : Subgroup D) [N.Normal] {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (fittingSubgroup N) ∣ p)
    (hN : N = conjugateSpanBy A ⊤) :
    ⁅fittingCommutator N, A⁆ = fittingCommutator N := by
  apply commutator_generation_of_card_dvd_prime (fittingImage N) N A hp
  · rwa [fittingImage, card_map_of_injective N.subtype_injective]
  · exact hN


variable {G : Type*} [Group G] [Finite G]

/-- Apply the prime-order reduction to the literal Thompson star image. -/
theorem thompson_generation_of_fitting_card_dvd_prime
    (T : Subgroup G) (z v : G)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card (fittingSubgroup (JGstar z v)) ∣ p) :
    ⁅fittingCommutator (JGstar z v),
      starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ =
        fittingCommutator (JGstar z v) := by
  let : (JGstar z v).Normal := JGstar_normal z v
  obtain ⟨_, _, _, _, hgen⟩ := exists_starSylow_marking T z v hSyl
  exact fittingCommutator_generation_of_card_dvd_prime _ _ hp hcard hgen

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FittingCenter.Generation
