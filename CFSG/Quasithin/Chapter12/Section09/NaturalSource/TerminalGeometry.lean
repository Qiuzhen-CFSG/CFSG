module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.FusionGeometry
public import Theory.GroupTheory.NormalizerControlOrbit

/-!
# Elementary deductions in the final S₃ argument

Failure of containment of W₀ produces a whole conjugate of the original seed
inside T. An overgroup escaping N_G(L) strictly enlarges the plane span by
12.9.7. Finally, if B is a hyperplane of the seed conjugate and its commutator
with that span lies in the point, the orbit count gives the required span
normalizer bound. The dimension assumption n=4 or 5 gives |B| > 4.

The actual overgroup, its S₃ quotient, the commutator bound and the final
moving conjugate still have to be constructed from the source inputs.
Source: Aschbacher--Smith, proof of 12.9.1, printed pp.863--864.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u
variable {X : Type u} [Group X] [Finite X]
variable {K : GroupClass.{u}} {T : Sylow 2 X} {L V : Subgroup X} {n : ℕ}

/-- The orbit-count application to the literal hyperplane and plane span. -/
theorem plane_span_normalizes_conjugate (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n)
    (hn : n = 4 ∨ n = 5)
    (control : ∀ i, 1 < i → i < n → F.Gi i ≤ normalizer (V : Set X))
    (H B : Subgroup X) (g : X) (hBA : B ≤ conjugate V g)
    (hindex : B.relIndex (conjugate V g) = 2)
    (hcomm : ⁅conjugateSpanBy (F.Vi 2) H, B⁆ ≤ F.Vi 1) :
    conjugateSpanBy (F.Vi 2) H ≤ normalizer (conjugate V g : Set X) := by
  have hcard : Nat.card (conjugate V g) = 2 ^ n := by
    change Nat.card (V.map (MulAut.conj g⁻¹).toMonoidHom) = _
    rw [card_map_of_injective (MulAut.conj _).injective, h.seed_card]
  have hbig : 4 < Nat.card B := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup X) B (conjugate V g) bot_le hBA
    simp only [relIndex_bot_left] at hc
    rw [hindex, hcard] at hc
    rcases hn with rfl | rfl <;> norm_num at hc <;> omega
  apply normalizes_of_order_two_commutator_and_normalizer_control hBA hbig
    (by simpa using F.card 1 (by have := h.rank; omega)) hcomm
  intro C hC hc
  exact normalizer_control_conjugate
    (fun B hB hb => subspace_normalizer_le h F control hB hb) g C hC hc

/-- The strict span assertion on p.863, using the actual 12.9.7 bound. -/
theorem plane_lt_span_of_escapes (h : HigherRankHypothesis K T L V n)
    (F : InvariantFlag T V n)
    (control : ∀ i, 1 < i → i < n →
      F.Gi i ≤ seedNormalizer (normalizer (L : Set X)) V)
    (H : Subgroup X) (hHM : ¬ H ≤ normalizer (L : Set X)) :
    F.Vi 2 < conjugateSpanBy (F.Vi 2) H := by
  apply lt_of_le_of_ne (le_conjugateSpanBy _ _)
  intro he
  have hHG : H ≤ F.Gi 2 := by
    change H ≤ normalizer (F.Vi 2 : Set X)
    rw [he]
    exact le_normalizer_conjugateSpanBy _ _
  exact hHM (hHG.trans ((control 2 (by omega) (by have := h.rank; omega)).trans
    (show seedNormalizer (normalizer (L : Set X)) V ≤ normalizer (L : Set X) from inf_le_left)))

omit [Finite X] in
/-- Extract a whole conjugate, retaining the right-conjugation convention. -/
theorem exists_conjugate_escaping_of_weakClosure (Q : Subgroup X)
    (hW : ¬ ChapterE.indexedWeakClosure V (T : Subgroup X) 0 ≤ Q) :
    ∃ g : X, conjugate V g ≤ (T : Subgroup X) ∧ ¬ conjugate V g ≤ Q := by
  by_contra! hn
  apply hW
  rw [ChapterE.weakClosure_eq_sSup_gamma]
  apply sSup_le
  intro A hA
  obtain ⟨g, rfl, hAT⟩ := (ChapterE.mem_gamma_zero_iff _ _ _).mp hA
  have he : conjugate V g⁻¹ = V.map (MulAut.conj g).toMonoidHom := by
    simp only [conjugate, inv_inv]
  exact he ▸ hn g⁻¹ (he.symm ▸ hAT)

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
