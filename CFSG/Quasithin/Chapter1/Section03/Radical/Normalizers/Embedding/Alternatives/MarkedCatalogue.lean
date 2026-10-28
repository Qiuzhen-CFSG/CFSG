module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Alternatives.MarkedSmallOrders

/-!
# The remaining actual containing models in the marked A.3.12 argument

Start with the full known-simple A.3.6 catalogue for the image of K in
N/O₂(N), supplied by the radical obstruction. Apply the marked full-Sylow
and odd-rank exclusions to that same image. The result keeps actual carrier
isomorphisms in every remaining branch, including the binary linear
central covers. The odd ternary branch keeps both signs and both the
projective and special groups.

This is a partial containing-model inspection, not the A.3.12 embedding
or the source case-ten extension. The remaining nonternary branches and
the elementary kernel in the ternary branch are still proof obligations.
Source: Aschbacher–Smith A.3.12, pp.47–48, in the proof of 1.3.8, p.513.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
open Section02 Section02.LocalModels ClassificationModels
open CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Alternatives
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original source setup eliminates the small and rank-one containing
models without an A.3.12 embedding premise. Every remaining branch carries
the actual model of the original quotient image. -/
theorem SourceData.containing_model_remainder
    {p r : ℕ} {L : Subgroup G} {T : Sylow 2 G}
    {C : Subgroup (radicalCore p L T)} {K : Subgroup G}
    (h : SourceData KnownSimple.IsKnownSimple p r L T C K) :
    let D := quotientImage K (normalizer (C.map (radicalCore p L T).subtype : Set G))
    IsQuasisimple D ∧ (
      (∃ q : ℕ, q.Prime ∧ Odd q ∧ ∃ unitary : Bool,
        IsPSLSign D unitary 3 q ∨ IsSLSign D unitary 3 q) ∨
      (∃ n : ℕ, 1 ≤ n ∧ Triality.Standard.IsTrialityGroupAt (2 ^ n) D) ∨
      (∃ m : ℕ, 1 ≤ m ∧ IsReeF4At D m) ∨
      Nonempty (D ≃* Tits.ParrottGroup) ∨
      (∃ name : SporadicName,
        (name = .j2 ∨ name = .hs ∨ name = .ru ∨ name = .he ∨ name = .j4) ∧
          Nonempty (D ≃* name.Carrier)) ∨
      (∃ n : ℕ, 1 ≤ n ∧ IsSL D 3 (2 ^ n))) := by
  let := h.characteristic
  have ho : Odd p := h.prime.odd_of_ne_two (by have := h.large; omega)
  obtain ⟨hquasi, hmodels⟩ := actual_containing_image_models_knownSimple
    h.ambient p h.prime ho L T C h.nontrivial K h.component h.residual_lt
    h.local_Y h.contains_xi h.nonsimple_Y h.radical_exclusion
  refine ⟨hquasi, ?_⟩
  rcases hmodels with ⟨_, hm⟩ | ⟨_, hm⟩
  · cases hm with
    | alternating n hn hm => exact (h.containing_not_alternating hn hm).elim
    | linear_odd q e hq ho he _ hm =>
      rcases he with rfl | rfl
      · exact (h.containing_not_prime_psl2 hq ho (by simpa only [pow_one] using hm)).elim
      · exact (h.containing_not_quadratic_psl2 hq ho hm).elim
    | three_odd q hq ho sign hm => exact .inl ⟨q, hq, ho, sign, .inl hm⟩
    | rank_one hm => exact (h.containing_not_bender hm).elim
    | rank_two hm =>
      cases hm with
      | linear n hn hm =>
        by_cases hlarge : 1 < n
        · exact (h.containing_not_binary_psl3 hlarge hm).elim
        · have he : n = 1 := by omega
          subst n
          exact (h.containing_not_small_binary_linear (by omega : 3 ≤ 3 ∧ 3 ≤ 5)
            (by simpa only [pow_one] using hm)).elim
      | symplectic n hn hm => exact (h.containing_not_binary_psp4 hn hm).elim
      | g2 n hn hm => exact (h.containing_not_binary_g2 hn hm).elim
      | triality n hn hm => exact .inr (.inl ⟨n, hn, hm⟩)
      | ree m hm he => exact .inr (.inr (.inl ⟨m, hm, he⟩))
      | symplectic_derived hm => exact (h.containing_not_symplectic_derived hm).elim
      | g2_derived hm => exact (h.containing_not_g2_derived hm).elim
      | tits hm => exact .inr (.inr (.inr (.inl hm)))
    | binary_linear n hn hm =>
      exact (h.containing_not_small_binary_linear (by rcases hn with rfl | rfl <;> omega) hm).elim
    | sporadic name hne hm =>
      exact .inr (.inr (.inr (.inr (.inl ⟨name, h.containing_sporadic_name name hne hm, hm⟩))))
    | janko_one hm => exact (h.containing_not_janko_one hm).elim
  · cases hm with
    | classical sign q hq hm =>
      rcases hq with ⟨n, hn, rfl, _⟩ | ⟨hq, ho⟩
      · cases sign with
        | false => exact .inr (.inr (.inr (.inr (.inr ⟨n, hn, hm⟩))))
        | true => exact (h.containing_not_binary_su3 (by omega) hm).elim
      · exact .inl ⟨q, hq, ho, sign, .inr hm⟩
    | alternating_six hm => exact (h.containing_not_alternating_cover (.inl rfl) hm).elim
    | alternating_seven hm => exact (h.containing_not_alternating_cover (.inr rfl) hm).elim
    | mathieu hm => exact (h.containing_not_mathieu_cover hm).elim

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
