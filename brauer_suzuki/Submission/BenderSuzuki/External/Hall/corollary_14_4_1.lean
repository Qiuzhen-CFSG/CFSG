/-
Authors: OpenAI
-/

module

public import Submission.BenderSuzuki.External.Hall.lemma_14_4_3

/-!
# Hall Corollary 14.4.1
-/

namespace BenderSuzuki
namespace External

universe u

/-- Hall Corollary 14.4.1: if every diagonal defect is trivial in the transfer
target, then the transfer of any element of `H` is the `[G:H]`-th power
of that element in the target. -/
public theorem hall_corollary_14_4_1_transfer_congruent_self
    {G A : Type u} [Group G] [Finite G]
    {H : Subgroup G} [H.FiniteIndex] [CommGroup A] (φ : H →* A)
    (hdefect : ∀ h : H, hallDiagonalDefect (H := H) φ h = 1) :
    ∀ h : H, MonoidHom.transfer φ (h : G) = (φ h) ^ H.index := by
  classical
  intro h
  have hdiag_self :
      ∀ a : H, hallDiagonalContribution (H := H) φ (a : G) = φ a := by
    intro a
    have hmul := congrArg (fun x : A => φ a * x) (hdefect a)
    simpa [hallDiagonalDefect, mul_assoc] using hmul
  haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers (h : G)) (G ⧸ H))) :=
    Fintype.ofFinite _
  rw [Subgroup.index_eq_sum_minimalPeriod H (h : G), ← Finset.prod_pow_eq_pow_sum,
    MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  refine Finset.prod_congr rfl ?_
  intro q _
  let m : ℕ := Function.minimalPeriod ((h : G) • ·) q.out
  let a : H :=
    ⟨q.out.out⁻¹ * (h : G) ^ m * q.out.out,
      QuotientGroup.out_conj_pow_minimalPeriod_mem H (h : G) q.out⟩
  let hm : H := ⟨(h : G) ^ m, H.pow_mem h.property m⟩
  let t : Gˣ := ⟨q.out.out⁻¹, q.out.out, by simp, by simp⟩
  have hconj : IsConj ((h : G) ^ m) (a : G) := by
    refine ⟨t, ?_⟩
    change (t : G) * ((h : G) ^ m) = (a : G) * (t : G)
    simp [t, a, mul_assoc]
  have hdiag_conj :
      hallDiagonalContribution (H := H) φ ((h : G) ^ m) =
        hallDiagonalContribution (H := H) φ (a : G) :=
    (hall_lemma_14_4_2_diagonal_contribution_conjugacy (H := H) φ).1
      ((h : G) ^ m) (a : G) hconj
  have hterm : φ a = φ hm := by
    calc
      φ a = hallDiagonalContribution (H := H) φ (a : G) := (hdiag_self a).symm
      _ = hallDiagonalContribution (H := H) φ ((h : G) ^ m) := hdiag_conj.symm
      _ = φ hm := hdiag_self hm
  change φ a = φ h ^ m
  calc
    φ a = φ hm := hterm
    _ = φ (h ^ m) := by
      congr 1
    _ = φ h ^ m := map_pow φ h m

end External
end BenderSuzuki
