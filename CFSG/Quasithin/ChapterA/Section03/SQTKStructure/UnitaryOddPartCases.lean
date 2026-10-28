module

public import Theory.SpecificGroups.PSU3.UniversalCover.OddPartDescent
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.RankOneCoverCases
public import Theory.SpecificGroups.SU3.BinarySylowOrder
public import Theory.SpecificGroups.SU3.ProjectiveInvolution

/-!
# The unitary ordinary-component cases of A.3.6

Only the odd part of the universal PSU₃ kernel is relevant when the
original component has trivial two-core. The scalar-cover descent
preserves its given central-quotient map. The resulting center has order
one or three; in the latter case the descended map identifies the
component with the actual SU₃ group for the original Hermitian form.

Both source families conclude the full A36Conclusion, including every
common Fitting, radical and commutator clause. The characteristic-two
family retains SU₃(8) as a possible triple cover. The ternary endpoint
reuses its checked source case. The outstanding premises belong exactly
to the existing even large/three-primary and odd cross-odd producers;
the two-primary universal-kernel calculations are not inputs here.

Source: Aschbacher–Smith A.3.6, printed pp.43–45, with Theorem C's
model parameters in Remark A.2.4, p.33; I.1.1–I.1.4, pp.407–408.
-/

public section
noncomputable section

open Subgroup Theory.GroupTheory PerfectCentralCovering
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterA.SQTKStructure.UnitaryOddPartCases
open Chapter1.Section02 Chapter1.Section02.LocalModels
open HermitianForm.UniversalCover
universe u

private theorem a36_of_scalar_lift {X : Type u} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L)
    (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F)
    (q : ℕ) (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    (e : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (k : J.specialSubgroup →* L) (hks : Function.Surjective k)
    (hk : (e.toMonoidHom.comp (QuotientGroup.mk' (center L))).comp k =
      J.specialToProjective)
    (heven : 2 ∣ Nat.card (ProjectiveSpecialUnitaryMatrixGroup J))
    (hmodel : ∀ _j : L ≃* ProjectiveSpecialUnitaryMatrixGroup J, TheoremCModel L)
    (hparam : q % 3 = 2 → CoverParameter true q) : A36Conclusion L := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.symm.isSimpleGroup
  have hd : Nat.card (center L) ∣ Nat.gcd 3 (q + 1) := by
    have h := kernel_card_dvd_of_surjective_factor J.specialToProjective
      (centralQuotientCover e).toMonoidHom k hks hk
    simpa only [centralQuotientCover_ker, card_kernel J hcard hconj] using h
  have hcases := Nat.prime_three.eq_one_or_self_of_dvd _
    (hd.trans (Nat.gcd_dvd_left 3 (q + 1)))
  have hevenL : 2 ∣ Nat.card L := by
    have h : 2 ∣ Nat.card (L ⧸ center L) := (Nat.card_congr e.toEquiv).symm ▸ heven
    exact h.trans (card_quotient_dvd_card _)
  refine ⟨?_, ReadyCoverCases.common_of_quasisimple hevenL hcases⟩
  rcases hcases with hc1 | hc3
  · have hz : center L = ⊥ := (eq_bot_iff_card _).mpr hc1
    let f := centralQuotientCover e
    have hi : Function.Injective f.toMonoidHom := by
      apply f.toMonoidHom.ker_eq_bot_iff.mp
      change (centralQuotientCover e).toMonoidHom.ker = ⊥
      simpa only [centralQuotientCover_ker] using hz
    let j : L ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
      MulEquiv.ofBijective f.toMonoidHom ⟨hi, f.surjective⟩
    exact .simple hL j.isSimpleGroup (hmodel j)
  · have hg : Nat.gcd 3 (q + 1) = 3 :=
      Nat.dvd_antisymm (Nat.gcd_dvd_left 3 (q + 1)) (hc3 ▸ hd)
    have hm : q % 3 = 2 := by
      have h3 : 3 ∣ q + 1 := hg ▸ Nat.gcd_dvd_right 3 (q + 1)
      have := Nat.mod_eq_zero_of_dvd h3
      omega
    have hcount := kernel_card_eq_mul_of_surjective_factor J.specialToProjective
      (centralQuotientCover e).toMonoidHom k (centralQuotientCover e).surjective hks hk
    have hker : Nat.card k.ker = 1 := by
      rw [card_kernel J hcard hconj, hg, centralQuotientCover_ker, hc3] at hcount
      omega
    let j : J.specialSubgroup ≃* L := MulEquiv.ofBijective k
      ⟨k.ker_eq_bot_iff.mp (k.ker.eq_bot_of_card_eq hker), hks⟩
    have hz : Nonempty (center L ≃* Multiplicative (ZMod 3)) :=
      ⟨mulEquivOfPrimeCardEq hc3 (by simp)⟩
    exact .cover hL hz (.classical true q (hparam hm)
      ⟨F, inferInstance, inferInstance, J, hcard, hconj, ⟨j.symm⟩⟩)

/-- The full ordinary-component source conclusion for every permitted
PSU₃(2ⁿ) quotient, using only its outstanding odd-primary inputs. -/
theorem a36_unitary_even {X : Type u} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (n : ℕ) (hn : 2 ≤ n) (F : Type) [Field F] [Finite F]
    (J : HermitianForm 3 F)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (e : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hlarge : ∀ r : ℕ, r.Prime → 3 < r →
      ¬ r ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    (hnine : Odd n →
      ¬ 9 ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker) :
    A36Conclusion L := by
  let : IsQuasisimple L := hL.2
  obtain ⟨k, hks, hk⟩ := OddPartDescent.exists_lift_even J hn hcard hconj hlarge hnine
    (centralQuotientCover e).toMonoidHom (centralQuotientCover e).surjective hcore
  have heven : 2 ∣ Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) := by
    apply dvd_trans _ (HermitianForm.BinarySylowOrder.cube_dvd_card_projective
      J (by omega) hcard hconj)
    rw [← pow_mul]
    exact dvd_pow_self 2 (by omega : n * 3 ≠ 0)
  exact a36_of_scalar_lift L hL F J (2 ^ n) hcard hconj e k hks hk heven
    (fun j => .rank_one (.unitary n hn
      ⟨F, inferInstance, inferInstance, J, hcard, hconj, ⟨j⟩⟩))
    (fun hm => Or.inl ⟨n, by omega, rfl, hm⟩)

/-- The full ordinary-component source conclusion for all odd prime
PSU₃ parameters. The checked q=3 case is reused directly. -/
theorem a36_unitary_odd_prime {X : Type u} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (F : Type) [Field F] [Finite F]
    (J : HermitianForm 3 F)
    (hcard : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    (e : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hother : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → r ≠ p →
      ¬ r ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    (hnine : p % 3 = 2 →
      ¬ 9 ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker) :
    A36Conclusion L := by
  by_cases hp3 : p = 3
  · subst p
    exact RankOneCoverCases.a36_psu3_three L hL hcore F J hcard hconj e
  let : IsQuasisimple L := hL.2
  have hp2 : p ≠ 2 := fun h => by subst p; norm_num at ho
  obtain ⟨k, hks, hk⟩ := OddPartDescent.exists_lift_odd J (e := 1) hp hp2
    (by decide) (by decide) (by simpa only [pow_one] using hcard)
    (by simpa only [pow_one] using hconj) (by simp) hother
    (by simpa only [pow_one] using hnine)
    (centralQuotientCover e).toMonoidHom (centralQuotientCover e).surjective hcore
  exact a36_of_scalar_lift L hL F J p hcard hconj e k hks hk
    (Matrix.SU3.two_dvd_projective_card_of_prime_frobenius J p hp ho hcard hconj)
    (fun j => .three_odd p hp ho true
      ⟨F, inferInstance, inferInstance, J, hcard, hconj, ⟨j⟩⟩)
    (fun _ => Or.inr ⟨hp, ho⟩)

end CFSG.Quasithin.ChapterA.SQTKStructure.UnitaryOddPartCases
