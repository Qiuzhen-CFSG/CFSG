module

public import Theory.SpecificGroups.PSL3.OrdinaryCenterRecognition
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound
public import Theory.SpecificGroups.PSL3.BinaryComparison
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import GorensteinWalter.SL2UniversalCover

/-!
# The small binary odd-center covering cases

At field order four the universal kernel divides 48, while the scalar
projection has kernel order three. The comparison kernel is therefore a
two-group and vanishes in any odd-center quasisimple target. This gives
the literal SL₃(4) map over the prescribed projective marking.

At field order two, the actual PSL₃(2) ≃ PSL₂(7) comparison and the
prime-field SL₂ kernel theorem make every covering kernel a two-group.
An odd covering center is consequently trivial.

Source: Aschbacher–Smith A.2.18, printed p.40, and I.1.3(2),(6), p.407.
-/

public section

open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups
namespace Matrix.PSL3.BinaryOddCenterCover

universe u v
variable {F : Type u} [Field F] [Finite F]
variable {L : Type v} [Group L] [Finite L] [IsQuasisimple L]

private theorem twoCore_eq_bot (ho : Odd (Nat.card (center L))) :
    pCore 2 L = ⊥ := by
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
  have hd := card_dvd_of_le (IsQuasisimple.pCore_le_center (G := L) 2)
  have hk0 : k = 0 := by
    by_contra hk0
    exact ho.not_two_dvd_nat ((dvd_pow_self 2 hk0).trans (hk ▸ hd))
  exact (pCore 2 L).eq_bot_of_card_eq (by simpa [hk0] using hk)

/-- Descent through the exceptional two-primary kernel at field order four. -/
theorem exists_scalar_lift_four (hF : Nat.card F = 4)
    (e : L ⧸ center L ≃* PSL(3,F)) (ho : Odd (Nat.card (center L))) :
    ∃ k : SL(3,F) →* L, Function.Surjective k ∧
      (centralQuotientCover e).toMonoidHom.comp k = projection F := by
  let c := ExceptionalFourCover.coverOver F hF
  let a := (ExceptionalFourCover.coverOver_isUniversal F hF).lift (projectionCovering F)
  have ha : (projectionCovering F).comp a = c :=
    (ExceptionalFourCover.coverOver_isUniversal F hF).lift_fac (projectionCovering F)
  have hd : Nat.card c.toMonoidHom.ker ∣ 2 ^ 4 * Nat.card (projectionCovering F).toMonoidHom.ker := by
    rw [projectionCovering_toMonoidHom, card_projectionKernel, hF]
    change Nat.card (ExceptionalFourCover.coverOver F hF).toMonoidHom.ker ∣ 48
    rw [ExceptionalFourCover.coverOver_ker]
    exact ExceptionalFourCover.kernel_card_dvd
  let g : Covering L PSL(3,F) :=
    ⟨(centralQuotientCover e).toMonoidHom, (centralQuotientCover e).surjective⟩
  obtain ⟨k, hk⟩ := (ExceptionalFourCover.coverOver_isUniversal F hF).exists_covering_of_kernel_card_dvd
    a (projectionCovering F) ha hd g (twoCore_eq_bot ho)
  exact ⟨k.toMonoidHom, k.surjective, congrArg Covering.toMonoidHom hk⟩

/-- The odd center of a cover of PSL₃(4) divides three. -/
theorem center_card_dvd_three_four (hF : Nat.card F = 4)
    (e : L ⧸ center L ≃* PSL(3,F)) (ho : Odd (Nat.card (center L))) :
    Nat.card (center L) ∣ 3 := by
  obtain ⟨k, hks, hk⟩ := exists_scalar_lift_four hF e ho
  have hd := kernel_card_dvd_of_surjective_factor (projection F)
    (centralQuotientCover e).toMonoidHom k hks hk
  simpa only [centralQuotientCover_ker, card_projectionKernel, hF,
    show Nat.gcd 3 (4 - 1) = 3 by decide] using hd

/-- A nontrivial odd-center cover at field order four is SL₃(4), over the
original quotient map, even though SL₃(4) is not the universal cover. -/
theorem nontrivial_center_recognition_four (hF : Nat.card F = 4)
    (e : L ⧸ center L ≃* PSL(3,F)) (ho : Odd (Nat.card (center L)))
    (hz : center L ≠ ⊥) :
    Nat.card (center L) = 3 ∧ ∃ j : SL(3,F) ≃* L,
      (centralQuotientCover e).toMonoidHom.comp j.toMonoidHom = projection F := by
  have h3 : Nat.card (center L) = 3 := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ (center_card_dvd_three_four hF e ho)
      with h1 | h3
    · exact (hz ((center L).eq_bot_of_card_eq h1)).elim
    · exact h3
  obtain ⟨k, hks, hk⟩ := exists_scalar_lift_four hF e ho
  have hcount := kernel_card_eq_mul_of_surjective_factor (projection F)
    (centralQuotientCover e).toMonoidHom k (centralQuotientCover e).surjective hks hk
  have hker : Nat.card k.ker = 1 := by
    rw [card_projectionKernel, hF, centralQuotientCover_ker, h3] at hcount
    rw [show Nat.gcd 3 (4 - 1) = 3 by decide] at hcount
    omega
  let j : SL(3,F) ≃* L := MulEquiv.ofBijective k
    ⟨k.ker_eq_bot_iff.mp (k.ker.eq_bot_of_card_eq hker), hks⟩
  exact ⟨h3, j, hk⟩

/-- The actual binary endpoint has no nontrivial odd-center cover. -/
theorem center_eq_bot_two (hF : Nat.card F = 2)
    (e : L ⧸ center L ≃* PSL(3,F)) (ho : Odd (Nat.card (center L))) :
    center L = ⊥ := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Fact (3 < Nat.card (ZMod 7)) := ⟨by norm_num⟩
  let e7 := e.trans (binaryEquivPsl2Seven F hF)
  let g : Covering L PSL(2, ZMod 7) :=
    ⟨(centralQuotientCover e7).toMonoidHom, (centralQuotientCover e7).surjective⟩
  have hp := GorensteinWalter.PSL2Cover.kernel_isPGroup_of_card_prime (ZMod 7) g
    (by norm_num)
  have hZ : IsPGroup 2 (center L) := by
    change IsPGroup 2 (centralQuotientCover e7).toMonoidHom.ker at hp
    rwa [centralQuotientCover_ker] at hp
  rcases hZ.card_eq_or_dvd with h1 | hd
  · exact (center L).eq_bot_of_card_eq h1
  · exact (ho.not_two_dvd_nat hd).elim

end Matrix.PSL3.BinaryOddCenterCover
