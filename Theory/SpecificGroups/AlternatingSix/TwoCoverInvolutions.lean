module

public import Theory.Alternating.proposition_5_2_7_8

/-!
# Involutions in two-covers of A₆

Every square-one element of a quasisimple double cover of A₆ lies in its
kernel. A nonidentity involution of A₆ moves four letters: its cycles have
length two, and its sign forces an even number of those cycles. Schur's
square formula then gives a nontrivial square for every lift. The unique
isomorphism to the concrete Schur cover transports this calculation from
`Type` to a cover in an arbitrary universe.

For a quasisimple group with central quotient A₆, the center order divides
six. If its center is a two-group, its order therefore divides two, and a
noncentral involution rules out the double cover.

Source: GLS, *The Classification of the Finite Simple Groups*, vol. 3,
Theorem 5.2.3 and Proposition 5.2.4(a). This is the intrinsic cover fact
used in the S₆ case of Aschbacher–Smith 13.6.6, printed p.927.
-/

open Subgroup Theory.GroupTheory GLS3.Chapter5 GLS3.Chapter5.SchurPresentation
namespace AlternatingSix.TwoCoverInvolutions

private theorem support_card (σ : alternatingGroup (Fin 6)) (hsq : σ ^ 2 = 1)
    (hne : σ ≠ 1) : σ.1.support.card = 4 := by
  have hp : σ.1 ^ 2 = 1 := congrArg Subtype.val hsq
  have hct := Equiv.Perm.cycleType_of_pow_prime_eq_one hp
  have hsupport : σ.1.support.card = 2 * σ.1.cycleType.card := by
    rw [← Equiv.Perm.sum_cycleType, hct]
    simp [Nat.mul_comm]
  have hsign : Equiv.Perm.sign σ.1 = 1 := σ.2
  have heven : Even (σ.1.cycleType.sum + σ.1.cycleType.card) := by
    apply (neg_one_pow_eq_one_iff_even (R := ℤˣ) (by norm_num)).mp
    rw [← Equiv.Perm.sign_of_cycleType]
    exact hsign
  have hsum : σ.1.cycleType.sum = 2 * σ.1.cycleType.card := by
    rw [hct]
    simp [Nat.mul_comm]
  have hpos : 0 < σ.1.support.card := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hne (Subtype.ext (Equiv.Perm.card_support_eq_zero.mp hzero))
  have hle : σ.1.support.card ≤ 6 := by
    simpa using Finset.card_le_univ σ.1.support
  rcases heven with ⟨k, hk⟩
  omega

/-- Every involution in an arbitrary double cover of A₆ lies in the kernel. -/
public theorem involution_mem_ker_of_double_cover
    {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q]
    (f : Covering Q (alternatingGroup (Fin 6)))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (x : Q) (hx : x ^ 2 = 1) : x ∈ f.toMonoidHom.ker := by
  by_contra hn
  have hne : f x ≠ 1 := hn
  have hsq : f x ^ 2 = 1 := by
    change f.toMonoidHom x ^ 2 = 1
    rw [← map_pow, hx, map_one]
  have hord : orderOf (f x) = 2 := orderOf_eq_prime hsq hne
  obtain ⟨e, he, _⟩ := theorem_5_2_3_a_2 1 f (schurAlternatingCovering 1)
    hcard (natCard_ker_schurAlternatingCovering 1)
  have hproj : schurAlternatingProjection 1 (e x) = f x := by
    exact DFunLike.congr_fun (congrArg Covering.toMonoidHom he) x
  have hlift := involutionLift_sq_of_support_card 1 1 (by decide) (by decide)
    (f x) hord (by simpa using support_card (f x) hsq hne) (e x) hproj
  have hesq : e x ^ 2 = 1 := by rw [← map_pow, hx, map_one]
  rw [hesq, pow_one] at hlift
  exact schurAlternatingCentral_ne_one 1 hlift.symm

/-- A quasisimple cover of A₆ with two-group center and a noncentral involution
has trivial center. -/
public theorem center_eq_bot_of_noncentral_involution
    {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q]
    (hc : IsPGroup 2 (center Q))
    (e : (Q ⧸ center Q) ≃* alternatingGroup (Fin 6))
    (hx : ∃ x : Q, orderOf x = 2 ∧ x ∉ center Q) : center Q = ⊥ := by
  have hdvd : Nat.card (center Q) ∣ 6 :=
    exceptional_alternating_center_card_dvd_six 6 e (Or.inl rfl)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hc
  have hcop : Nat.Coprime (Nat.card (center Q)) 3 := by
    rw [hk]
    exact (by norm_num : Nat.Coprime 2 3).pow_left k
  have htwo : Nat.card (center Q) ∣ 2 := hcop.dvd_mul_right.mp hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp htwo with hone | htwo
  · exact Subgroup.card_eq_one.mp hone
  · obtain ⟨f, hf⟩ := exists_alternatingCenterQuotientCovering 6 e
    obtain ⟨x, hxord, hxnc⟩ := hx
    apply False.elim
    apply hxnc
    rw [← hf]
    exact involution_mem_ker_of_double_cover f (by rwa [hf]) x
      (by simpa [hxord] using pow_orderOf_eq_one x)
end AlternatingSix.TwoCoverInvolutions
