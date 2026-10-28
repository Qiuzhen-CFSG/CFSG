module
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Sylow two-subgroups with cyclic three-group residual

If the two-core is trivial, a Sylow two-subgroup acts faithfully by
conjugation on the two-residual: its centralizer there is normalized by
both the residual and the Sylow subgroup, hence is a normal two-subgroup.
For a cyclic three-group residual, the automorphism group has order
`2 * 3^n` (or one), so the Sylow two-subgroup has order at most two.

This is the finite-group obstruction used to eliminate the cyclic
three-group alternative in Aschbacher–Smith, 14.7.8, printed p.1045.
-/

public section
open Subgroup
open scoped IsMulCommutative

variable {A : Type*} [Group A] [Finite A]

private theorem residual_sylow_action_faithful (S : Sylow 2 A)
    (hcore : pCore 2 A = ⊥) :
    Function.Injective ((pResidual 2 A).normalizerMonoidHom.comp
      (inclusion (show (S : Subgroup A) ≤ normalizer (pResidual 2 A : Set A) by
        rw [normalizer_eq_top]; exact le_top))) := by
  let N := pResidual 2 A
  let D : Subgroup A := (S : Subgroup A) ⊓ centralizer (N : Set A)
  have hND : N ≤ normalizer (D : Set A) :=
    (le_centralizer_iff.mp (show D ≤ centralizer (N : Set A) from inf_le_right)).trans
      (centralizer_le_normalizer _)
  have hSD : (S : Subgroup A) ≤ normalizer (D : Set A) := by
    apply le_normalizer_iff.mpr
    intro s hs x hx
    refine ⟨(S : Subgroup A).mul_mem ((S : Subgroup A).mul_mem hs hx.1)
      ((S : Subgroup A).inv_mem hs), ?_⟩
    exact (inferInstance : (centralizer (N : Set A)).Normal).conj_mem x hx.2 s
  have htop : normalizer (D : Set A) = ⊤ := by
    apply top_unique
    rw [← pResidual_sup_sylow_eq_top S]
    exact sup_le hND hSD
  let : D.Normal := normalizer_eq_top_iff.mp htop
  have hD : D = ⊥ := by
    apply le_bot_iff.mp
    rw [← hcore]
    exact le_sSup ⟨inferInstance, S.isPGroup'.to_le inf_le_left⟩
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro s hs
  apply Subtype.ext
  apply mem_bot.mp
  rw [← hD]
  refine ⟨s.property, ?_⟩
  intro n hn
  have he := congrArg (fun f : MulAut N => (f ⟨n,hn⟩ : A)) hs
  change (s : A) * n * (s : A)⁻¹ = n at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- A group with trivial two-core and cyclic three-group two-residual
has Sylow two-subgroups of order at most two. -/
theorem Sylow.card_le_two_of_cyclic_three_residual (S : Sylow 2 A)
    (hcore : pCore 2 A = ⊥) [IsCyclic (pResidual 2 A)]
    (hthree : IsPGroup 3 (pResidual 2 A)) : Nat.card S ≤ 2 := by
  let f := (pResidual 2 A).normalizerMonoidHom.comp
      (inclusion (show (S : Subgroup A) ≤ normalizer (pResidual 2 A : Set A) by
        rw [normalizer_eq_top]; exact le_top))
  have hd : Nat.card S ∣ Nat.card (MulAut (pResidual 2 A)) :=
    card_dvd_of_injective f (residual_sylow_action_faithful S hcore)
  rw [IsCyclic.card_mulAut] at hd
  obtain ⟨n, hn⟩ := hthree.exists_card_eq
  rw [hn] at hd
  cases n with
  | zero =>
    have h1 : Nat.card S ∣ 1 := by simpa using hd
    exact (Nat.le_of_dvd (by decide : 0 < 1) h1).trans (by decide)
  | succ n =>
    rw [Nat.totient_prime_pow_succ (by decide : Nat.Prime 3)] at hd
    obtain ⟨k,hk⟩ := S.isPGroup'.exists_card_eq
    have hc : Nat.Coprime (Nat.card S) (3 ^ n) := by
      rw [hk]
      exact ((by decide : Nat.Coprime 2 3).pow_left k).pow_right n
    have htwo : Nat.card S ∣ 2 := hc.dvd_of_dvd_mul_left hd
    exact Nat.le_of_dvd (by decide) htwo
