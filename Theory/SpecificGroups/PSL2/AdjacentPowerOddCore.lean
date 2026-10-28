module

public import GorensteinWalter.Section4.PSL2ReflectedTorusCard
public import Theory.GroupAction.SylowFixedRankOneOddCore
public import Theory.SpecificGroups.PSL2.PrimeSylowFixers

/-!
# Involution centralizers for odd PSL₂ with an adjacent power of two

The actual reflected torus in an involution centralizer has the even one
of the two half-orders (q−1)/2 and (q+1)/2. If q>3 and one adjacent order
is a power of two, parity forces that torus to be a two-group. Its inverting
reflection also has order two, so the full centralizer is a two-group.
For prime fields, full Sylow pointwise innerness transfers the odd-core
conclusion to the original faithful automorphism overgroup.

Source: Huppert II.8.3–4, as used for the Fermat–Mersenne row of
Aschbacher–Smith E.6.19, printed p.252.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

/-- The full involution centralizer is a two-group, including q=5 and q=7. -/
theorem involutionCentralizer_isTwoGroup_of_adjacent_power
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (hlarge : 3 < Nat.card F)
    {k : ℕ} (hk : Nat.card F - 1 = 2 ^ k ∨ Nat.card F + 1 = 2 ^ k)
    (t : PSL(2,F)) (ht : orderOf t = 2) :
    IsPGroup 2 (centralizer ({t} : Set PSL(2,F))) := by
  have hk2 : 2 ≤ k := by
    by_contra! hh
    interval_cases k <;> norm_num at hk <;> omega
  have heven : Even (2 ^ (k - 1)) :=
    (even_two.pow_of_ne_zero (by omega))
  have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
    calc
      2 ^ k = 2 ^ ((k - 1) + 1) := congrArg (fun m => 2 ^ m) (by omega)
      _ = 2 * 2 ^ (k - 1) := by rw [pow_succ, Nat.mul_comm]
  obtain ⟨T,s,_,_,hs,_,hinv,hC,hTeven,hTcard⟩ := psl2_reflected_torus_card hF
    (show IsInvolution t from ⟨by intro h; simp [h] at ht,
      by simpa only [ht] using pow_orderOf_eq_one t⟩)
  have hcard : Nat.card T = 2 ^ (k - 1) := by
    obtain ⟨a,ha⟩ := hTeven
    obtain ⟨b,hb⟩ := heven
    rcases hk with hm | hp <;> rcases hTcard with htm | htp <;> omega
  have hT : IsPGroup 2 T := IsPGroup.of_card hcard
  have hS : IsPGroup 2 (zpowers s) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hs.2)
  have hsN : s ∈ normalizer (T : Set PSL(2,F)) := by
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      rw [hinv x hx]
      exact T.inv_mem hx
    · intro hx
      have hh := T.inv_mem hx
      have he : s * (s * x * s⁻¹) * s⁻¹ = x := by
        calc
          _ = (s * s) * x * (s * s)⁻¹ := by group
          _ = x := by rw [← pow_two, hs.2]; simp
      rwa [← hinv _ hx, he] at hh
  rw [hC]
  exact hT.to_sup_of_normal_left' hS (zpowers_le.mpr hsN)

/-- The faithful prime-field actor centralizer has trivial odd core. -/
theorem prime_adjacent_sylowFixedInvolution_oddCore_eq_bot
    {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hlarge : 3 < p)
    (hk : p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k)
    {H : Type*} [Group H] [Finite H] {φ : H →* MulAut PSL(2,ZMod p)} {E : Subgroup H}
    (d : Theory.GroupAction.SylowFixedInvolution φ E) :
    pPrimeCore 2 (centralizer (E : Set H)) = ⊥ := by
  apply d.oddCore_eq_bot_of_inner (psl2_center_eq_bot (ZMod p))
    (primeField_sylow_fixed_inner hp hlarge)
  intro S z hz _
  exact Theory.GroupAction.pPrimeCore_eq_bot_of_isPGroup
    (involutionCentralizer_isTwoGroup_of_adjacent_power
      ⟨p,1,Fact.out,hp,by omega,by simp⟩ (by simpa using hlarge)
      (by simpa using hk) z hz)

end Theory.PSL2
