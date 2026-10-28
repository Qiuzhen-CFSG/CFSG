module

public import Theory.SpecificGroups.PSL2.OddPerfectCore
public import Theory.SpecificGroups.PSL2.TwoPerfectInvolutionCentralizer
public import Theory.GroupTheory.SimpleFiveSmallSectionAction

/-!
# Quintic two-perfect subgroups of odd-field PSL₂

A two-perfect subgroup whose two-core quotient has order five has trivial
two-core, and consequently has order five. Indeed a nontrivial two-core
contains a normal elementary abelian group of order at most four. The
quintic section acts trivially on this group, placing the original subgroup
in an involution centralizer. Its two-perfect image there has odd order.

This retains the literal odd-field PSL₂ subgroup used in the last paragraph
of Aschbacher--Smith 6.1.4, printed p.666.
-/

public section
open Subgroup Theory.GroupTheory GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

/-- The quintic two-perfect subgroup in an odd-field PSL₂ is a literal group
of order five: its two-core does not survive inside the simple model. -/
theorem odd_twoPerfect_quintic_subgroup
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (X : Subgroup PSL(2,F))
    (hX : IsPPerfect 2 X) (hfive : Nat.card (X ⧸ pCore 2 X) = 5) :
    pCore 2 X = ⊥ ∧ Nat.card X = 5 := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let : IsSimpleGroup (X ⧸ pCore 2 X) := isSimpleGroup_of_prime_card hfive
  have hcore : pCore 2 X = ⊥ := by
    by_contra hne
    have hr : primeRank 2 PSL(2,F) ≤ 2 := by
      let S : Sylow 2 PSL(2,F) := Classical.choice inferInstance
      obtain ⟨n, _, ⟨e⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hF S
      rw [S.primeRank_eq, primeRank_equiv 2 e]
      exact dihedral_rank_le_two n
    have hrX : primeRank 2 X ≤ 2 :=
      (primeRank_le_of_injective 2 X.subtype X.subtype_injective).trans hr
    obtain ⟨E, hEn, hEne, _, hE, _⟩ := exists_minimal_normal_le_pCore hne
    let : E.Normal := hEn
    let : IsElementaryAbelian 2 E := hE
    have hEcard : Nat.card E ≤ 4 :=
      (primeRank_le_iff_elementary_card_le X).mp hrX E hE
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
    have hnle : n ≤ 3 := by
      by_contra hnle
      have hh : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      rw [← hn] at hh
      omega
    have hEdvd : Nat.card E ∣ 8 := by
      rw [hn]
      exact pow_dvd_pow 2 hnle
    let a : X →* MulAut E := MulAut.conjNormal
    have ha : a = 1 := hom_eq_one_of_twoPerfect_simple_five_section hX
      (by rw [hfive]) a (five_coprime_card_mulAut_of_card_dvd_eight hEdvd)
    let : Nontrivial E := (nontrivial_iff_ne_bot E).mpr hEne
    obtain ⟨u, hu, hu1⟩ := E.exists_ne_one_of_nontrivial
    have hu2 : u ^ 2 = 1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) ⟨u, hu⟩)
    have huo : orderOf u = 2 := orderOf_eq_prime_iff.mpr ⟨hu2, hu1⟩
    have ht : orderOf (u : PSL(2,F)) = 2 := by
      exact orderOf_eq_prime_iff.mpr ⟨congrArg Subtype.val hu2,
        fun he => hu1 (Subtype.ext he)⟩
    have hc (x : X) : Commute (X.subtype x) (u : PSL(2,F)) := by
      have he := congrArg (fun b : MulAut E => (b ⟨u, hu⟩ : X))
        (DFunLike.congr_fun ha x)
      change x * u * x⁻¹ = u at he
      exact congrArg Subtype.val (mul_inv_eq_iff_eq_mul.mp he)
    have ho := odd_image_of_twoPerfect_centralizing_involution hF u ht hX X.subtype hc
    rw [X.range_subtype] at ho
    have hd : 2 ∣ Nat.card X := by
      simpa only [huo] using (_root_.orderOf_dvd_natCard u)
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hd)
  refine ⟨hcore, ?_⟩
  have hc := (pCore 2 X).card_mul_index
  change Nat.card (pCore 2 X) * Nat.card (X ⧸ pCore 2 X) = Nat.card X at hc
  have hcardcore : Nat.card (pCore 2 X) = 1 := by rw [hcore]; simp
  rw [hcardcore, one_mul, hfive] at hc
  exact hc.symm

end Theory.PSL2
