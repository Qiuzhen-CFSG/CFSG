module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Embeddings
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismOrder
public import Theory.SpecificGroups.PSL2.RootTwoRank
public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank
public import GorensteinWalter.PSL2Cardinality
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Binary PSL₂ parameters and the faithful Sylow budget

The two-adic valuation of |PSL₂(2ⁿ)| is n. Comparing two-ranks with an
odd-prime PSL₂ model forces n=2, and the order formulas then force p=5.
A faithful two-group of automorphisms has order dividing 2ⁿn, after removing
the odd factor from the actual semilinear automorphism order.

These comparisons apply to the original block image and full Sylow in
Aschbacher–Smith C.5.13, printed pp.162–163, when inspecting A.3.12.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
variable {B : Type*} [Group B] [Finite B] {n : ℕ}

omit [Finite B] in
theorem binary_card (hB : ClassicalGroup.IsPSL B 2 (2^n)) :
    Nat.card B = 2^n * ((2^n)^2 - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hB
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  rw [Nat.card_congr e.toEquiv,
    ← Nat.card_congr (BenderSuzuki.ZD.Linear.sl2QuotientEquiv F).toEquiv,
    BenderSuzuki.External.huppert614_card_specialLinearGroup, hF]

omit [Finite B] in
theorem binary_two_valuation (hn : 0 < n)
    (hB : ClassicalGroup.IsPSL B 2 (2^n)) : (Nat.card B).factorization 2 = n := by
  have hq : 1 < 2^n := Nat.one_lt_pow (by omega) (by decide)
  have ho : Odd ((2^n)^2-1) := by
    apply Nat.Even.sub_odd (by nlinarith)
    · exact (even_two.pow_of_ne_zero (by omega)).pow_of_ne_zero (by decide)
    · exact odd_one
  have hs : 1 < (2^n)^2 := by nlinarith
  rw [binary_card hB, Nat.factorization_mul (by positivity) (by omega),
    Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by simpa only [← even_iff_two_dvd] using Nat.not_even_iff_odd.mpr ho)]
  omega

omit [Finite B] in
theorem binary_parameter_of_alternating_five (hn : 0 < n)
    (hB : ClassicalGroup.IsPSL B 2 (2^n)) (ha : CFSG.Quasithin.Chapter1.Section02.LocalModels.IsAlternating B 5) : n = 2 := by
  obtain ⟨e⟩ := ha
  have hc : Nat.card B = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hv := binary_two_valuation hn hB
  have he : Nat.factorization 60 2 = 2 := by
    rw [show 60 = 2^2 * 15 by decide, Nat.factorization_mul (by decide) (by decide),
      Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 15)]
  rw [hc, he] at hv
  exact hv.symm

theorem binary_rank_lower (hB : ClassicalGroup.IsPSL B 2 (2^n)) : n ≤ primeRank 2 B := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hB
  rw [primeRank_equiv 2 e]
  exact Theory.PSL2.root_two_rank_ge F hF

theorem binary_odd_prime_parameters (hn : 1 < n)
    (hB : ClassicalGroup.IsPSL B 2 (2^n)) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hlarge : 3 < p)
    (hm : ClassicalGroup.IsPSL B 2 p) : n = 2 ∧ p = 5 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, hp, ho, by omega, by simpa using hF⟩
  have hr : primeRank 2 B ≤ 2 := by
    rw [primeRank_equiv 2 e]
    let P : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Classical.choice inferInstance
    obtain ⟨k, _, ⟨eP⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hodd P
    rw [P.primeRank_eq, primeRank_equiv 2 eP]
    exact dihedral_rank_le_two k
  have hn2 : n = 2 := by have := binary_rank_lower hB; omega
  have hc := binary_card hB
  rw [hn2] at hc
  norm_num at hc
  have hc' : p * (p^2-1) / 2 = 60 := by
    rw [← hF, ← GorensteinWalter.psl2_card_formula F hodd,
      ← Nat.card_congr e.toEquiv]
    exact hc
  have hupper : p * (p^2-1) < 122 := by omega
  have hp5 : p ≤ 5 := by
    by_contra hh
    have hh : 6 ≤ p := by omega
    have hs : 35 ≤ p^2-1 := by
      have : 36 ≤ p^2 := by nlinarith
      omega
    nlinarith
  have hpne4 : p ≠ 4 := by intro he; rw [he] at hp; norm_num at hp
  exact ⟨hn2, by omega⟩
omit [Finite B] in
/-- Any faithful two-group of automorphisms satisfies the sharp divisibility
needed for the actual full-Sylow row comparison. -/
theorem binary_actor_card_dvd (hn : 0 < n)
    (hB : ClassicalGroup.IsPSL B 2 (2^n))
    {A : Type*} [Group A] [Finite A] (hA : IsPGroup 2 A)
    (f : A →* MulAut B) (hf : Function.Injective f) :
    Nat.card A ∣ 2^n * n := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hB
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let g := (MulAut.congr e).toMonoidHom.comp f
  have hg : Function.Injective g := (MulAut.congr e).injective.comp hf
  have hd : Nat.card A ∣ (2^n*n) * ((2^n)^2-1) := by
    simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (card_dvd_of_injective g hg).trans
        (Theory.PSL2.BinaryAutomorphismOrder.aut_card_dvd hF)
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  have ho : Odd ((2^n)^2-1) := by
    apply Nat.Even.sub_odd (by have := Nat.one_le_pow (n*2) 2 (by omega); simpa [pow_mul] using this)
    · rw [← pow_mul]
      exact (Nat.even_pow' (by omega)).2 even_two
    · exact odd_one
  have hc : Nat.Coprime (Nat.card A) ((2^n)^2-1) := by
    rw [hk]
    exact (Nat.coprime_two_left.mpr ho).pow_left k
  exact hc.dvd_of_dvd_mul_right hd

/-- The literal conjugation action of the full source Sylow supplies the
faithful actor used above. -/
theorem binary_normalizer_card_dvd {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (B : Subgroup G) (hn : 0 < n)
    (hB : ClassicalGroup.IsPSL B 2 (2^n))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hfaith : (T : Subgroup G) ⊓ centralizer (B : Set G) = ⊥) :
    Nat.card T ∣ 2^n*n := by
  let f := B.normalizerMonoidHom.comp (inclusion hTB)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro a ha
    apply Subtype.ext
    apply mem_bot.mp
    rw [← hfaith]
    refine ⟨a.property, ?_⟩
    change inclusion hTB a ∈ B.normalizerMonoidHom.ker at ha
    rw [normalizerMonoidHom_ker] at ha
    exact ha
  exact binary_actor_card_dvd hn hB T.isPGroup' f hf

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
