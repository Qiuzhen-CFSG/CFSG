module

public import Theory.SpecificGroups.SL2.DefiningRank
public import Theory.SpecificGroups.PSL3.DefiningRank
public import Theory.SpecificGroups.PSL4.DefiningRank
public import Theory.SpecificGroups.PSL4.OddSplitTorus
public import Theory.SpecificGroups.SymplecticFour.DefiningRank
public import Theory.NumberTheory.TwoPowerNeighbors
public import CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalRanks.UnitaryThree
public import CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalRanks.UnitaryFour
public import CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalRanks.NondefiningThree
public import CFSG.Quasithin.Defs

/-!
# Concrete classical rank obstructions in A.2.17

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), printed p.39.

The ordinary defining ranks of PSL₃(p^e) and PSU₃(p^e) are at least 2e. In particular
the source sentence bounding all odd prime ranks by two cannot be used
in defining characteristic. The ordinary rank bound forces e=1.
First-row and symmetric-shear embeddings exclude PSL₄, PSU₄ and PSp₄
from ordinary defining rank at most two. The nondefining three-rank bounds
for both dimension-three families include the noncommuting matrix-lift case;
these supply the rank input for the source's odd center of order three.

For PSL₄(p), odd torsion in the diagonal torus survives the scalar
quotient and centralizes a nonidentity involution. Local ranks at most
two therefore force p-1 to be a power of two, and primality yields the
Fermat restriction, including p=3. The norm-one unitary torus similarly
forces p+1 to be a power of two with prime exponent. Its witnesses and
defining-rank shears transport to arbitrary Hermitian forms through actual
projective equivalences.

The final corollaries supply the local bounds from quasithinness on a
specified isomorphic group, and the ordinary bounds from strong quasithinness
on an ambient group containing the model. The earlier family, central-cover
and defining-kernel reductions remain with the full A.2.17 assembly; no
family elimination or passage to arbitrary central quotients is assumed here.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterA.Section02
open Matrix
open scoped MatrixGroups
variable {F : Type*} [Field F] [Finite F]
  {p e : ℕ} [Fact p.Prime] [CharP F p]

theorem psl3_fieldExponent_eq_one (hc : Nat.card F = p ^ e) (he : 1 ≤ e)
    (hr : primeRank p PSL(3,F) ≤ 2) : e = 1 := by
  have := Matrix.PSL3.DefiningRank.two_mul_fieldExponent_le_primeRank F hc
  omega

theorem psl3_square_four_le_primeRank (hc : Nat.card F = p ^ 2) :
    4 ≤ primeRank p PSL(3,F) := by
  simpa using Matrix.PSL3.DefiningRank.two_mul_fieldExponent_le_primeRank F hc

theorem psl4_defining_primeRank_gt_two (hc : Nat.card F = p ^ e) (he : 1 ≤ e) :
    2 < primeRank p PSL(4,F) := by
  have := Matrix.PSL4.DefiningRank.three_mul_fieldExponent_le_primeRank F hc
  omega

theorem psp4_defining_primeRank_gt_two (hc : Nat.card F = p ^ e) (he : 1 ≤ e) :
    2 < primeRank p (symplecticGroup (Fin 2) F ⧸
      Subgroup.center (symplecticGroup (Fin 2) F)) := by
  have := Theory.SpecificGroups.SymplecticFour.DefiningRank.three_mul_fieldExponent_le_primeRank F hc
  omega

theorem psl4_no_odd_prime_dvd_pred (hp : p ≠ 2) (hc : Nat.card F = p)
    (hl : ∀ s : ℕ, s.Prime → s ≠ 2 → ∀ z : PSL(4,F), z ≠ 1 → z ^ 2 = 1 →
      primeRank s (Subgroup.centralizer ({z} : Set PSL(4,F))) ≤ 2) :
    ∀ s : ℕ, s.Prime → s ≠ 2 → ¬ s ∣ p - 1 := by
  intro s hs hs2 hd
  let : Fact s.Prime := ⟨hs⟩
  let : Fact (2 < p) := ⟨lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp)⟩
  have hodd : (-1 : F) ≠ 1 := CharP.neg_one_ne_one F p
  have hge := Matrix.PSL4.OddSplitTorus.three_le_primeRank_torus F hs2 (hc.symm ▸ hd)
  have hle := hl s hs hs2 (Matrix.PSL4.OddSplitTorus.splitInvolution F)
    (Matrix.PSL4.OddSplitTorus.splitInvolution_ne_one F hodd) (Matrix.PSL4.OddSplitTorus.splitInvolution_sq F)
  omega

theorem psl4_pred_eq_two_pow (hp : p ≠ 2) (hc : Nat.card F = p)
    (hl : ∀ s : ℕ, s.Prime → s ≠ 2 → ∀ z : PSL(4,F), z ≠ 1 → z ^ 2 = 1 →
      primeRank s (Subgroup.centralizer ({z} : Set PSL(4,F))) ≤ 2) :
    ∃ a : ℕ, p - 1 = 2 ^ a := by
  apply Nat.eq_two_pow_of_no_odd_prime_dvd
    (by have := (Fact.out : p.Prime).two_le; omega)
  exact psl4_no_odd_prime_dvd_pred hp hc hl

theorem psl4_fermat_parameter (hp : p ≠ 2) (hc : Nat.card F = p)
    (hl : ∀ s : ℕ, s.Prime → s ≠ 2 → ∀ z : PSL(4,F), z ≠ 1 → z ^ 2 = 1 →
      primeRank s (Subgroup.centralizer ({z} : Set PSL(4,F))) ≤ 2) :
    ∃ k : ℕ, p = 2 ^ (2 ^ k) + 1 :=
  Nat.fermat_of_no_odd_prime_dvd_pred (Fact.out : p.Prime) hp
    (psl4_no_odd_prime_dvd_pred hp hc hl)

end CFSG.Quasithin.ChapterA.Section02

namespace CFSG.Quasithin.ChapterA.Section02
open Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
variable {F G : Type*} [Field F] [Finite F] [Group G] [Finite G]
  {p e : ℕ} [Fact p.Prime]

private instance finite_projective (n : ℕ) : Finite (ProjGenLinGroup (Fin n) F) :=
  Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective

private theorem involution_rank_bound_of_quasithin (hqt : IsQuasithin G)
    (s : ℕ) (hs : s.Prime) (hs2 : s ≠ 2) (z : G) (hz : z ≠ 1) (hz2 : z ^ 2 = 1) :
    primeRank s (Subgroup.centralizer ({z} : Set G)) ≤ 2 :=
  Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hqt _
    (Theory.GroupTheory.isTwoLocal_involution_centralizer (orderOf_eq_prime hz2 hz))
    s hs (hs.odd_of_ne_two hs2)

/-- Quasithinness on a group identified with the actual PSL₄ forces the
Fermat parameter, by applying its two-local bounds to the torus involution. -/
theorem psl4_fermat_parameter_of_quasithin [CharP F p]
    (hp : p ≠ 2) (hc : Nat.card F = p) (iso : G ≃* PSL(4,F))
    (hqt : IsQuasithin G) : ∃ k : ℕ, p = 2 ^ (2 ^ k) + 1 :=
  psl4_fermat_parameter hp hc
    (involution_rank_bound_of_quasithin (Theory.GroupTheory.isQuasithin_of_equiv iso hqt))

/-- Quasithinness on a group identified with the actual PSU₄ forces the
Mersenne parameter, including p=3, for every permitted Hermitian form. -/
theorem psu4_mersenne_parameter_of_quasithin (J : HermitianForm 4 F)
    (hp : p ≠ 2) (hc : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    (iso : G ≃* ProjectiveSpecialUnitaryMatrixGroup J) (hqt : IsQuasithin G) :
    ∃ b : ℕ, b.Prime ∧ p + 1 = 2 ^ b :=
  psu4_mersenne_parameter J hp hc hconj
    (involution_rank_bound_of_quasithin (Theory.GroupTheory.isQuasithin_of_equiv iso hqt))

/-- The source strongly quasithin hypothesis forces prime field size for
an embedded PSL₃; the two root directions give the required ordinary rank. -/
theorem psl3_fieldExponent_eq_one_of_stronglyQuasithin [CharP F p]
    (hp : p ≠ 2) (hc : Nat.card F = p ^ e) (he : 1 ≤ e)
    (f : PSL(3,F) →* G) (hf : Function.Injective f) (hsq : IsStronglyQuasithin G) :
    e = 1 :=
  psl3_fieldExponent_eq_one hc he
    ((Theory.GroupTheory.primeRank_le_of_injective p f hf).trans
      (hsq p Fact.out ((Fact.out : p.Prime).odd_of_ne_two hp)))

/-- The source strongly quasithin hypothesis forces prime fixed-field size
for an embedded PSU₃ of the specified Hermitian form. -/
theorem psu3_fieldExponent_eq_one_of_stronglyQuasithin (J : HermitianForm 3 F)
    (hp : p ≠ 2) (hc : Nat.card F = (p ^ e) ^ 2) (he : 1 ≤ e)
    (hconj : ∀ x, J.conj x = x ^ (p ^ e))
    (f : ProjectiveSpecialUnitaryMatrixGroup J →* G) (hf : Function.Injective f)
    (hsq : IsStronglyQuasithin G) : e = 1 :=
  psu3_fieldExponent_eq_one J hp hc he hconj
    ((Theory.GroupTheory.primeRank_le_of_injective p f hf).trans
      (hsq p Fact.out ((Fact.out : p.Prime).odd_of_ne_two hp)))

/-- The three projective first-row directions exclude strong quasithinness
for every ambient group containing the actual PSL₄ model. -/
theorem psl4_not_stronglyQuasithin [CharP F p]
    (hp : p ≠ 2) (hc : Nat.card F = p ^ e) (he : 1 ≤ e)
    (f : PSL(4,F) →* G) (hf : Function.Injective f) : ¬ IsStronglyQuasithin G := by
  intro hsq
  have hgt := (psl4_defining_primeRank_gt_two hc he).trans_le
    (Theory.GroupTheory.primeRank_le_of_injective p f hf)
  exact (not_le_of_gt hgt) (hsq p Fact.out ((Fact.out : p.Prime).odd_of_ne_two hp))

/-- The three faithful Hermitian shear directions exclude strong
quasithinness for every ambient group containing the actual PSU₄ model. -/
theorem psu4_not_stronglyQuasithin (J : HermitianForm 4 F)
    (hp : p ≠ 2) (hc : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    (f : ProjectiveSpecialUnitaryMatrixGroup J →* G) (hf : Function.Injective f) :
    ¬ IsStronglyQuasithin G := by
  intro hsq
  have hgt := (psu4_defining_primeRank_gt_two J hc hconj).trans_le
    (Theory.GroupTheory.primeRank_le_of_injective p f hf)
  exact (not_le_of_gt hgt) (hsq p Fact.out ((Fact.out : p.Prime).odd_of_ne_two hp))

/-- The three symmetric-shear directions survive the literal center
quotient of Sp₄ and exclude strong quasithinness in any containing group. -/
theorem psp4_not_stronglyQuasithin [CharP F p]
    (hp : p ≠ 2) (hc : Nat.card F = p ^ e) (he : 1 ≤ e)
    (f : (symplecticGroup (Fin 2) F ⧸ Subgroup.center (symplecticGroup (Fin 2) F)) →* G)
    (hf : Function.Injective f) : ¬ IsStronglyQuasithin G := by
  intro hsq
  have hgt := (psp4_defining_primeRank_gt_two hc he).trans_le
    (Theory.GroupTheory.primeRank_le_of_injective p f hf)
  exact (not_le_of_gt hgt) (hsq p Fact.out ((Fact.out : p.Prime).odd_of_ne_two hp))

end CFSG.Quasithin.ChapterA.Section02
