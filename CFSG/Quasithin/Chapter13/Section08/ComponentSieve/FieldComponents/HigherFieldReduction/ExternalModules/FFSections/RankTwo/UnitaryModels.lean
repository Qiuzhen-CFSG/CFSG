module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.UnitaryProjection
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.QuasisimpleModels
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.UnitaryModels.RootInvariants
public import Theory.SpecificGroups.PSL2.RootTwoRank
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.SpecificGroups.G2Even.TwoRank
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup

/-!
# Excluding even-degree unitary groups from the complete B.4.2 list

For a genuine ternary Hermitian form over a field of order 2^(2*n), with
conjugation the 2^n power map, PSU₃ has two-rank at most n and order with two-part
2^(3*n). The explicit root Sylow and an actual change of Hermitian basis
supply these invariants on the original projective carrier.

For a binary field of degree d, the pairs (two-rank lower bound,
exponent of the two-part) for SL₂, SL₃, Sp₄ and G₂ are respectively
(d,d), (2*d,3*d), (3*d,4*d) and (3*d,6*d). None can equal the unitary
invariants. The fixed models are excluded by their orders: in the only
remaining SL₄(2) case, n=2, PSU₃(4) has order 62400 rather than 20160.
The triple A₆ cover is counted through its actual center and quotient;
the genuine derived G₂(2), of order 6048, is treated separately.

All ten constructors of `QuasisimpleModel` are retained. These cover every
actor in `IrreducibleActionCase`, including the symmetric and orthogonal
endpoints. The existing literal special-to-projective equivalence also
gives the exclusion for SU₃ when n is even. No simplicity or action premise
is added. Application of the source FF-module theorem remains with the caller.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2,
printed p.86, and the unitary exclusion in the proof of 13.8.20, printed
p.954. The matrix-field order is 2^(2*n), and the fixed-field order is 2^n.
-/

public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm
open OddPrimeSylow.NormalizedOuter.FormTransport
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo

private theorem sl_card_mul (F : Type*) [Field F] [Finite F]
    (d : ℕ) [NeZero d] :
    Nat.card (Matrix.SpecialLinearGroup (Fin d) F) * (Nat.card F - 1) =
      ∏ i : Fin d, (Nat.card F ^ d - Nat.card F ^ (i : ℕ)) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (Matrix.SpecialLinearGroup (Fin d) F)),
    Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
  exact Atlas.ExceptionalSupport.card_psl_mul d

private theorem unitary_card_four {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hcard : Nat.card E = (2 ^ 2) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ 2)) :
    Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) = 62400 := by
  have hf : Nat.card {x : E // J.conj x = x} = 2 ^ 2 :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2 (by decide) hcard hconj
  obtain ⟨e⟩ := exists_projectiveEquiv J (2 ^ 2) hcard hf
  rw [Nat.card_congr e.toEquiv]
  obtain ⟨_, _, _, _, _, _, _, _, hc, _⟩ :=
    BenderSuzuki.External.huppert_II_10_12 (standardForm J) (2 ^ 2) hcard hf rfl
  norm_num at hc
  exact hc

private theorem binary_sub_one_two_part {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    ((2 ^ n) ^ k - 1).factorization 2 = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  have he : ((2 ^ n) ^ k) % 2 = 0 := by
    simp [Nat.pow_mod, Nat.ne_of_gt hn, Nat.ne_of_gt hk]
  have hp : 0 < (2 ^ n) ^ k := by positivity
  omega

private theorem binary_sub_one_pos {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    0 < (2 ^ n) ^ k - 1 := by
  have h : 1 < (2 ^ n) ^ k :=
    one_lt_pow₀ (one_lt_pow₀ (by decide) (by omega)) (by omega)
  omega

private theorem binary_order_two_part {n a b c : ℕ}
    (hn : 0 < n) (hb : 0 < b) (hc : 0 < c) :
    ((2 ^ n) ^ a * ((2 ^ n) ^ b - 1) * ((2 ^ n) ^ c - 1)).factorization 2 = a * n := by
  have hbpos := binary_sub_one_pos hn hb
  rw [Nat.factorization_mul (by positivity) (by
    exact Nat.ne_of_gt (binary_sub_one_pos hn hc)),
    Nat.factorization_mul (by positivity) (Nat.ne_of_gt (binary_sub_one_pos hn hb))]
  simp only [Finsupp.add_apply, binary_sub_one_two_part hn hb,
    binary_sub_one_two_part hn hc, add_zero]
  rw [← pow_mul, Nat.factorization_pow_self Nat.prime_two, Nat.mul_comm]

private theorem sl_three_card (F : Type*) [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card
  have h := sl_card_mul F 3
  change Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) * (q - 1) = _ at h
  simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one] at h
  have h1 : q ^ 3 - q = q * (q ^ 2 - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
    ring
  have h2 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
  rw [h1, h2] at h
  apply Nat.eq_of_mul_eq_mul_right (show 0 < q - 1 by omega)
  rw [h]
  ring

private theorem sl_two_part (F : BinaryField) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) F.Carrier)).factorization 2 = F.degree := by
  rw [Atlas.card_sl_two, F.card_eq,
    Nat.factorization_mul (by positivity) (Nat.ne_of_gt (binary_sub_one_pos F.degree_pos (by decide)))]
  simp only [Finsupp.add_apply, binary_sub_one_two_part F.degree_pos (by decide : 0 < 2),
    add_zero, Nat.factorization_pow_self Nat.prime_two]

private theorem sl_three_part (F : BinaryField) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 3) F.Carrier)).factorization 2 = 3 * F.degree := by
  rw [sl_three_card, F.card_eq]
  exact binary_order_two_part F.degree_pos (by decide) (by decide)

private theorem sp_four_part (F : BinaryField) :
    (Nat.card (Matrix.symplecticGroup (Fin 2) F.Carrier)).factorization 2 = 4 * F.degree := by
  rw [Theory.SpecificGroups.SymplecticFour.card_sp F.Carrier, F.card_eq]
  exact binary_order_two_part F.degree_pos (by decide) (by decide)

private theorem g2_part (F : BinaryField) :
    (Nat.card (Atlas.G2.Model F.Carrier)).factorization 2 = 6 * F.degree := by
  rw [Atlas.G2.card_Model, F.card_eq]
  exact binary_order_two_part F.degree_pos (by decide) (by decide)

private theorem sl_two_rank_ge (F : BinaryField) :
    F.degree ≤ primeRank 2 (Matrix.SpecialLinearGroup (Fin 2) F.Carrier) := by
  let e := MulEquiv.ofBijective (BenderSuzuki.Converse.pi F.Carrier)
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩
  rw [primeRank_equiv 2 e]
  exact Theory.PSL2.root_two_rank_ge F.Carrier F.card_eq

private theorem sl_three_rank_ge (F : BinaryField) :
    2 * F.degree ≤ primeRank 2 (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) := by
  rw [← Matrix.PSL3Even.UnipotentGeometry.unipotent_two_rank F.Carrier F.card_eq]
  exact primeRank_le_of_injective 2 (Matrix.PSL3Even.UnipotentGeometry.specialLinear F.Carrier)
    (Matrix.PSL3Even.UnipotentGeometry.specialLinear_injective F.Carrier)

private theorem sl_four_card :
    Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  have h := sl_card_mul (ZMod 2) 4
  norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
    Finset.prod_empty, mul_one] at h
  exact h

private theorem sl_five_card :
    Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
  have h := sl_card_mul (ZMod 2) 5
  norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
    Finset.prod_empty, mul_one] at h
  exact h

private theorem derived_g2_card :
    Nat.card (commutator (Atlas.G2.Model (ZMod 2))) = 6048 := by
  rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
  exact Atlas.G2.BinaryException.card_H

private theorem not_model_of_invariants {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : 0 < n) (heven : Even n)
    (hr : primeRank 2 G ≤ n) (hp : (Nat.card G).factorization 2 = 3 * n)
    (hc : n = 2 → Nat.card G = 62400) : ¬ QuasisimpleModel G := by
  have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := heven; omega
  intro h
  cases h with
  | linearTwo F e =>
    have hlow := sl_two_rank_ge F
    rw [← primeRank_equiv 2 e] at hlow
    have hbound := hlow.trans hr
    rw [Nat.card_congr e.toEquiv, sl_two_part] at hp
    omega
  | linearThree F e =>
    have hlow := sl_three_rank_ge F
    rw [← primeRank_equiv 2 e] at hlow
    have hbound := hlow.trans hr
    rw [Nat.card_congr e.toEquiv, sl_three_part] at hp
    omega
  | symplecticFour F e =>
    have hlow := Theory.SpecificGroups.SymplecticFour.EvenTwoRank.three_mul_le_rank F.card_eq
    rw [← primeRank_equiv 2 e] at hlow
    have hbound := hlow.trans hr
    rw [Nat.card_congr e.toEquiv, sp_four_part] at hp
    omega
  | g2 F e =>
    have hlow := (Atlas.G2.EvenTwoRank.two_rank F.Carrier F.card_eq).ge
    rw [← primeRank_equiv 2 e] at hlow
    have hbound := hlow.trans hr
    rw [Nat.card_congr e.toEquiv, g2_part] at hp
    omega
  | alternatingSix e =>
    have hm : Nat.card G = 360 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hm, show Nat.factorization 360 2 = 3 by decide +kernel] at hp
    omega
  | alternatingSeven e =>
    have hm : Nat.card G = 2520 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hm, show Nat.factorization 2520 2 = 3 by decide +kernel] at hp
    omega
  | tripleSix ec eq =>
    have hm : Nat.card G = 1080 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center G),
        Nat.card_congr eq.toEquiv, Nat.card_congr ec.toEquiv,
        nat_card_alternatingGroup]
      norm_num [Nat.factorial, Nat.card_congr Multiplicative.toAdd]
    rw [hm, show Nat.factorization 1080 2 = 3 by decide +kernel] at hp
    omega
  | g2DerivedTwo e =>
    have hm : Nat.card G = 6048 := (Nat.card_congr e.toEquiv).trans derived_g2_card
    rw [hm, show Nat.factorization 6048 2 = 5 by decide +kernel] at hp
    omega
  | linearFourTwo e =>
    have hm : Nat.card G = 20160 := (Nat.card_congr e.toEquiv).trans sl_four_card
    rw [hm, show Nat.factorization 20160 2 = 6 by decide +kernel] at hp
    have hc' := hc (by omega)
    omega
  | linearFiveTwo e =>
    have hm : Nat.card G = 9999360 := (Nat.card_congr e.toEquiv).trans sl_five_card
    rw [hm, show Nat.factorization 9999360 2 = 10 by decide +kernel] at hp
    omega

/-- The actual even-degree projective unitary group is absent from every
concrete generalized-Fitting model in the complete B.4.2 action list. -/
theorem unitary_not_quasisimpleModel_even {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n) (heven : Even n)
    (hcard : Nat.card E = 2 ^ (2 * n))
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    ¬ QuasisimpleModel (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hcard' : Nat.card E = (2 ^ n) ^ 2 := by
    simpa only [← pow_mul, Nat.mul_comm n 2] using hcard
  have hi := UnitaryModels.projective_invariants J hn hcard' hconj
  exact not_model_of_invariants hn heven hi.1 hi.2 (by
      intro h
      subst n
      exact unitary_card_four J hcard' hconj)

/-- The literal special-to-projective equivalence gives the same exclusion
for the special unitary carrier at even degree. -/
theorem specialUnitary_not_quasisimpleModel_even {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n) (heven : Even n)
    (hcard : Nat.card E = 2 ^ (2 * n))
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    ¬ QuasisimpleModel J.specialSubgroup := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hcard' : Nat.card E = (2 ^ n) ^ 2 := by
    simpa only [← pow_mul, Nat.mul_comm n 2] using hcard
  let e := specialProjectiveEquivEven J heven hconj
  apply not_model_of_invariants hn heven
  · rw [primeRank_equiv 2 e]
    exact (UnitaryModels.projective_invariants J hn hcard' hconj).1
  · rw [Nat.card_congr e.toEquiv]
    exact (UnitaryModels.projective_invariants J hn hcard' hconj).2
  · intro h
    subst n
    rw [Nat.card_congr e.toEquiv]
    exact unitary_card_four J hcard' hconj

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo
