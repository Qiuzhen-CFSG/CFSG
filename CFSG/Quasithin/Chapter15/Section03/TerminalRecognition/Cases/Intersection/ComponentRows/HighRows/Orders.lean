module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.ModelBounds
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup

/-!
# The two-part-five component sieve

A group in the ten-component B.5.6 list whose order has two-part 32
is SL₂(32) or the actual commutator subgroup of G₂(2). The odd
prime cube present in each F.6.18 degree-three model excludes SL₂(32).
This identifies components only; the full action remains necessary to
identify the offender and ambient groups.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6, printed p.105, and F.6.18(10)–(11), pp.309–310.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection.ComponentRows.HighRows
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

private theorem sl_card_mul (F : Type*) [Field F] [Finite F]
    (d : ℕ) [NeZero d] :
    Nat.card (Matrix.SpecialLinearGroup (Fin d) F) * (Nat.card F - 1) =
      ∏ i : Fin d, (Nat.card F ^ d - Nat.card F ^ (i : ℕ)) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (Matrix.SpecialLinearGroup (Fin d) F)),
    Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
  exact Atlas.ExceptionalSupport.card_psl_mul d

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
  rw [Nat.factorization_mul (by positivity)
    (Nat.ne_of_gt (binary_sub_one_pos hn hc)),
    Nat.factorization_mul (by positivity) (Nat.ne_of_gt (binary_sub_one_pos hn hb))]
  simp only [Finsupp.add_apply, binary_sub_one_two_part hn hb,
    binary_sub_one_two_part hn hc, add_zero]
  rw [← pow_mul, Nat.factorization_pow_self Nat.prime_two, Nat.mul_comm]

private theorem sl_three_card (F : Type*) [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (Matrix.SpecialLinearGroup (Fin 3) F)),
    Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
  exact Matrix.PSL3.LinearThree.card_projective_mul_scalar F

/-- The two-part 32 separates the two remaining actual group models.
No restriction on the ambient three-rank is used. -/
theorem model_twoPart_five {L : Type*} [Group L]
    (hpart : (Nat.card L).factorization 2 = 5) (h : QuasisimpleModel L) :
    (∃ F : BinaryField, F.degree = 5 ∧
      Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)) ∨
      Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  cases h with
  | linearTwo F e =>
    have hp : (Nat.card (Matrix.SpecialLinearGroup (Fin 2) F.Carrier)).factorization 2 =
        F.degree := by
      rw [Atlas.card_sl_two, F.card_eq,
        Nat.factorization_mul (by positivity)
          (Nat.ne_of_gt (binary_sub_one_pos F.degree_pos (by decide)))]
      simp only [Finsupp.add_apply, binary_sub_one_two_part F.degree_pos (by decide : 0 < 2),
        add_zero, Nat.factorization_pow_self Nat.prime_two]
    rw [Nat.card_congr e.toEquiv, hp] at hpart
    exact Or.inl ⟨F, hpart, ⟨e⟩⟩
  | linearThree F e =>
    rw [Nat.card_congr e.toEquiv, sl_three_card, F.card_eq,
      binary_order_two_part F.degree_pos (by decide) (by decide)] at hpart
    omega
  | symplecticFour F e =>
    rw [Nat.card_congr e.toEquiv, Theory.SpecificGroups.SymplecticFour.card_sp, F.card_eq,
      binary_order_two_part F.degree_pos (by decide) (by decide)] at hpart
    omega
  | g2 F e =>
    rw [Nat.card_congr e.toEquiv, Atlas.G2.card_Model, F.card_eq,
      binary_order_two_part F.degree_pos (by decide) (by decide)] at hpart
    omega
  | alternatingSix e =>
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at hpart
    norm_num only [Nat.card_fin, Nat.factorial] at hpart
    norm_num only [show Nat.factorization 360 2 = 3 by decide +kernel,
      show Nat.factorization 2520 2 = 3 by decide +kernel] at hpart
  | alternatingSeven e =>
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at hpart
    norm_num only [Nat.card_fin, Nat.factorial] at hpart
    norm_num only [show Nat.factorization 360 2 = 3 by decide +kernel,
      show Nat.factorization 2520 2 = 3 by decide +kernel] at hpart
  | tripleSix a b =>
    have hc : Nat.card L = 1080 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center L),
        Nat.card_congr a.toEquiv, Nat.card_congr b.toEquiv, nat_card_alternatingGroup]
      norm_num
    rw [hc, show Nat.factorization 1080 2 = 3 by decide +kernel] at hpart
    omega
  | g2DerivedTwo e => exact Or.inr ⟨e⟩
  | linearFourTwo e =>
    have hc := sl_card_mul (ZMod 2) 4
    norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
      Finset.prod_empty, mul_one] at hc
    rw [Nat.card_congr e.toEquiv, hc,
      show Nat.factorization 20160 2 = 6 by decide +kernel] at hpart
    omega
  | linearFiveTwo e =>
    have hc := sl_card_mul (ZMod 2) 5
    norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
      Finset.prod_empty, mul_one] at hc
    rw [Nat.card_congr e.toEquiv, hc,
      show Nat.factorization 9999360 2 = 10 by decide +kernel] at hpart
    omega

/-- The defining-prime cube excludes the remaining binary rank-one model.
The survivor is an actual equivalence with the derived octonion model. -/
theorem degreeThree_model_of_twoPart_five {L : Type*} [Group L]
    {p : ℕ} (hp : p.Prime) (hne : p ≠ 2)
    (hdegree : FSource.DegreeThree p L)
    (hpart : (Nat.card L).factorization 2 = 5) (h : QuasisimpleModel L) :
    Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  rcases model_twoPart_five hpart h with ⟨F, hF, ⟨e⟩⟩ | he
  · have hc := degreeThree_prime_cube hp hdegree
    rw [Nat.card_congr e.toEquiv] at hc
    exact (linearTwo_no_odd_prime_cube F (by omega) hp hne hc).elim
  · exact he

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection.ComponentRows.HighRows
