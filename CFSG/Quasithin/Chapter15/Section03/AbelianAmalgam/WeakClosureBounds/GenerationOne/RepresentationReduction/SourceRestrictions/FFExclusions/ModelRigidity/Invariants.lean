module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity.Suzuki
public import Theory.SpecificGroups.PSL2.RootTwoRank
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.SpecificGroups.G2Even.TwoRank
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup

/-!
# Order and elementary rank of the actual FF component models

The two-part and two-rank together distinguish the four infinite families.
The projective linear Sylow calculation retains its odd scalar kernel.
The two small derived groups and all fixed alternating and binary linear
entries are counted on their actual carriers, rather than extrapolated from
the generic field formulas.

Source: Aschbacher--Smith, B.4.2--4, printed pp.86--87, and the rank table
on printed p.356, used at odd field exponent in 15.3.65, p.1152.
-/

public section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity

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
  rw [Nat.factorization_mul (by positivity) (Nat.ne_of_gt (binary_sub_one_pos hn hc)),
    Nat.factorization_mul (by positivity) (Nat.ne_of_gt (binary_sub_one_pos hn hb))]
  simp only [Finsupp.add_apply, binary_sub_one_two_part hn hb,
    binary_sub_one_two_part hn hc, add_zero]
  rw [← pow_mul, Nat.factorization_pow_self Nat.prime_two, Nat.mul_comm]

variable {F : Type*} [Field F] [Finite F] {n : ℕ}

/-- Binary PSL₂ has its actual SL₂ order: the scalar projection is injective. -/
theorem pslTwo_card (hF : Nat.card F = 2 ^ n) :
    Nat.card PSL(2,F) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let e := MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩
  rw [← Nat.card_congr e.toEquiv, Atlas.card_sl_two, hF]

/-- The root subgroup attains the full two-part of PSL₂. -/
theorem pslTwo_invariants (hn : 0 < n) (hF : Nat.card F = 2 ^ n) :
    primeRank 2 PSL(2,F) = n ∧ (Nat.card PSL(2,F)).factorization 2 = n := by
  have hp : (Nat.card PSL(2,F)).factorization 2 = n := by
    rw [pslTwo_card hF, Nat.factorization_mul (by positivity)
      (Nat.ne_of_gt (binary_sub_one_pos hn (by decide)))]
    simp only [Finsupp.add_apply, binary_sub_one_two_part hn (by decide : 0 < 2),
      add_zero, Nat.factorization_pow_self Nat.prime_two]
  refine ⟨le_antisymm ?_ (Theory.PSL2.root_two_rank_ge F hF), hp⟩
  let P : Sylow 2 PSL(2,F) := Classical.choice inferInstance
  rw [P.primeRank_eq]
  apply (primeRank_le_iff_elementary_card_le P).mpr
  intro A _
  have hc := P.card_eq_multiplicity
  rw [hp] at hc
  exact A.card_le_card_group.trans hc.le

/-- The actual projective root Sylow has order q³ and elementary rank 2n. -/
theorem pslThree_invariants (hn : 0 < n) (hF : Nat.card F = 2 ^ n) :
    primeRank 2 PSL(3,F) = 2 * n ∧ (Nat.card PSL(3,F)).factorization 2 = 3 * n := by
  refine ⟨Matrix.PSL3Even.two_rank F hn hF, ?_⟩
  have hs := (Matrix.PSL3.LinearThree.unipotentSylow F hn hF).card_eq_multiplicity
  have hc : Nat.card (Matrix.PSL3.LinearThree.unipotentSylow F hn hF) = 2 ^ (3 * n) := by
    change Nat.card (Matrix.PSL3.LinearThree.unipotent F) = _
    rw [Matrix.PSL3.LinearThree.card_unipotent, hF, ← pow_mul, Nat.mul_comm n 3]
  rw [hc] at hs
  exact (Nat.pow_right_injective (by decide : 1 < 2) hs).symm

/-- The actual center quotient of Sp₄ has the same order and rank in characteristic two. -/
theorem spFour_invariants (hn : 0 < n) (hF : Nat.card F = 2 ^ n) :
    primeRank 2 (Theory.SpecificGroups.SymplecticFour.Sp F ⧸
      center (Theory.SpecificGroups.SymplecticFour.Sp F)) = 3 * n ∧
    (Nat.card (Theory.SpecificGroups.SymplecticFour.Sp F ⧸
      center (Theory.SpecificGroups.SymplecticFour.Sp F))).factorization 2 = 4 * n := by
  refine ⟨Theory.SpecificGroups.SymplecticFour.EvenTwoRank.projective_rank hF hn, ?_⟩
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  rw [← Nat.card_congr (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).toEquiv,
    Theory.SpecificGroups.SymplecticFour.card_sp, hF]
  exact binary_order_two_part hn (by decide) (by decide)

/-- This is the full G₂ model, distinct from the derived binary endpoint. -/
theorem gTwo_invariants (hn : 0 < n) (hF : Nat.card F = 2 ^ n) :
    primeRank 2 (Atlas.G2.Model F) = 3 * n ∧
      (Nat.card (Atlas.G2.Model F)).factorization 2 = 6 * n := by
  refine ⟨Atlas.G2.EvenTwoRank.two_rank F hF, ?_⟩
  rw [Atlas.G2.card_Model, hF]
  exact binary_order_two_part hn (by decide) (by decide)

private theorem binary_psl_four_card : Nat.card PSL(4,ZMod 2) = 20160 := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 4
  norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
    Finset.prod_empty, mul_one] at h
  norm_num at h ⊢
  exact h

private theorem binary_psl_five_card : Nat.card PSL(5,ZMod 2) = 9999360 := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
  norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
    Finset.prod_empty, mul_one] at h
  norm_num at h ⊢
  exact h

/-- The finite exceptional orders are retained as an explicit disjunction. -/
@[expose] def SmallOrder (c : ℕ) : Prop :=
  c = 60 ∨ c = 360 ∨ c = 2520 ∨ c = 6048 ∨ c = 20160 ∨ c = 9999360

/-- Simultaneous invariants, derived from the genuine model equivalences.
The last disjunct retains every small derived, alternating and binary endpoint. -/
theorem ComponentModel.invariant_cases {S : Type*} [Group S]
    {family : Family} {q : ℕ} (h : ComponentModel S family q) :
    (∃ n, 0 < n ∧ family = .linearTwo ∧ q = 2 ^ n ∧
      primeRank 2 S = n ∧ (Nat.card S).factorization 2 = n) ∨
    (∃ n, 0 < n ∧ family = .linearThree ∧ q = 2 ^ n ∧
      primeRank 2 S = 2 * n ∧ (Nat.card S).factorization 2 = 3 * n) ∨
    (∃ n, 1 < n ∧ family = .symplecticFour ∧ q = 2 ^ n ∧
      primeRank 2 S = 3 * n ∧ (Nat.card S).factorization 2 = 4 * n) ∨
    (∃ n, 1 < n ∧ family = .gTwo ∧ q = 2 ^ n ∧
      primeRank 2 S = 3 * n ∧ (Nat.card S).factorization 2 = 6 * n) ∨
    SmallOrder (Nat.card S) := by
  cases h with
  | linearTwo F hn hF e =>
    let : Finite S := Finite.of_equiv _ e.toEquiv.symm
    exact Or.inl ⟨_, hn, rfl, rfl, (primeRank_equiv 2 e).trans (pslTwo_invariants hn hF).1,
      congrArg (fun c : ℕ => c.factorization 2) (Nat.card_congr e.toEquiv) |>.trans
        (pslTwo_invariants hn hF).2⟩
  | linearThree F hn hF e =>
    let : Finite S := Finite.of_equiv _ e.toEquiv.symm
    exact Or.inr (Or.inl ⟨_, hn, rfl, rfl,
      (primeRank_equiv 2 e).trans (pslThree_invariants hn hF).1,
      congrArg (fun c : ℕ => c.factorization 2) (Nat.card_congr e.toEquiv) |>.trans
        (pslThree_invariants hn hF).2⟩)
  | symplecticFour F hn hF e =>
    let : Finite S := Finite.of_equiv _ e.toEquiv.symm
    exact Or.inr (Or.inr (Or.inl ⟨_, hn, rfl, rfl,
      (primeRank_equiv 2 e).trans (spFour_invariants (by omega) hF).1,
      congrArg (fun c : ℕ => c.factorization 2) (Nat.card_congr e.toEquiv) |>.trans
        (spFour_invariants (by omega) hF).2⟩))
  | gTwo F hn hF e =>
    let : Finite S := Finite.of_equiv _ e.toEquiv.symm
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hn, rfl, rfl,
      (primeRank_equiv 2 e).trans (gTwo_invariants (by omega) hF).1,
      congrArg (fun c : ℕ => c.factorization 2) (Nat.card_congr e.toEquiv) |>.trans
        (gTwo_invariants (by omega) hF).2⟩)))
  | symplecticFourTwoDerived e =>
    apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
    rw [Nat.card_congr e.toEquiv,
      Nat.card_congr (derivedCongr
        (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := ZMod 2))).toEquiv,
      Nat.card_congr Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix.toEquiv,
      nat_card_alternatingGroup]
    norm_num [SmallOrder, Nat.factorial]
  | gTwoTwoDerived e =>
    apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
    rw [Nat.card_congr e.toEquiv, Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
      Atlas.G2.BinaryException.card_H]
    exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | alternatingFive e | alternatingSix e | alternatingSeven e =>
    apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [SmallOrder, Nat.factorial]
  | linearFourTwo e =>
    apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
    rw [Nat.card_congr e.toEquiv, binary_psl_four_card]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | linearFiveTwo e =>
    apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
    rw [Nat.card_congr e.toEquiv, binary_psl_five_card]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity
