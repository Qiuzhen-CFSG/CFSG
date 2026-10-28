module
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.Linear
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.Unitary
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.SymplecticG2
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.RankTwoCubic
public import CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalStructure.SmallIsomorphisms
public import CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalStructure.SmallIsomorphisms.OddFive
public import CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalStructure.SmallIsomorphisms.MinusFour
public import CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalStructure.SmallIsomorphisms.MinusSix

/-!
# Odd orthogonal source rank obstructions and small-model reductions

Faithful fundamental SL₂ maps and actual cubic pairs in their centralizers
exclude every odd orthogonal rank at least three, split rank at least four,
and nonsplit rank at least four. The nonsplit endpoint uses the explicit
cubic in the four-dimensional minus complement, including over F₃. The proof
only needs containment in the centralizer, which the block maps supply.

The field-preserving rank-one, odd-five, minus-four and minus-six comparisons
then complete Case I for the odd and nonsplit families. Split rank three is
retained for the separate general exterior-square comparison with PSL₄.

Source: Aschbacher–Smith, A.2.17, printed pp.38–39; GLS3 §2.7.
-/

open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups
open ClassicalOrthogonal.Fundamental
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
  {r e : ℕ} [Fact r.Prime] [CharP F r]

/-- The cubic in SL₂ bounds the full centralizer's three-rank, with no
residual identification required. -/
public theorem fundamental_centralizer_three_rank_le_one
    (hr : Odd r) (hcard : Nat.card F = r ^ e)
    (hqt : IsQuasithin G) (j : SL(2,F) →* G) (hj : Function.Injective j) :
    primeRank 3 (centralizer (j.range : Set G)) ≤ 1 := by
  have hr2 : r ≠ 2 := fun he => by subst r; exact (by decide : ¬ Odd 2) hr
  have hd : 3 ∣ Nat.card SL(2,F) := by
    rw [← cubicSL_order (F := F)]
    exact orderOf_dvd_natCard _
  exact (RootCoverTransfer.sl2_complementary_primeRank_le_one hr2 (by decide : Odd 3)
    (by rw [hcard]; exact hr.pow) j hj (centralizer (j.range : Set G)) le_rfl hd
    (fun z hz hz2 => Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hqt _
      (Theory.GroupTheory.isTwoLocal_involution_centralizer (orderOf_eq_prime hz2 hz))
      3 (by decide) (by decide)) (MonoidHom.id _) Function.surjective_id).1

private theorem nine_rank {X : Type*} [Group X] [Finite X]
    (E : Subgroup X) (hE : IsElementaryAbelian 3 E) (hc : Nat.card E = 9) :
    2 ≤ primeRank 3 X := by
  let := hE
  let : CommGroup E := IsMulCommutative.instCommGroup
  exact primeRank_ge_of_elementary_embedding
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 E)) hc E.subtype E.subtype_injective

/-- Every odd orthogonal model of natural dimension at least seven is
excluded by the actual elementary nine-subgroup of its fundamental centralizer. -/
public theorem orthogonal_odd_not_quasithin {n : ℕ} (hn : 3 ≤ n)
    (hr : Odd r) (hcard : Nat.card F = r^e) :
    ¬ IsQuasithin (ClassicalOrthogonal.POmegaOdd n F) := by
  intro hqt
  open SplitOddCentralizers in
    have hu := fundamental_centralizer_three_rank_le_one hr hcard hqt
      (oddLeft (F := F) n (by omega)) (oddLeft_injective hn)
  obtain ⟨E, hE, hc⟩ := SplitOddCentralizers.odd_residual_contains_nine (F := F) r hn
  have hl := nine_rank E hE hc
  have hi := primeRank_le_of_injective 3
    (SplitOddCentralizers.centralizerResidual r (SplitOddCentralizers.oddFundamental (F := F) n (by omega))).subtype
    Subtype.val_injective
  change primeRank 3 _ ≤ primeRank 3 (centralizer
    ((SplitOddCentralizers.oddLeft (F := F) n (by omega)).range : Set (ClassicalOrthogonal.POmegaOdd n F))) at hi
  omega

/-- Every split orthogonal model of natural dimension at least eight is
excluded by the actual cubic pair in its fundamental centralizer. -/
public theorem orthogonal_plus_not_quasithin {n : ℕ} (hn : 4 ≤ n)
    (hr : Odd r) (hcard : Nat.card F = r^e) :
    ¬ IsQuasithin (ClassicalOrthogonal.POmegaPlus n F) := by
  intro hqt
  have hu := fundamental_centralizer_three_rank_le_one hr hcard hqt
    (SplitOddCentralizers.plusLeft (F := F) n (by omega))
    (SplitOddCentralizers.plusLeft_injective hn)
  obtain ⟨E, hE, hc⟩ := SplitOddCentralizers.plus_residual_contains_nine (F := F) r hn
  have hl := nine_rank E hE hc
  have hi := primeRank_le_of_injective 3
    (SplitOddCentralizers.centralizerResidual r (SplitOddCentralizers.plusFundamental (F := F) n (by omega))).subtype
    Subtype.val_injective
  change primeRank 3 _ ≤ primeRank 3 (centralizer
    ((SplitOddCentralizers.plusLeft (F := F) n (by omega)).range : Set (ClassicalOrthogonal.POmegaPlus n F))) at hi
  omega

private theorem minus_block_obstruction (s : ℕ) (hq : 2 < Nat.card F)
    (hr : Odd r) (hcard : Nat.card F = r^e)
    (hE : ∃ E : Subgroup (ClassicalGroup.POmegaMinus (s+3) F),
      E ≤ (MinusCentralizer.projectiveBlockHom s hq).range ∧
      IsElementaryAbelian 3 E ∧ Nat.card E = 9) :
    ¬ IsQuasithin (ClassicalGroup.POmegaMinus (s+3) F) := by
  intro hqt
  have hu := fundamental_centralizer_three_rank_le_one hr hcard hqt
    (MinusCentralizer.fundamentalHom s hq) (MinusCentralizer.fundamentalHom_injective s hq)
  obtain ⟨E, hle, hE, hc⟩ := hE
  let := hE
  have hC := hle.trans (MinusCentralizer.projectiveBlockHom_le_centralizer s hq)
  let f := Subgroup.inclusion hC
  have hf : Function.Injective f := Subgroup.inclusion_injective hC
  have hEbound := (primeRank_le_of_injective 3 f hf).trans hu
  have hlow : 2 ≤ primeRank 3 E := by
    let : CommGroup E := IsMulCommutative.instCommGroup
    exact primeRank_ge_of_elementary_embedding
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 3 E)) hc (MonoidHom.id E) Function.injective_id
  omega

/-- Every nonsplit orthogonal model of natural dimension at least eight is
excluded, including the smallest complementary four-space over F₃. -/
public theorem orthogonal_minus_not_quasithin {n : ℕ} (hn : 4 ≤ n)
    (hr : Odd r) (hcard : Nat.card F = r^e) :
    ¬ IsQuasithin (ClassicalGroup.POmegaMinus n F) := by
  have hq : 2 < Nat.card F := MinusCentralizer.field_card_gt_two Fact.out hr
  by_cases h4 : n = 4
  · subst n
    exact minus_block_obstruction 1 hq hr hcard
      (MinusCentralizer.smallestBlock_contains_nine hr hq)
  obtain ⟨s, rfl⟩ : ∃ s, n = s+5 := ⟨n-5, by omega⟩
  exact minus_block_obstruction (s+2) hq hr hcard
    (MinusCentralizer.higherBlock_contains_nine s hq)

/-- The full odd orthogonal Case I branch, including the genuine rank-one and
rank-two comparisons, supplies the exact B and C conclusions. -/
public theorem orthogonal_odd_caseI {n : ℕ} (hn : 1 ≤ n)
    (hr : Odd r) (he : 1 ≤ e) (hqt : IsQuasithin G)
    (model : ClassicalGroup.IsPOmegaOdd G n (r^e)) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  by_cases h1 : n = 1
  · subst n
    exact linear_caseI (by decide) hr he hqt
      (SmallIsomorphisms.isPSL_two_of_isPOmegaOdd_one model)
  by_cases h2 : n = 2
  · subst n
    exact symplectic_caseI (by decide) hr he hqt
      (SmallIsomorphisms.isPSp_two_of_isPOmegaOdd_two hr.pow model)
  obtain ⟨F, hF, hfin, hc, ⟨iso⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  exact (orthogonal_odd_not_quasithin (by omega) hr hc
    (isQuasithin_of_equiv iso hqt)).elim

/-- The full nonsplit orthogonal Case I branch, with ambient simplicity as in
the source, uses the actual minus-four and minus-six field-preserving models. -/
public theorem orthogonal_minus_caseI [IsSimpleGroup G] {n : ℕ} (hn : 2 ≤ n)
    (hr : Odd r) (he : 1 ≤ e) (hqt : IsQuasithin G)
    (model : ClassicalGroup.IsPOmegaMinus G n (r^e)) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  by_cases h2 : n = 2
  · subst n
    have hm : ClassicalGroup.IsPSL G 2 (r^(e*2)) := by
      simpa only [pow_mul] using
        SmallIsomorphisms.isPSL_two_sq_of_isPOmegaMinus_two model
    exact linear_caseI (by decide) hr (by omega) hqt hm
  by_cases h3 : n = 3
  · subst n
    exact unitary_caseI (by decide) hr he hqt
      (SmallIsomorphisms.isPSU_four_of_isPOmegaMinus_three hr.pow model)
  obtain ⟨F, hF, hfin, hc, ⟨iso⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  exact (orthogonal_minus_not_quasithin (by omega) hr hc
    (isQuasithin_of_equiv iso hqt)).elim

/-- The higher split orthogonal Case I source alternative is impossible. -/
public theorem orthogonal_plus_caseI_false {n : ℕ} (hn : 4 ≤ n)
    (hr : Odd r) (hqt : IsQuasithin G)
    (model : ClassicalGroup.IsPOmegaPlus G n (r^e)) : False := by
  obtain ⟨F, hF, hfin, hc, ⟨iso⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  exact orthogonal_plus_not_quasithin hn hr hc (isQuasithin_of_equiv iso hqt)
end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
