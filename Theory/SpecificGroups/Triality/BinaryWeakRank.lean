module

public import Theory.GroupTheory.TwoRankFourthPower
public import Theory.SpecificGroups.Triality.BinaryRootWord
public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.RootElements
public import Theory.SpecificGroups.Triality.BinaryCenter
public import Theory.SpecificGroups.Triality.OuterOddSubgroups
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.OddExponent

/-!
# A sufficient two-rank bound at the binary triality endpoint

The actual long-root/short-root product has nontrivial fourth power, by its
literal elementary lift and the faithful central quotient. The Sylow group
has order 2^12, so its elementary subgroups have order at most 2^10.
At q=2 the coefficient automorphism group has order three. Genuine
inner–coefficient coverage therefore makes the outer quotient odd and gives
the same upper bound for the automorphism group. Coverage remains explicit.
Source: the sufficient bounds for Aschbacher–Smith G.9.3, printed p.356.
-/

@[expose] public section
namespace Triality.Standard.BinaryWeakRank
open Subgroup Theory.GroupTheory

open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.EvenInvolutionGeometry

/-- The concrete endpoint witness already has certified Sylow membership. -/
noncomputable def endpointRootProduct : BinaryCarrier 1 Nat.zero_lt_one :=
  longRoot 1 Nat.zero_lt_one 1 * shortRoot 1 Nat.zero_lt_one 1

theorem endpointRootProduct_mem :
    endpointRootProduct ∈ unipotent (binaryParameters 1 Nat.zero_lt_one) :=
  Subgroup.mul_mem _ (longRoot_mem_unipotent 1 Nat.zero_lt_one 1)
    (shortRoot_mem_unipotent 1 Nat.zero_lt_one 1)

/-- This is the exact weak intrinsic-rank consumer of the missing matrix certificate. -/
private theorem endpoint_twoRank_le_ten_of_fourth_ne
    (hx : endpointRootProduct ^ 4 ≠ 1) :
    primeRank 2 (BinaryCarrier 1 Nat.zero_lt_one) ≤ 10 := by
  rw [(unipotentSylow (binaryParameters 1 Nat.zero_lt_one) rfl).primeRank_eq]
  change primeRank 2 (unipotent (binaryParameters 1 Nat.zero_lt_one)) ≤ 10
  apply twoRank_le_of_card_pow_and_fourth_ne 10
    (by simpa using card_unipotent_binary (binaryParameters 1 Nat.zero_lt_one) rfl)
    (⟨endpointRootProduct, endpointRootProduct_mem⟩ :
      unipotent (binaryParameters 1 Nat.zero_lt_one))
  intro h
  exact hx (congrArg Subtype.val h)

/-- Exact automorphism-rank target sufficient for the new 24-dimensional endpoint bound. -/
private theorem endpoint_automorphism_twoRank_le_ten
    (hx : endpointRootProduct ^ 4 ≠ 1)
    (hodd : ¬ 2 ∣ Nat.card (MulAut.Outer (BinaryCarrier 1 Nat.zero_lt_one))) :
    primeRank 2 (MulAut (BinaryCarrier 1 Nat.zero_lt_one)) ≤ 10 :=
  (automorphism_twoRank_le_of_odd_outer
    (binaryCarrier_center_eq_bot 1 Nat.zero_lt_one) hodd).trans
    (endpoint_twoRank_le_ten_of_fourth_ne hx)

/-- At the endpoint, genuine inner-coefficient coverage makes the outer order odd. -/
theorem endpoint_outer_odd_of_coverage
    (hcoverage : ∀ a : MulAut (BinaryCarrier 1 Nat.zero_lt_one),
      ∃ g : BinaryCarrier 1 Nat.zero_lt_one,
      ∃ e : OuterOdd.CoefficientAut (binaryParameters 1 Nat.zero_lt_one),
        a = MulAut.conj g * OuterOdd.coefficientAction (binaryParameters 1 Nat.zero_lt_one) e) :
    ¬ 2 ∣ Nat.card (MulAut.Outer (BinaryCarrier 1 Nat.zero_lt_one)) := by
  have hs := (OuterOdd.outerCoefficientAction_surjective_iff
    (binaryParameters 1 Nat.zero_lt_one)).mpr hcoverage
  have hd := Subgroup.card_dvd_of_surjective
    (OuterOdd.outerCoefficientAction (binaryParameters 1 Nat.zero_lt_one)) hs
  rw [coefficientAut_card] at hd
  intro he
  have := he.trans hd
  norm_num at this

/-- The sole remaining model premise besides the matrix witness is the existing coverage target. -/
private theorem endpoint_automorphism_twoRank_le_ten_of_coverage
    (hx : endpointRootProduct ^ 4 ≠ 1)
    (hcoverage : ∀ a : MulAut (BinaryCarrier 1 Nat.zero_lt_one),
      ∃ g : BinaryCarrier 1 Nat.zero_lt_one,
      ∃ e : OuterOdd.CoefficientAut (binaryParameters 1 Nat.zero_lt_one),
        a = MulAut.conj g * OuterOdd.coefficientAction (binaryParameters 1 Nat.zero_lt_one) e) :
    primeRank 2 (MulAut (BinaryCarrier 1 Nat.zero_lt_one)) ≤ 10 :=
  endpoint_automorphism_twoRank_le_ten hx (endpoint_outer_odd_of_coverage hcoverage)

private noncomputable def rootElementary (n : ℕ) (hn : 0 < n) : ElementaryGroup (binaryParameters n hn) :=
  sl2ElementaryLift (binaryParameters n hn) rfl (longRankOneFixed n hn)
      (Matrix.SpecialLinearGroup.upperUnipotentHom _ (Multiplicative.ofAdd 1)) *
    sl2ElementaryLift (binaryParameters n hn) rfl (shortRankOneFixed n hn)
      (Matrix.SpecialLinearGroup.upperUnipotentHom _ (Multiplicative.ofAdd 1))

private lemma rootElementary_toCarrier (n : ℕ) (hn : 0 < n) :
    toCarrier (binaryParameters n hn) (rootElementary n hn) = (longRoot n hn 1 * shortRoot n hn 1) := by
  simp only [rootElementary, map_mul, longRoot, shortRoot, longRootHom,
    shortRootHom, MonoidHom.comp_apply]

private lemma rootElementary_split (n : ℕ) (hn : 0 < n) :
    elementaryInclusion (binaryParameters n hn) (rootElementary n hn) =
      positiveRoot (binaryParameters n hn) 1 1 *
        (positiveRoot (binaryParameters n hn) 0 1 *
          positiveRoot (binaryParameters n hn) 2 1 *
          positiveRoot (binaryParameters n hn) 3 1) := by
  simp only [rootElementary, elementaryInclusion, MonoidHom.comp_apply,
    map_mul, Subgroup.subtype_apply]
  change (longRankOneFixed n hn
      (Matrix.SpecialLinearGroup.upperUnipotentHom (GaloisField 2 n)
        (Multiplicative.ofAdd 1)) : SplitGroup (binaryParameters n hn)) *
    (shortRankOneFixed n hn
      (Matrix.SpecialLinearGroup.upperUnipotentHom (ExtensionField (binaryParameters n hn))
        (Multiplicative.ofAdd 1)) : SplitGroup (binaryParameters n hn)) = _
  have hbase : baseFieldEmbedding (binaryParameters n hn) (1 : GaloisField 2 n) =
      (1 : ExtensionField (binaryParameters n hn)) :=
    (baseFieldEmbedding (binaryParameters n hn)).map_one
  have hlong := (longRankOneFixed_upper_val n hn 1).trans
    (congrArg (positiveRoot (binaryParameters n hn) 1) hbase)
  have hshort := shortRankOneFixed_upper_val n hn 1
  simpa only [map_one] using congrArg₂
    (fun x y : SplitGroup (binaryParameters n hn) => x * y) hlong hshort


/-- The sparse actual-matrix certificate survives the genuine central quotient. -/
theorem rootProduct_fourth_ne (n : ℕ) (hn : 0 < n) : (longRoot n hn 1 * shortRoot n hn 1) ^ 4 ≠ 1 := by
  intro h
  have he : rootElementary n hn ^ 4 = 1 :=
    ElementaryCentralKernel.toCarrier_injective (binaryParameters n hn) rfl
      (by simpa only [map_pow, map_one, rootElementary_toCarrier] using h)
  apply BinaryRootWord.split_word_four_ne_one (binaryParameters n hn) rfl
  calc
    _ = (elementaryInclusion (binaryParameters n hn) (rootElementary n hn)) ^ 4 :=
      congrArg (fun x => x ^ 4) (rootElementary_split n hn).symm
    _ = elementaryInclusion (binaryParameters n hn) (rootElementary n hn ^ 4) :=
      ((elementaryInclusion (binaryParameters n hn)).map_pow (rootElementary n hn) 4).symm
    _ = elementaryInclusion (binaryParameters n hn) 1 :=
      congrArg (elementaryInclusion (binaryParameters n hn)) he
    _ = 1 := (elementaryInclusion (binaryParameters n hn)).map_one

/-- The certified word on the actual binary endpoint. -/
theorem endpointRootProduct_fourth_ne : endpointRootProduct ^ 4 ≠ 1 := by
  simpa only [endpointRootProduct] using rootProduct_fourth_ne 1 Nat.zero_lt_one

/-- The weak unconditional intrinsic endpoint estimate. -/
theorem endpoint_twoRank_le_ten : primeRank 2 (BinaryCarrier 1 Nat.zero_lt_one) ≤ 10 :=
  endpoint_twoRank_le_ten_of_fourth_ne endpointRootProduct_fourth_ne

/-- Genuine coverage is the only remaining automorphism premise. -/
theorem endpoint_automorphism_rank_le_ten
    (hcoverage : ∀ a : MulAut (BinaryCarrier 1 Nat.zero_lt_one),
      ∃ g : BinaryCarrier 1 Nat.zero_lt_one,
      ∃ e : OuterOdd.CoefficientAut (binaryParameters 1 Nat.zero_lt_one),
        a = MulAut.conj g * OuterOdd.coefficientAction (binaryParameters 1 Nat.zero_lt_one) e) :
    primeRank 2 (MulAut (BinaryCarrier 1 Nat.zero_lt_one)) ≤ 10 :=
  endpoint_automorphism_twoRank_le_ten_of_coverage endpointRootProduct_fourth_ne hcoverage


end Triality.Standard.BinaryWeakRank
