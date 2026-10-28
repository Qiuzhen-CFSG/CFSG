module

public import Theory.SpecificGroups.Triality.StandardTwoRank.Sylow
public import Theory.SpecificGroups.Triality.StandardTwoRank.FourSemilinear.RankCriterion
public import Theory.SpecificGroups.Triality.StandardTwoRank.FourSemilinear.HighestRoot
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual
public import Theory.SpecificGroups.Triality.BinaryCenter
public import Theory.GroupTheory.AutomorphismRankFixedSubgroup
public import Theory.GroupTheory.TwoRankFourthPower

/-!
# Sharp automorphism rank for genuine binary triality

The proved inner--coefficient coverage gives a cyclic outer quotient of
order dividing 3n. Every elementary automorphism subgroup fixes a Sylow
two-subgroup. A maximal-rank inner kernel would contain its central
highest-root subgroup. A noninner involution cannot fix that subgroup:
its coefficient factor has even order, whereas the automorphisms fixing
the base field have order dividing three. Consequently the inner kernel
has rank at most 5n - 1, and the cyclic outer image adds at most one.
This proves the sharp bound for every n > 0, including n = 1 and n = 2.

Simplicity and perfectness are inherited on this same carrier, as in the
G.9 component application. The separate unconditional assembly must supply
those instances. The older odd-exponent and fixed-group routes retain
their public interfaces; the all-exponent estimate below needs no
normalization or fixed-group descent premise.

Source: Aschbacher--Smith, printed p.356 (`refs/quasithin.pdf`);
GLS3 §2.5, especially 2.5.12(d,f) and 2.5.17
(`refs/KGroup/GLS3/chapter2.tex`). All actions use Aut(GF(2^(3n))) and the
actual graph-field construction and elementary central quotient.
-/

public section
noncomputable section
namespace Triality.Standard.TwoRank.Automorphisms
open Theory.GroupTheory OuterOdd EvenField Parabolics RadicalCoordinates.Centers

private theorem highestRoot_elementary (n : ℕ) (hn : 0 < n) :
    IsElementaryAbelian 2 (highestRoot (binaryParameters n hn)) := by
  let P := binaryParameters n hn
  let e := highestRootEquiv P rfl
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · intro x y
    apply e.symm.injective
    simp only [map_mul, mul_comm]
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply e.symm.injective
    rw [map_pow, map_one]
    change 2 • (e.symm x).toAdd = 0
    rw [two_nsmul]
    exact CharTwo.add_self_eq_zero _

variable (n : ℕ) (hn : 0 < n)
  [IsSimpleGroup (BinaryCarrier n hn)] [Group.IsPerfect (BinaryCarrier n hn)]

/-- Coverage by the actual cubic coefficient action makes the outer group cyclic. -/
theorem binary_outer_isCyclic : IsCyclic (MulAut.Outer (BinaryCarrier n hn)) :=
  outer_isCyclic_of_inner_coefficient (binaryParameters n hn)
    (Coverage.binary_inner_coefficient n hn)

/-- The order of the actual outer quotient divides 3n, retaining its odd
diagram contribution even when n = 1. -/
theorem binary_outer_card_dvd : Nat.card (MulAut.Outer (BinaryCarrier n hn)) ∣ 3 * n := by
  have hs := (outerCoefficientAction_surjective_iff (binaryParameters n hn)).mpr
    (Coverage.binary_inner_coefficient n hn)
  have hd := Subgroup.card_dvd_of_surjective
    (outerCoefficientAction (binaryParameters n hn)) hs
  have hc : Nat.card (CoefficientAut (binaryParameters n hn)) = 3 * n :=
    GaloisField.card_ringAut 2 (3 * n) (by omega)
  exact hc ▸ hd

/-- The sharp automorphism two-rank bound for every positive binary exponent.
Only simplicity and perfectness on the same genuine carrier are inherited;
coverage, intrinsic rank and the noninner highest-root movement are proved. -/
theorem automorphism_twoRank_le_five_mul :
    primeRank 2 (MulAut (BinaryCarrier n hn)) ≤ 5 * n := by
  let P := binaryParameters n hn
  let : IsCyclic (MulAut.Outer (BinaryCarrier n hn)) := binary_outer_isCyclic n hn
  let : IsElementaryAbelian 2 (highestRoot P) := highestRoot_elementary n hn
  apply FourSemilinear.automorphism_twoRank_le_of_moved_central_bound (5 * n) (by omega)
    (binaryCarrier_center_eq_bot n hn) (twoRank_le_five_mul n hn)
    (unipotentSylow P rfl) (highestRoot P)
  · intro z hz u hu
    obtain ⟨w, hw, rfl⟩ := highestRoot_le_center_unipotent P rfl hz
    exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hw) ⟨u, hu⟩)).symm
  · exact FourSemilinear.binary_noninner_involution_not_fix_highestRoot n hn

/-- No descent premise is needed for positive odd exponents. -/
theorem automorphism_twoRank_le_of_odd (hodd : Odd n) :
    primeRank 2 (MulAut (BinaryCarrier n hn)) ≤ 5 * n := by
  apply (automorphism_twoRank_le_of_odd_outer (binaryCarrier_center_eq_bot n hn) ?_).trans
    (twoRank_le_five_mul n hn)
  intro hd
  have heven : 2 ∣ n := (Nat.Prime.dvd_mul Nat.prime_two).mp
    (hd.trans (binary_outer_card_dvd n hn)) |>.resolve_left (by decide)
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr heven)

/-- The sharp endpoint bound, retaining the coefficient field GF(8). -/
theorem endpoint_automorphism_twoRank_le_five
    [IsSimpleGroup (BinaryCarrier 1 Nat.zero_lt_one)]
    [Group.IsPerfect (BinaryCarrier 1 Nat.zero_lt_one)] :
    primeRank 2 (MulAut (BinaryCarrier 1 Nat.zero_lt_one)) ≤ 5 :=
  automorphism_twoRank_le_of_odd 1 Nat.zero_lt_one (by decide)

/-- Sharp rank assembly from genuine smaller fixed-group isomorphisms.
The explicit premise is geometric, with no rank or coverage certificate. -/
theorem automorphism_twoRank_le_of_fixed_models
    (hmodels : ∀ a : MulAut (BinaryCarrier n hn), a ^ 2 = 1 →
      a ∉ MulAut.innerSubgroup (BinaryCarrier n hn) →
      ∃ (m : ℕ) (hm : 0 < m), n = 2 * m ∧
        Nonempty (a.fixedSubgroup ≃* BinaryCarrier m hm)) :
    primeRank 2 (MulAut (BinaryCarrier n hn)) ≤ 5 * n := by
  let := binary_outer_isCyclic n hn
  apply automorphism_twoRank_le_of_cyclic_outer_fixed (binaryCarrier_center_eq_bot n hn)
    (twoRank_le_five_mul n hn)
  intro a ha hi
  obtain ⟨m, hm, hnm, ⟨e⟩⟩ := hmodels a ha hi
  rw [primeRank_equiv 2 e]
  have hr := twoRank_le_five_mul m hm
  omega

/-- An alternative sharp bound using two explicit geometric inputs.
The inner--coefficient decomposition and every intrinsic rank estimate are
discharged by their proved producers. -/
theorem automorphism_twoRank_le_of_normalization_descent
    (hnormalize : ∀ (a : MulAut (BinaryCarrier n hn)), a ^ 2 = 1 →
      a ∉ MulAut.innerSubgroup (BinaryCarrier n hn) →
      ∀ (g : BinaryCarrier n hn) (e : CoefficientAut (binaryParameters n hn)),
      a = MulAut.conj g * coefficientAction (binaryParameters n hn) e →
      ∀ (m : ℕ), 0 < m → n = 2 * m →
        ∃ b : MulAut (BinaryCarrier n hn), ∀ x, b (a x) =
          coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3 * m)) (b x))
    (hdescent : ∀ (m : ℕ) (hm : 0 < m), n = 2 * m →
      Nonempty ((coefficientAction (binaryParameters n hn)
        (coefficientFrobenius n hn (3 * m))).fixedSubgroup ≃* BinaryCarrier m hm)) :
    primeRank 2 (MulAut (BinaryCarrier n hn)) ≤ 5 * n := by
  apply automorphism_twoRank_le_of_fixed_models n hn
  intro a ha hi
  obtain ⟨g, e, he⟩ := Coverage.binary_inner_coefficient n hn a
  obtain ⟨m, hm, hnm⟩ := even_parameter_of_noninner_inner_coefficient n hn a ha hi g e he
  obtain ⟨b, hb⟩ := hnormalize a ha hi g e he m hm hnm
  obtain ⟨d⟩ := hdescent m hm hnm
  exact ⟨m, hm, hnm, ⟨(MulAut.fixedSubgroupEquivOfCompatible b a _ hb).trans d⟩⟩

end Triality.Standard.TwoRank.Automorphisms
