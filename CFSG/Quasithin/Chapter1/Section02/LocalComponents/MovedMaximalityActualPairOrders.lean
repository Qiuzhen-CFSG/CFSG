module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityActualPair
public import Theory.SpecificGroups.Suzuki.SubgroupParameters
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.SpecificGroups.SL2.SmallOddComparisons
public import Theory.SpecificGroups.Held.OddOrderBound
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.SeventeenSylow.Preservation
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.PairBound
/-!
# The order obstruction for the actual moved pair

The squared order of the smaller simple two-core quotient divides the
containing radical quotient order. Exact orders for Rudvalis and J₄, and
the proved Held order bound, reduce the source four-model list to PSL₂(7)
in Held alone. The prime-PSL₂ calculation retains primality, oddness and
the genuine exclusion of PSL₂(4), using PSL₂(5)≃PSL₂(4).

The final theorems apply to the original moved component and its literal
containing quotient, without arbitrary maximal-overgroup classification.
Source: Aschbacher--Smith, A.3.12 and 1.2.8, pp.47--48 and 506--507.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximality
private abbrev ruOrder : ℕ := 145926144000
private abbrev j4Order : ℕ := 86775571046077562880
private abbrev heBound : ℕ := 2^12 * (3^3*5^2*7^3*17)
private abbrev commonBound : ℕ := 2^21*(3^3*5^3*7^3*11^3*13*17*23*29*31*37*43)

private theorem prime_square_candidates {p N : ℕ} (hp : p.Prime)
    (hN : N = ruOrder ∨ N = j4Order ∨ N = heBound) (hd : p^2 ∣ N) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
  have hcommon : p^2 ∣ commonBound := hd.trans (by
    rcases hN with rfl | rfl | rfl <;> norm_num [ruOrder,j4Order,heBound,commonBound])
  have hpd : p ∣ commonBound := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hcommon
  have hfac : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨
      p = 17 ∨ p = 23 ∨ p = 29 ∨ p = 31 ∨ p = 37 ∨ p = 43 := by
    change p ∣ 2^21*(3^3*5^3*7^3*11^3*13*17*23*29*31*37*43) at hpd
    simp only [hp.dvd_mul, hp.prime.dvd_pow_iff_dvd (by decide : 21 ≠ 0),
      hp.prime.dvd_pow_iff_dvd (by decide : 3 ≠ 0),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 13),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 17),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 23),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 29),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 31),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 37),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 43), or_assoc] at hpd
    exact hpd
  rcases hfac with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | (solve | omega) | (solve | norm_num [commonBound] at hcommon)

private theorem model_square_survivor {X : Type*} [Group X] [Finite X] [Group.IsPerfect X] [Nontrivial X]
    (hm : NonnormalCComponentModel X) (hn : ¬ ClassicalGroup.IsPSL X 2 4)
    {N : ℕ} (hN : N = ruOrder ∨ N = j4Order ∨ N = heBound)
    (hd : Nat.card X ^ 2 ∣ N) : N = heBound ∧ ClassicalGroup.IsPSL X 2 7 := by
  cases hm with
  | linear_even n hlow hmodel =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    have hc : Nat.card X = 2^n * ((2^n)^2-1) := by
      rw [Nat.card_congr e.toEquiv,
        ← Nat.card_congr (Theory.PSL2.sl2QuotientEquiv F).toEquiv,
        GorensteinWalter.sl2_card_formula,hF]
    have hd2 : 2^(n*2) ∣ N := by
      rw [pow_mul]
      exact (pow_dvd_pow_of_dvd (hc ▸ dvd_mul_right _ _) 2).trans hd
    have hhigh : n ≤ 10 := by
      by_contra! hh
      have hbad : 2^22 ∣ N := (pow_dvd_pow 2 (show 22 ≤ n*2 by omega)).trans hd2
      rcases hN with rfl | rfl | rfl <;> norm_num [ruOrder,j4Order,heBound] at hbad
    interval_cases n
    all_goals first
      | exact (hn ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩).elim
      | (rw [hc] at hd; rcases hN with rfl | rfl | rfl <;>
          norm_num [ruOrder,j4Order,heBound] at hd)
  | suzuki m hlow hmodel =>
    obtain ⟨e⟩ := hmodel
    have hc : Nat.card X = ((2^(2*m+1))^2+1) * (2^(2*m+1)-1) * (2^(2*m+1))^2 := by
      rw [Nat.card_congr e.toEquiv, BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card m (by omega)]
      ring
    have hr := (BenderSuzuki.MatrixGroups.SuzukiRootSubgroup m).card_subgroup_dvd_card
    rw [BenderSuzuki.MatrixGroups.suzukiRootSubgroup_card m (by omega),
      ← Nat.card_congr e.toEquiv] at hr
    have hd2 : 2^((2*m+1)*4) ∣ N := by
      rw [pow_mul,show 4=2*2 by decide,pow_mul]
      exact (pow_dvd_pow_of_dvd hr 2).trans hd
    have hhigh : m ≤ 2 := by
      by_contra! hh
      have hbad : 2^28 ∣ N := (pow_dvd_pow 2 (show 28 ≤ (2*m+1)*4 by omega)).trans hd2
      rcases hN with rfl | rfl | rfl <;> norm_num [ruOrder,j4Order,heBound] at hbad
    interval_cases m <;> rw [hc] at hd
    all_goals rcases hN with rfl | rfl | rfl <;> norm_num [ruOrder,j4Order,heBound] at hd
  | linear_prime p hp ho hmodel =>
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
    have hlarge : 3 < Nat.card F :=
      Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
        (hF ▸ ho) (fun hs => by
          let := hs
          exact Group.IsPerfect.not_isSolvable X
            (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective))
    have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) (hF ▸ ho)
    rw [← Nat.card_congr e.toEquiv,hF] at hc
    have hpd : p ∣ Nat.card X := (hp.dvd_mul.mp (hc ▸ dvd_mul_right p (p^2-1))).resolve_right
      (fun hh => by have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hh; omega)
    have hpc := prime_square_candidates hp hN ((pow_dvd_pow_of_dvd hpd 2).trans hd)
    rcases hpc with rfl | rfl | rfl | rfl | rfl
    · norm_num at ho
    · omega
    · have hfour : Nat.card (GaloisField 2 2) = 4 := by
        rw [GaloisField.card 2 2 (by decide)]; norm_num
      let b := Matrix.ProjectiveSpecialLinearGroup.cardFiveEquivFour hF
      exact (hn ⟨GaloisField 2 2,inferInstance,inferInstance,hfour,⟨e.trans b⟩⟩).elim
    · have hx : Nat.card X = 168 := by norm_num at hc; omega
      rw [hx] at hd
      have hhe : N = heBound := by
        rcases hN with rfl | rfl | rfl
        · norm_num [ruOrder] at hd
        · norm_num [j4Order] at hd
        · rfl
      exact ⟨hhe,⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩⟩
    · have hx : Nat.card X = 660 := by norm_num at hc; omega
      rw [hx] at hd
      rcases hN with rfl | rfl | rfl <;> norm_num [ruOrder,j4Order,heBound] at hd
  | janko hmodel =>
    have hx : Nat.card X = 175560 := (Nat.card_congr hmodel.some.toEquiv).trans Janko1.card_model
    rw [hx] at hd
    rcases hN with rfl | rfl | rfl <;> norm_num [ruOrder,j4Order,heBound] at hd

private theorem held_order_dvd : Nat.card Held.He ∣ heBound := by
  have hg := Held.Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup
  exact Held.OddOrderBound.card_dvd_of_graph_and_pair_bound hg
    (Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.pairStabilizer_card_dvd hg)

variable {G : Type*} [Group G] [Finite G]
private theorem actual_core_square_survivor
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B : Subgroup G} (hB : B ∈ L G (T : Subgroup G))
    (hm : B < conjugateSpanBy B (T : Subgroup G))
    (hn : ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    {N : ℕ} (hN : N = ruOrder ∨ N = j4Order ∨ N = heBound)
    (hd : Nat.card (B ⧸ pCore 2 B)^2 ∣ N) :
    N = heBound ∧ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 7 := by
  let := hB.1.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (T : Subgroup G) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show B ≤ B ⊔ (T : Subgroup G) from le_sup_left)).surjective
  let := moved_local_simple_core_quotient hG T hB hm
  exact model_square_survivor (moved_local_model hG T hB hm) hn hN hd

/-- The actual moved pair excludes Rudvalis without any arbitrary-overgroup catalogue. -/
theorem actual_pair_not_rudvalis
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G} (hB : B ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G))
    (hn : ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (he : Nonempty ((K ⧸ solvableRadical K) ≃* Rudvalis.Model)) : False := by
  have hd := actual_pair_twoCore_square_dvd hG T hB hBK hTK hm
  rw [Nat.card_congr he.some.toEquiv,Rudvalis.model_card] at hd
  have hh := (actual_core_square_survivor hG T hB hm hn (Or.inl rfl) hd).1
  norm_num [ruOrder,heBound] at hh

/-- The same actual-pair square excludes J₄. -/
theorem actual_pair_not_janko_four
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G} (hB : B ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G))
    (hn : ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (he : Nonempty ((K ⧸ solvableRadical K) ≃* Janko4.Model)) : False := by
  have hd := actual_pair_twoCore_square_dvd hG T hB hBK hTK hm
  rw [Nat.card_congr he.some.toEquiv,Janko4.Cardinality.model_card] at hd
  have hh := (actual_core_square_survivor hG T hB hm hn (Or.inr (Or.inl rfl)) hd).1
  norm_num [j4Order,heBound] at hh

/-- In the Held carrier the actual smaller simple quotient must be PSL₂(7). -/
theorem actual_pair_held_smaller_seven
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G} (hB : B ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G))
    (hn : ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (he : Nonempty ((K ⧸ solvableRadical K) ≃* Held.He)) :
    ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 7 := by
  have hd := actual_pair_twoCore_square_dvd hG T hB hBK hTK hm
  rw [Nat.card_congr he.some.toEquiv] at hd
  exact (actual_core_square_survivor hG T hB hm hn (Or.inr (Or.inr rfl))
    (hd.trans held_order_dvd)).2
end CFSG.Quasithin.Chapter1.Section02.MovedMaximality
