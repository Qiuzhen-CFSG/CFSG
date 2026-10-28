module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.MovedDegree
public import Theory.Mathieu.M22.Properties.TwoRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowNormalElementary
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.Mathieu.M24.Properties.Order
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.SpecificGroups.Held.SylowOrderBound

/-!
# Complementary point carriers for a binary rank-one original quotient

The actual moved image has rank at least twice the original field degree.
This excludes M₂₂, M₂₃ and HS using their certified elementary-subgroup
bounds. Its two-part together with the literal local quotient gives the
order divisor 2³ⁿ(2²ⁿ−1), excluding L₄(2), L₅(2), M₂₄, J₄ and Ru in
every even degree above two. Held needs only its certified Sylow bound.
Degree two is A₅ and is excluded by the original non-A₅ hypothesis.

The same calculation restricts every remaining complementary rank-one
case to degree three or five. Quasisimple.Source applies both conclusions
to the complete carrier catalogue. All fixed vectors and original module
rows are retained. Source: Aschbacher–Smith 10.2.9, pp.750–751.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c


namespace Other

theorem not_mathieuTwentyTwo_of_binary_quotient [Group.IsPerfect I]
    {n : ℕ} (hn : 2 < n) (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (eI : (I ⧸ center I) ≃* Sporadic.Mathieu.M22) : False := by
  have hl := center_quotient_rank_of_binary_quotient D c (by omega) hL
  rw [primeRank_equiv 2 eI] at hl
  have hu := Sporadic.Mathieu.m22_twoRank_le_four
  omega

theorem not_mathieuTwentyThree_of_binary_quotient [Group.IsPerfect I]
    {n : ℕ} (hn : 2 < n) (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (eI : (I ⧸ center I) ≃* Sporadic.Mathieu.M23) : False := by
  have hl := center_quotient_rank_of_binary_quotient D c (by omega) hL
  rw [primeRank_equiv 2 eI] at hl
  have hu := Sporadic.Mathieu.m23_twoRank_le_four
  omega

theorem not_higmanSims_of_binary_quotient [Group.IsPerfect I]
    {n : ℕ} (hn : 1 < n) (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (eI : (I ⧸ center I) ≃* Sporadic.LeechRelated.HS.Carrier) : False := by
  obtain ⟨S,_,_,_,hSN,_,_,hE,_⟩ := center_quotient_data D c
  let E := ((⁅D.fullModule,L⁆).subgroupOf I).map (QuotientGroup.mk' (center I))
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  let := hE
  have hu := Sporadic.LeechRelated.HS.normal_elementary_card_le_eight
    (R.mapSurjective (f := eI.toMonoidHom) eI.surjective)
    (E.map eI.toMonoidHom) (IsElementaryAbelian.map eI.toMonoidHom)
    ((map_mono hSN).trans (le_normalizer_map eI.toMonoidHom))
  rw [card_map_of_injective eI.injective] at hu
  have hl := center_moved_card_of_binary_quotient D c (by omega) hL
  change 2 ^ (2 * n) ≤ Nat.card E at hl
  have h16 : 2 ^ 4 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by decide) (by omega)
  omega
end Other
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple

namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
private theorem even_order_exclusion {n m : ℕ} (hn : 2 < n) (he : Even n)
    (h24 : ¬ 2 ^ 24 ∣ m)
    (h4 : ¬ (2 ^ (3 * 4) * ((2 ^ 4) ^ 2 - 1)) ∣ m)
    (h6 : ¬ (2 ^ (3 * 6) * ((2 ^ 6) ^ 2 - 1)) ∣ m)
    (hd : 2 ^ (3 * n) * ((2 ^ n) ^ 2 - 1) ∣ m) : False := by
  have hsmall : n < 8 := by
    by_contra! hbig
    exact h24 ((pow_dvd_pow 2 (by omega : 24 ≤ 3 * n)).trans
      ((dvd_mul_right _ _).trans hd))
  have hncase : n = 4 ∨ n = 6 := by
    obtain ⟨k,hk⟩ := he
    omega
  rcases hncase with rfl | rfl
  · exact h4 hd
  · exact h6 hd
include D c

theorem not_mathieuTwentyFour_of_even_binary_quotient [Group.IsPerfect I]
    {n : ℕ} (hn : 2 < n) (he : Even n)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (eI : (I ⧸ center I) ≃* Sporadic.Mathieu.M24) : False := by
  have hd := binary_quotient_moved_order_dvd D c (by omega) hL
  rw [Nat.card_congr eI.toEquiv,Sporadic.Mathieu.m24_order] at hd
  exact even_order_exclusion hn he (by norm_num) (by norm_num) (by norm_num) hd

theorem not_jankoFour_of_even_binary_quotient [Group.IsPerfect I]
    {n : ℕ} (hn : 2 < n) (he : Even n)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (eI : (I ⧸ center I) ≃* Janko4.Model) : False := by
  have hd := binary_quotient_moved_order_dvd D c (by omega) hL
  rw [Nat.card_congr eI.toEquiv,Janko4.Cardinality.model_card] at hd
  exact even_order_exclusion hn he (by norm_num) (by norm_num) (by norm_num) hd

theorem not_rudvalis_of_even_binary_quotient [Group.IsPerfect I]
    {n : ℕ} (hn : 2 < n) (he : Even n)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (eI : (I ⧸ center I) ≃* Rudvalis.Model) : False := by
  have hd := binary_quotient_moved_order_dvd D c (by omega) hL
  rw [Nat.card_congr eI.toEquiv,Rudvalis.model_card] at hd
  exact even_order_exclusion hn he (by norm_num) (by norm_num) (by norm_num) hd

theorem not_held_of_even_binary_quotient [Group.IsPerfect I]
    {n : ℕ} (hn : 2 < n) (he : Even n)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (eI : (I ⧸ center I) ≃* Held.He) : False := by
  have hn4 : 4 ≤ n := by obtain ⟨k,hk⟩ := he; omega
  have hd := binary_quotient_moved_order_dvd D c (by omega) hL
  rw [Nat.card_congr eI.toEquiv] at hd
  exact Held.not_two_pow_twelve_dvd_card
    ((pow_dvd_pow 2 (by omega : 12 ≤ 3*n)).trans ((dvd_mul_right _ _).trans hd))

omit D c in
private theorem binary_card (r : ℕ) [NeZero r] :
    Nat.card PSL(r, ZMod 2) = ∏ i : Fin r, (2 ^ r - 2 ^ i.val) := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) r
  simpa only [Nat.card_zmod, show 2 - 1 = 1 from rfl, Nat.gcd_one_right, mul_one] using h

theorem not_higher_linear_of_even_binary_quotient [Group.IsPerfect I]
    {n : ℕ} (hn : 2 < n) (he : Even n)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {r : ℕ} (hr : r = 4 ∨ r = 5) (hI : ClassicalGroup.IsPSL (I ⧸ center I) r 2) : False := by
  obtain ⟨F,_,_,hF,⟨eI⟩⟩ := hI
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let d := eI.trans (Atlas.fieldEquivPSL r f)
  have hd := binary_quotient_moved_order_dvd D c (by omega) hL
  rw [Nat.card_congr d.toEquiv] at hd
  rcases hr with rfl | rfl
  · rw [binary_card] at hd
    norm_num [Fin.prod_univ_succ] at hd
    exact even_order_exclusion hn he (by norm_num) (by norm_num) (by norm_num) hd
  · rw [binary_card] at hd
    norm_num [Fin.prod_univ_succ] at hd
    exact even_order_exclusion hn he (by norm_num) (by norm_num) (by norm_num) hd
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other

namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
open Subgroup Theory.GroupTheory Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

theorem not_remaining_of_even_binary_quotient [Group.IsPerfect I]
    {n : ℕ} (hn : 1 < n) (he : Even n)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hmodels :
      (∃ r, (r = 4 ∨ r = 5) ∧ ClassicalGroup.IsPSL (I ⧸ center I) r 2) ∨
      (∃ name : ClassificationModels.SporadicName,
        (name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j4 ∨
          name = .hs ∨ name = .he ∨ name = .ru) ∧
        Nonempty ((I ⧸ center I) ≃* name.Carrier))) : False := by
  have hn2 := two_lt_binary_degree_of_not_alternating_five hn hL hna
  rcases hmodels with ⟨r,hr,hI⟩ | ⟨name,hname,⟨eI⟩⟩
  · exact not_higher_linear_of_even_binary_quotient D c hn2 he hL hr hI
  · rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact not_mathieuTwentyTwo_of_binary_quotient D c hn2 hL eI
    · exact not_mathieuTwentyThree_of_binary_quotient D c hn2 hL eI
    · exact not_mathieuTwentyFour_of_even_binary_quotient D c hn2 he hL eI
    · exact not_jankoFour_of_even_binary_quotient D c hn2 he hL eI
    · exact not_higmanSims_of_binary_quotient D c hn hL eI
    · exact not_held_of_even_binary_quotient D c hn2 he hL eI
    · exact not_rudvalis_of_even_binary_quotient D c hn2 he hL eI
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other

namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
open Chapter3.Section02
private theorem degree_three_or_five {n m : ℕ} (hn : 2 < n)
    (h24 : ¬ 2 ^ 24 ∣ m)
    (h4 : ¬ (2 ^ (3 * 4) * ((2 ^ 4) ^ 2 - 1)) ∣ m)
    (h6 : ¬ (2 ^ (3 * 6) * ((2 ^ 6) ^ 2 - 1)) ∣ m)
    (h7 : ¬ (2 ^ (3 * 7) * ((2 ^ 7) ^ 2 - 1)) ∣ m)
    (hd : 2 ^ (3 * n) * ((2 ^ n) ^ 2 - 1) ∣ m) : n = 3 ∨ n = 5 := by
  have hsmall : n < 8 := by
    by_contra! hbig
    exact h24 ((pow_dvd_pow 2 (by omega : 24 ≤ 3 * n)).trans
      ((dvd_mul_right _ _).trans hd))
  have hn4 : n ≠ 4 := by rintro rfl; exact h4 hd
  have hn6 : n ≠ 6 := by rintro rfl; exact h6 hd
  have hn7 : n ≠ 7 := by rintro rfl; exact h7 hd
  omega

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

theorem binary_degree_three_or_five [Group.IsPerfect I]
    {n : ℕ} (hn : 1 < n)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hmodels :
      (∃ r, (r = 4 ∨ r = 5) ∧ ClassicalGroup.IsPSL (I ⧸ center I) r 2) ∨
      (∃ name : ClassificationModels.SporadicName,
        (name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j4 ∨
          name = .hs ∨ name = .he ∨ name = .ru) ∧
        Nonempty ((I ⧸ center I) ≃* name.Carrier))) : n = 3 ∨ n = 5 := by
  have hn2 := two_lt_binary_degree_of_not_alternating_five hn hL hna
  have hd := binary_quotient_moved_order_dvd D c (by omega) hL
  rcases hmodels with ⟨r,hr,hI⟩ | ⟨name,hname,⟨eI⟩⟩
  · obtain ⟨F,_,_,hF,⟨eI⟩⟩ := hI
    let := Fintype.ofFinite F
    let f : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
    let d := eI.trans (Atlas.fieldEquivPSL r f)
    rw [Nat.card_congr d.toEquiv] at hd
    rcases hr with rfl | rfl
    · rw [binary_card] at hd
      norm_num [Fin.prod_univ_succ] at hd
      exact degree_three_or_five hn2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hd
    · rw [binary_card] at hd
      norm_num [Fin.prod_univ_succ] at hd
      exact degree_three_or_five hn2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hd
  · rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (not_mathieuTwentyTwo_of_binary_quotient D c hn2 hL eI).elim
    · exact (not_mathieuTwentyThree_of_binary_quotient D c hn2 hL eI).elim
    · rw [Nat.card_congr eI.toEquiv] at hd
      change 2 ^ (3 * n) * ((2 ^ n) ^ 2 - 1) ∣ Nat.card Sporadic.Mathieu.M24 at hd
      rw [Sporadic.Mathieu.m24_order] at hd
      exact degree_three_or_five hn2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hd
    · rw [Nat.card_congr eI.toEquiv] at hd
      change 2 ^ (3 * n) * ((2 ^ n) ^ 2 - 1) ∣ Nat.card Janko4.Model at hd
      rw [Janko4.Cardinality.model_card] at hd
      exact degree_three_or_five hn2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hd
    · exact (not_higmanSims_of_binary_quotient D c hn hL eI).elim
    · rw [Nat.card_congr eI.toEquiv] at hd
      have hsmall : n < 4 := by
        by_contra! hbig
        exact Held.not_two_pow_twelve_dvd_card
          ((pow_dvd_pow 2 (by omega : 12 ≤ 3*n)).trans ((dvd_mul_right _ _).trans hd))
      exact .inl (by omega)
    · rw [Nat.card_congr eI.toEquiv] at hd
      change 2 ^ (3 * n) * ((2 ^ n) ^ 2 - 1) ∣ Nat.card Rudvalis.Model at hd
      rw [Rudvalis.model_card] at hd
      exact degree_three_or_five hn2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hd
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
