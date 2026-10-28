module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.RankOne
public import Theory.Representation.SL2.PerfectCoreQuotientDegree
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# Binary linear embeddings and the remaining rank-one point carriers

The literal local image in a binary linear carrier acts on its natural
space. A nontrivial perfect action with the original SL₂(2ⁿ) two-core
quotient has a noncentral irreducible section of dimension at least 2n.
Thus both L₄(2) and L₅(2) are impossible for every non-A₅ rank-one quotient,
including odd degrees. No irreducibility of the chosen full module is used.

Combining this comparison with the moved-image order divisor leaves only
degree three with M₂₄, J₄, Held or Rudvalis, or degree five with J₄, among
the complementary carriers. Quasisimple.Source applies this list to the
actual escaping component and retains the Ree branch separately.
Source: Aschbacher–Smith E.2.13(4), p.225, and 10.2.9, pp.750–751.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
open Chapter3.Section02 BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

/-- The actual smaller quotient bounds the natural dimension of its containing carrier. -/
theorem binary_linear_dimension_of_binary_quotient
    {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hI : ClassicalGroup.IsPSL (I ⧸ center I) r 2) : 2 * n ≤ r := by
  obtain ⟨F,_,_,hF,⟨eI⟩⟩ := hI
  let := Fintype.ofFinite F
  let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let f := (eI.trans (Atlas.fieldEquivPSL r k)).trans (projectiveEquivLinear hr)
  let : Finite (LinearGroup r) := Finite.of_equiv (I ⧸ center I) f.toEquiv
  let A := (L.subgroupOf I).map (f.toMonoidHom.comp (QuotientGroup.mk' (center I)))
  let := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (markedLocalHom_surjective c.strict.le f)
  obtain ⟨K,hfield,hfinite,hK,⟨eL⟩⟩ := hL
  let := hfield
  let := hfinite
  let := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  let d : (A ⧸ pCore 2 A) ≃* SL(2,K) :=
    ((markedCoreQuotientEquiv D c.strict.le f).symm.trans eL).trans
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := K)).symm
  let ρ : Representation (ZMod 2) A (Space r) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp A.subtype
  have hnt : ∃ a, ρ a ≠ 1 := by
    by_contra! h
    have ha : ∀ a : A, a = 1 := by
      intro a
      apply Subtype.ext
      apply LinearEquiv.toLinearMap_injective
      exact h a
    have hc := marked_core_center_not_central D c.strict.le f
    change ¬ (center (pCore 2 A)).map (pCore 2 A).subtype ≤ center A at hc
    exact hc (by intro a _; rw [ha a]; exact one_mem _)
  have hd := Representation.SL2.perfect_core_quotient_finrank_bound d ρ hnt (by omega) hK
  simpa only [Space, Module.finrank_fin_fun, Fintype.card_fin] using hd

/-- All non-A₅ binary rank-one quotients exclude both higher binary-linear carriers. -/
theorem not_higher_linear_of_binary_quotient
    {n : ℕ} (hn : 1 < n)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {r : ℕ} (hr : r = 4 ∨ r = 5) (hI : ClassicalGroup.IsPSL (I ⧸ center I) r 2) : False := by
  have hn2 := two_lt_binary_degree_of_not_alternating_five hn hL hna
  have hd := binary_linear_dimension_of_binary_quotient D c (by omega) (by omega) hL hI
  omega
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other

namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

/-- The remaining complementary carriers are coupled to the actual original degree. -/
theorem binary_quotient_sporadic_residual [Group.IsPerfect I]
    {n : ℕ} (hn : 1 < n)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hmodels :
      (∃ r, (r = 4 ∨ r = 5) ∧ ClassicalGroup.IsPSL (I ⧸ center I) r 2) ∨
      (∃ name : ClassificationModels.SporadicName,
        (name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j4 ∨
          name = .hs ∨ name = .he ∨ name = .ru) ∧
        Nonempty ((I ⧸ center I) ≃* name.Carrier))) :
    (n = 3 ∧ ∃ name : ClassificationModels.SporadicName,
      (name = .m24 ∨ name = .j4 ∨ name = .he ∨ name = .ru) ∧
      Nonempty ((I ⧸ center I) ≃* name.Carrier)) ∨
    (n = 5 ∧ Nonempty ((I ⧸ center I) ≃* Janko4.Model)) := by
  have hdegree := binary_degree_three_or_five D c hn hL hna hmodels
  have hn2 := two_lt_binary_degree_of_not_alternating_five hn hL hna
  rcases hmodels with ⟨r,hr,hI⟩ | ⟨name,hname,⟨eI⟩⟩
  · exact (not_higher_linear_of_binary_quotient D c hn hL hna hr hI).elim
  · rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (not_mathieuTwentyTwo_of_binary_quotient D c hn2 hL eI).elim
    · exact (not_mathieuTwentyThree_of_binary_quotient D c hn2 hL eI).elim
    · rcases hdegree with hn3 | hn5
      · exact .inl ⟨hn3,.m24,by simp,⟨eI⟩⟩
      · have hd := binary_quotient_moved_order_dvd D c (by omega) hL
        rw [hn5,Nat.card_congr eI.toEquiv] at hd
        change 2 ^ (3 * 5) * ((2 ^ 5) ^ 2 - 1) ∣ Nat.card Sporadic.Mathieu.M24 at hd
        rw [Sporadic.Mathieu.m24_order] at hd
        norm_num at hd
    · rcases hdegree with hn3 | hn5
      · exact .inl ⟨hn3,.j4,by simp,⟨eI⟩⟩
      · exact .inr ⟨hn5,⟨eI⟩⟩
    · exact (not_higmanSims_of_binary_quotient D c hn hL eI).elim
    · rcases hdegree with hn3 | hn5
      · exact .inl ⟨hn3,.he,by simp,⟨eI⟩⟩
      · have hd := binary_quotient_moved_order_dvd D c (by omega) hL
        rw [hn5,Nat.card_congr eI.toEquiv] at hd
        exact (Held.not_two_pow_twelve_dvd_card
          ((by norm_num : 2^12 ∣ 2^(3*5)*((2^5)^2-1)).trans hd)).elim
    · rcases hdegree with hn3 | hn5
      · exact .inl ⟨hn3,.ru,by simp,⟨eI⟩⟩
      · have hd := binary_quotient_moved_order_dvd D c (by omega) hL
        rw [hn5,Nat.card_congr eI.toEquiv] at hd
        change 2 ^ (3 * 5) * ((2 ^ 5) ^ 2 - 1) ∣ Nat.card Rudvalis.Model at hd
        rw [Rudvalis.model_card] at hd
        norm_num at hd
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
