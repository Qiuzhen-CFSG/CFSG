module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.Local
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.LinearThreeRestriction.Geometry
public import Theory.SpecificGroups.PSL3.CartanActions.OddDegree
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The opposite-sign linear-three restriction in 15.3.37

In the rank-one setup, a model L ≅ PSL₃(2ⁿ) with 2ⁿ ≡ -1 modulo three
must have n = 1. We use the actual nontrivial residual
Y_L = O²(Y₊ ∩ L), whose order is divisible by three. The supplied Sylow
normalizes Y_L, and the join Y_L(S ∩ L) is a solvable {2,3}-group.
Transport through the actual model equivalence and Sylow conjugacy puts
this join over the full upper-unitriangular subgroup.

For n ≥ 2, the cyclic three-core and fixed-space argument in `Geometry`
puts the join in the Borel. That Borel has order prime to three in odd
binary degree, contradicting the three-part of Y_L. A proper Sylow
overgroup alone would not give this conclusion, since parabolics also
contain a Sylow subgroup and have nontrivial three-part.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.37, printed p.1135 (PDF p.1152), with local inputs 15.3.11--12
and 15.3.33 on printed pp.1123--1125 and 1134.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction
variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L : Subgroup G} (h : Setup Yplus S M I L)

include h in
/-- The supplied Sylow normalizes the actual residual O²(Y₊ ∩ L). -/
theorem Setup.sylow_normalizes_componentPart :
    S ≤ normalizer (componentPart Yplus L : Set G) := by
  have hSY : S ≤ normalizer (Yplus : Set G) :=
    (le_inf h.sylow_le (le_sup_right.trans h.outside.1.2)).trans
      (h.normalizer_eq.symm.le.trans inf_le_right)
  change S ≤ normalizer (ComponentIntersection.intersectionResidual Yplus L : Set G)
  rw [ComponentIntersection.intersectionResidual,
    ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
  exact (le_normalizer_inf hSY (le_sup_right.trans h.normalizes_component)).trans
    (normalizer_le_normalizer_characteristic_image (Yplus ⊓ L)
      (pResidual 2 (Yplus ⊓ L : Subgroup G)))

private theorem prime_eq_of_dvd_pGroup {K : Type*} [Group K] [Finite K]
    {p q : ℕ} (hK : IsPGroup q K) (hq : q.Prime) (hp : p.Prime)
    (hd : p ∣ Nat.card K) : p = q := by
  let _ : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, hk⟩ := hK.exists_card_eq
  rw [hk] at hd
  exact (Nat.dvd_prime hq).mp (hp.dvd_of_dvd_pow hd) |>.resolve_left hp.ne_one

include h in
private theorem Setup.residual_sylow_join_prime_divisors
    (P : Sylow 2 L) (hP : (P : Subgroup L).map L.subtype = S ⊓ L) :
    ∀ p : ℕ, p.Prime →
      p ∣ Nat.card ((componentPart Yplus L).subgroupOf L ⊔ (P : Subgroup L) : Subgroup L) →
        p = 2 ∨ p = 3 := by
  let R := (componentPart Yplus L).subgroupOf L
  have hRL : componentPart Yplus L ≤ L :=
    (ComponentIntersection.intersectionResidual_le Yplus L).trans inf_le_right
  have hPR : (P : Subgroup L) ≤ normalizer (R : Set L) := by
    rw [← subgroupOf_normalizer_eq hRL]
    intro x hx
    exact h.sylow_normalizes_componentPart ((hP ▸ mem_map_of_mem L.subtype hx).1)
  intro p hp hd
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes R (P : Subgroup L) hPR
  have hdprod : p ∣ Nat.card R * Nat.card P := by
    rw [hc]
    exact dvd_mul_of_dvd_right hd _
  rcases hp.dvd_mul.mp hdprod with hR | hT
  · have hY : p ∣ Nat.card Yplus := by
      have hr : Nat.card R = Nat.card (componentPart Yplus L) :=
        Nat.card_congr (subgroupOfEquivOfLe hRL).toEquiv
      rw [hr] at hR
      exact hR.trans (card_dvd_of_le
        ((ComponentIntersection.intersectionResidual_le Yplus L).trans inf_le_left))
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 Yplus)] at hY
    rcases hp.dvd_mul.mp hY with h3 | h2
    · exact Or.inr (prime_eq_of_dvd_pGroup h.quotient_three Nat.prime_three hp h3)
    · exact Or.inl (prime_eq_of_dvd_pGroup pCore_isPGroup Nat.prime_two hp h2)
  · exact Or.inl (prime_eq_of_dvd_pGroup P.isPGroup' Nat.prime_two hp hT)

include h in
/-- The opposite-sign PSL₃ possibility in the rank-one paragraph of
15.3.37 is exactly the binary model. -/
theorem Setup.linear_three_exponent_eq_one {n : ℕ} (hn : 0 < n)
    (hmod : 2 ^ n % 3 = 2) (hm : ClassicalGroup.IsPSL L 3 (2 ^ n)) : n = 1 := by
  by_contra hne
  have hn2 : 2 ≤ n := by omega
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  obtain ⟨P, hP⟩ := h.component_sylow
  let T := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(3,F) T
    (Matrix.PSL3.LinearThree.unipotentSylow F hn hF)
  let f := (e.trans (MulAut.conj g)).toMonoidHom
  have hcoord : (P : Subgroup L).map f = Matrix.PSL3.LinearThree.unipotent F := by
    have he := congrArg Sylow.toSubgroup hg
    change ((P : Subgroup L).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at he
    rwa [map_map] at he
  let R := (componentPart Yplus L).subgroupOf L
  let J : Subgroup L := R ⊔ (P : Subgroup L)
  let H := J.map f
  have hRL : componentPart Yplus L ≤ L :=
    (ComponentIntersection.intersectionResidual_le Yplus L).trans inf_le_right
  have hJ : J.map L.subtype ≤ Yplus ⊔ S := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hRL, hP]
    exact sup_le
      (((ComponentIntersection.intersectionResidual_le Yplus L).trans inf_le_left).trans le_sup_left)
      (inf_le_left.trans le_sup_right)
  have hS : IsPGroup 2 S := by
    obtain ⟨Q, hQ⟩ := h.sylow
    exact hQ ▸ Q.isPGroup'.map I.subtype
  have hSY : S ≤ normalizer (Yplus : Set G) :=
    (le_inf h.sylow_le (le_sup_right.trans h.outside.1.2)).trans
      (h.normalizer_eq.symm.le.trans inf_le_right)
  let _ := solvable_yplus_join_of_threeGroup_quotient hS hSY h.quotient_three
  let _ : Group.IsSolvable (J.map L.subtype) :=
    Group.isSolvable_of_isSolvable_injective
      (f := inclusion hJ) (inclusion_injective hJ)
  let eJ := J.equivMapOfInjective L.subtype L.subtype_injective
  let _ : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective
    (f := eJ.toMonoidHom) eJ.injective
  let _ : Group.IsSolvable H :=
    Group.isSolvable_of_surjective (f := f.subgroupMap J) (f.subgroupMap_surjective J)
  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3 := by
    intro p hp hd
    exact h.residual_sylow_join_prime_divisors P hP p hp (hd.trans (J.card_map_dvd f))
  have hUH : Matrix.PSL3.LinearThree.unipotent F ≤ H :=
    hcoord ▸ map_mono le_sup_right
  have hB := LinearThreeGeometry.solvable_le_borel F hn2 hF hmod H hUH hprime
  have hthree : 3 ∣ Nat.card H := by
    have hc : Nat.card H = Nat.card J := card_map_of_injective (e.trans (MulAut.conj g)).injective
    rw [hc]
    have hr : Nat.card R = Nat.card (componentPart Yplus L) :=
      Nat.card_congr (subgroupOfEquivOfLe hRL).toEquiv
    exact (hr ▸ h.three_dvd_residual).trans (card_dvd_of_le (show R ≤ J from le_sup_left))
  have hodd : Odd n := by
    apply Nat.odd_iff.mpr
    have ht := Nat.BinaryTorusParity.two_pow_mod_three n
    split_ifs at ht <;> omega
  exact (Nat.prime_three.coprime_iff_not_dvd.mp
    (Matrix.PSL3.CartanActions.OddDegree.borel_threePrime F hF hodd))
      (hthree.trans (card_dvd_of_le hB))

end CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction
