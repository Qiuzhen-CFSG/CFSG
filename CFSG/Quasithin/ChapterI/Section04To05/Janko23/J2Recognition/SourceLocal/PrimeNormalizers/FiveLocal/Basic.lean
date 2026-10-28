module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.ConjugateGraph

/-!
# The two five-subgroup families and the first Sylow bounds

In Aschbacher, *Sporadic Groups* (1994), 47.2, printed p.261, the two
families consist of order-five subgroups centralizing the two involution
classes. Each family is one conjugacy class: transport to a fixed involution
centralizer and apply Sylow conjugacy there. This does not yet prove that
the two families are distinct or exhaust all order-five subgroups.

The order from 47.1 also gives an abelian Sylow five-subgroup of order 25.
Consequently a Sylow subgroup containing X lies in C_G(X), but it cannot
lie in a subgroup of order 240. These are the actual initial bounds in the
root-four branch of 47.2, before its recognition argument.
-/

@[expose] public section

open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal

variable {G : Type*} [Group G] [Finite G]

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Order-five subgroups centralizing the ambient conjugacy class of t. -/
def FiveCentralizing (t : G) (E : Subgroup G) : Prop :=
  Nat.card E = 5 ∧ ∃ u : G, IsConj t u ∧ E ≤ involutionCentralizer u

/-- Sylow conjugacy in a literal local subgroup with exactly one factor of five. -/
theorem conjugate_five_of_le (H : Subgroup G)
    (hH : 5 ^ (Nat.card H).factorization 5 = 5)
    (E F : Subgroup G) (hE : Nat.card E = 5) (hF : Nat.card F = 5)
    (hEH : E ≤ H) (hFH : F ≤ H) :
    ∃ g : H, ConjAct.toConjAct (g : G) • E = F := by
  have hc (A : Subgroup G) (hA : Nat.card A = 5) (hAH : A ≤ H) :
      Nat.card (A.subgroupOf H) = 5 ^ (Nat.card H).factorization 5 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv, hA, hH]
  let P : Sylow 5 H := Sylow.ofCard (E.subgroupOf H) (hc E hE hEH)
  let Q : Sylow 5 H := Sylow.ofCard (F.subgroupOf H) (hc F hF hFH)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P Q
  have he := congrArg (fun S : Sylow 5 H => (S : Subgroup H)) hg
  change MulAut.conj g • E.subgroupOf H = F.subgroupOf H at he
  rw [conj_smul_subgroupOf hEH g] at he
  have hm := congrArg (fun S : Subgroup H => S.map H.subtype) he
  rw [map_subgroupOf_eq_of_le (conj_smul_le_of_le hEH g),
    map_subgroupOf_eq_of_le hFH] at hm
  exact ⟨g, hm⟩

/-- Every member of the family is conjugate to any fixed local Sylow subgroup. -/
theorem fiveCentralizing_iff_mem_orbit (t : G)
    (ht : 5 ^ (Nat.card (involutionCentralizer t)).factorization 5 = 5)
    (E : Subgroup G) (hE : Nat.card E = 5) (hEt : E ≤ involutionCentralizer t)
    (F : Subgroup G) :
    FiveCentralizing t F ↔ F ∈ MulAction.orbit (ConjAct G) E := by
  constructor
  · rintro ⟨hF, u, htu, hFu⟩
    obtain ⟨g, rfl⟩ := isConj_iff.mp htu
    let F₀ : Subgroup G := ConjAct.toConjAct g⁻¹ • F
    have hF₀ : Nat.card F₀ = 5 := by
      change Nat.card (F.map (MulAut.conj g⁻¹).toMonoidHom) = 5
      rw [card_map_of_injective (MulAut.conj g⁻¹).injective, hF]
    have hF₀t : F₀ ≤ involutionCentralizer t := by
      rintro _ ⟨x, hx, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      have he := mem_centralizer_singleton_iff.mp (hFu hx)
      change (g⁻¹ * x * (g⁻¹)⁻¹) * t = t * (g⁻¹ * x * (g⁻¹)⁻¹)
      have hc := congrArg (fun y : G => g⁻¹ * y * g) he
      convert hc using 1 <;> group
    obtain ⟨a, ha⟩ := conjugate_five_of_le (involutionCentralizer t) ht
      E F₀ hE hF₀ hEt hF₀t
    refine ⟨ConjAct.toConjAct g * ConjAct.toConjAct (a : G), ?_⟩
    change (ConjAct.toConjAct g * ConjAct.toConjAct (a : G)) • E = F
    rw [mul_smul, ha]
    exact smul_inv_smul (ConjAct.toConjAct g) F
  · rintro ⟨g, rfl⟩
    refine ⟨?_, (MulAut.conj (ConjAct.ofConjAct g)) t,
      isConj_iff.mpr ⟨ConjAct.ofConjAct g, rfl⟩, ?_⟩
    · change Nat.card (E.map (MulAut.conj (ConjAct.ofConjAct g)).toMonoidHom) = 5
      rw [card_map_of_injective (MulAut.conj _).injective, hE]
    · rintro _ ⟨x, hx, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      have he := congrArg (MulAut.conj (ConjAct.ofConjAct g))
        (mem_centralizer_singleton_iff.mp (hEt hx))
      change (ConjAct.ofConjAct g * x * (ConjAct.ofConjAct g)⁻¹) *
        (MulAut.conj (ConjAct.ofConjAct g)) t =
        (MulAut.conj (ConjAct.ofConjAct g)) t *
          (ConjAct.ofConjAct g * x * (ConjAct.ofConjAct g)⁻¹)
      simpa only [map_mul, MulAut.conj_apply] using he

/-- A family with this local order is nonempty. -/
theorem exists_fiveCentralizing (t : G)
    (ht : 5 ^ (Nat.card (involutionCentralizer t)).factorization 5 = 5) :
    ∃ E : Subgroup G, Nat.card E = 5 ∧ E ≤ involutionCentralizer t := by
  let P : Sylow 5 (involutionCentralizer t) := Classical.choice inferInstance
  refine ⟨(P : Subgroup (involutionCentralizer t)).map
    (involutionCentralizer t).subtype, ?_, map_subtype_le _⟩
  rw [card_map_of_injective (involutionCentralizer t).subtype_injective,
    P.card_eq_multiplicity, ht]

/-- The two-central family is one actual conjugacy class, directly from the seed. -/
theorem twoCentral_five_orbit (D : Seed G) :
    ∃ E : Subgroup G, Nat.card E = 5 ∧ E ≤ involutionCentralizer D.z ∧
      ∀ F : Subgroup G, FiveCentralizing D.z F ↔
        F ∈ MulAction.orbit (ConjAct G) E := by
  have ht : 5 ^ (Nat.card (involutionCentralizer D.z)).factorization 5 = 5 := by
    rw [D.localType.centralizer_card]
    decide +kernel
  obtain ⟨E, hE, hEt⟩ := exists_fiveCentralizing D.z ht
  exact ⟨E, hE, hEt, fiveCentralizing_iff_mem_orbit D.z ht E hE hEt⟩

/-- The initial order calculation in 47.2 uses only the order from 47.1. -/
theorem sylow_card (hG : Nat.card G = 604800) (P : Sylow 5 G) : Nat.card P = 25 := by
  rw [P.card_eq_multiplicity, hG]
  decide +kernel

theorem sylow_commutative (hG : Nat.card G = 604800) (P : Sylow 5 G) :
    IsMulCommutative P :=
  IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5) (sylow_card hG P)

/-- This is the source inclusion P ≤ C_G(X), for the same ambient X and P. -/
theorem sylow_le_centralizer (hG : Nat.card G = 604800) (P : Sylow 5 G)
    (E : Subgroup G) (hEP : E ≤ (P : Subgroup G)) :
    (P : Subgroup G) ≤ centralizer (E : Set G) :=
  (le_centralizer_iff_isMulCommutative.mpr (sylow_commutative hG P)).trans
    (centralizer_le hEP)

/-- A Sylow five-subgroup cannot lie in a root involution centralizer of order 240. -/
theorem sylow_not_le_card_240 (hG : Nat.card G = 604800) (P : Sylow 5 G)
    (H : Subgroup G) (hH : Nat.card H = 240) : ¬ (P : Subgroup G) ≤ H := by
  intro hPH
  have hd := card_dvd_of_le hPH
  rw [sylow_card hG P, hH] at hd
  norm_num at hd

/-- The first normalizer-index congruence on printed p.261. -/
theorem sylow_normalizer_relIndex_mod (hG : Nat.card G = 604800) (P : Sylow 5 G) :
    (P : Subgroup G).relIndex (normalizer (P : Set G)) ≡ 2 [MOD 5] := by
  have hi : (P : Subgroup G).index = 24192 := by
    have hm := (P : Subgroup G).index_mul_card
    rw [sylow_card hG P, hG] at hm
    omega
  have hc := Sylow.card_quotient_normalizer_modEq_card_quotient
    (p := 5) (n := 2) (H := (P : Subgroup G)) (sylow_card hG P)
  change (P : Subgroup G).relIndex (normalizer (P : Set G)) ≡
    (P : Subgroup G).index [MOD 5] at hc
  exact hc.trans (by rw [hi]; decide)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal
