module
public import Theory.GroupAction.AbelianCoprimeFixedGeneration
public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.Tactic
/-!
# A cubic with more than two fixed points

An elementary group of order nine acting on a finite two-group of order
larger than two has a cubic subgroup with more than two fixed points.
Otherwise every cyclic-quotient fixed subgroup is fixed by the entire
actor: automorphisms of groups of order at most two are trivial. Coprime
fixed-point generation would then make the entire group fixed and of
order at most two. No faithful-action or irreducibility assumption is used.

The conjugation form retains the actual ambient cubic and centralizer.
Source application: Aschbacher--Smith 4.2.13, printed p.612, selecting the
cubic in the original Mathieu intersection residual.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupAction
private theorem fixed_small_is_fixed
    {A U : Type*} [CommGroup A] [Group U] [Finite U] [MulDistribMulAction A U]
    (Y : Subgroup A) (hb : Nat.card (FixedPoints.subgroup Y U) ≤ 2) :
    FixedPoints.subgroup Y U ≤ FixedPoints.subgroup (⊤ : Subgroup A) U := by
  intro u hu a
  have hau : a.val • u ∈ FixedPoints.subgroup Y U := by
    intro y
    change (y : A) • (a.val • u) = a.val • u
    rw [smul_comm]
    exact congrArg (fun v : U => a.val • v) (hu y)
  by_cases hone : Nat.card (FixedPoints.subgroup Y U) = 1
  · have hu1 : u = 1 := (Subgroup.card_eq_one.mp hone).le hu
    simp [hu1]
  have htwo : Nat.card (FixedPoints.subgroup Y U) = 2 := by
    have := Nat.card_pos (α := FixedPoints.subgroup Y U)
    omega
  have uniq := (Nat.card_eq_two_iff' (1 : FixedPoints.subgroup Y U)).mp htwo
  by_cases hu1 : u = 1
  · simp [hu1]
  have hau1 : a.val • u ≠ 1 := by
    intro he
    apply hu1
    have hh := congrArg (fun v : U => a.val⁻¹ • v) he
    simpa only [inv_smul_smul,smul_one] using hh
  exact congrArg Subtype.val (uniq.unique
    (show (⟨a.val • u,hau⟩ : FixedPoints.subgroup Y U) ≠ 1 from
      fun he => hau1 (congrArg Subtype.val he))
    (show (⟨u,hu⟩ : FixedPoints.subgroup Y U) ≠ 1 from
      fun he => hu1 (congrArg Subtype.val he)))

/-- Coprime fixed-point generation forces a cubic fixed subgroup of order greater than two. -/
theorem exists_cubic_large_fixed
    {A U : Type*} [Group A] [Finite A] [IsElementaryAbelian 3 A]
    [Group U] [Finite U] [MulDistribMulAction A U]
    (hp : IsPGroup 2 U) (hA : Nat.card A = 9) (hU : 2 < Nat.card U) :
    ∃ Y : Subgroup A, Nat.card Y = 3 ∧ 2 < Nat.card (FixedPoints.subgroup Y U) := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  let : Fact (IsPGroup 2 U) := ⟨hp⟩
  by_contra hn
  push Not at hn
  have hgen := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup
    (G := U) (A := A) (q := 2) (by rw [hA]; decide)
  have hfull : FixedPoints.subgroup (⊤ : Subgroup A) U = ⊤ := by
    apply top_unique
    rw [←hgen]
    refine iSup₂_le fun Y hcyc => ?_
    have hd : Y.index ∣ 3 := by
      rw [Subgroup.index_eq_card,←hcyc.exponent_eq_card]
      exact (Group.exponent_quotient_dvd Y).trans (IsElementaryAbelian.exponent_dvd_p 3 A)
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · rw [Subgroup.index_eq_one.mp h1]
    · have hY : Nat.card Y = 3 := by
        have hh := Y.index_mul_card
        rw [h3,hA] at hh
        omega
      exact fixed_small_is_fixed Y (hn Y hY)
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hA]; decide)
  have hc : Nat.card (zpowers a) = 3 := (Nat.card_zpowers a).trans ha
  have hh := hn (zpowers a) hc
  have htop : FixedPoints.subgroup (zpowers a) U = ⊤ := by
    apply top_unique
    rw [←hfull]
    exact fun u hu a => hu ⟨a,mem_top _⟩
  rw [htop,card_top] at hh
  omega
end Theory.GroupAction

namespace Subgroup
/-- The same cubic selection for literal conjugation on an ambient two-subgroup. -/
theorem exists_cubic_large_centralizer_of_elementary_nine
    {G : Type*} [Group G] [Finite G] (E V : Subgroup G)
    [IsElementaryAbelian 3 E] (hE : Nat.card E = 9)
    (hEV : E ≤ normalizer (V : Set G)) (hp : IsPGroup 2 V)
    (hV : 2 < Nat.card V) :
    ∃ x ∈ E, orderOf x = 3 ∧
      2 < Nat.card (V ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  let := conjMulDistribMulActionOfLeNormalizer E V hEV
  obtain ⟨Y,hY,hbig⟩ := Theory.GroupAction.exists_cubic_large_fixed
    (A := E) hp hE hV
  obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hY])
  have hyE : orderOf (y : E) = 3 := (orderOf_coe y).trans hy
  refine ⟨(y : E), (y : E).property, (orderOf_coe (y : E)).trans hyE, ?_⟩
  have hle : (FixedPoints.subgroup Y V).map V.subtype ≤
      V ⊓ centralizer ({((y : E) : G)} : Set G) := by
    rintro v ⟨v,hv,rfl⟩
    refine ⟨v.property,mem_centralizer_singleton_iff.mpr ?_⟩
    have hh := congrArg V.subtype (hv y)
    change ((y : E) : G) * (v : G) * ((y : E) : G)⁻¹ = v at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  exact hbig.trans_le ((card_map_of_injective V.subtype_injective).symm.trans_le
    (card_le_of_le hle))
end Subgroup
