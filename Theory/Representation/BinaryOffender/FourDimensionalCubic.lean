module
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.BinaryOffender.ComponentPermutationObstruction
public import Theory.Representation.BinaryGroupAction
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Four-group actors in a four-dimensional binary representation

Every elementary abelian group of order four acts cubically in
characteristic two: its two commuting displacement generators square to
zero, so every triple product vanishes. A two-group acting on a nonzero
binary space fixes a nonzero vector. In dimension four the four-group
therefore has fixed codimension at most three and action ratio below two.
Thus cubic ratio two excludes every elementary four-subgroup.

This is the four-group exclusion used in Aschbacher--Smith D.2.25,
printed p.190; faithfulness is not needed for this particular implication.
-/

open Subgroup
open scoped ENNReal
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

public theorem isCubic_of_elementary_card_four (A : Subgroup G)
    (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 4) : IsCubic ρ A := by
  let := hA
  have hne : A ≠ ⊥ := by intro he; rw [he, card_bot] at hc; omega
  let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hne
  let : IsKleinFour A := ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩
  have sq (a : A) (v : V) : displacement ρ a (displacement ρ a v) = 0 :=
    sub_eq_zero.mpr (involution_fixes_displacement ρ
      (congrArg Subtype.val (IsKleinFour.mul_self a)) v)
  have comm (a b : A) (v : V) :
      displacement ρ a (displacement ρ b v) = displacement ρ b (displacement ρ a v) :=
    displacement_commute ρ ⟨hne,hA⟩ a.property b.property v
  have prod (a b : A) (v : V) : displacement ρ (a*b : A) v =
      displacement ρ a (displacement ρ b v) + displacement ρ a v + displacement ρ b v := by
    simp only [displacement, LinearMap.sub_apply, LinearMap.id_apply, Subgroup.coe_mul,
      map_mul, Module.End.mul_apply, map_sub]
    abel
  intro a ha b hb c hc' v
  let a' : A := ⟨a,ha⟩
  let b' : A := ⟨b,hb⟩
  let c' : A := ⟨c,hc'⟩
  change displacement ρ a' (displacement ρ b' (displacement ρ c' v)) = 0
  by_cases ha1 : a'=1
  · simp [ha1,displacement]
  by_cases hb1 : b'=1
  · simp [hb1,displacement]
  by_cases hc1 : c'=1
  · simp [hc1,displacement]
  by_cases hab : a'=b'
  · rw [hab,sq]
  by_cases hca : c'=a'
  · rw [hca,comm b' a',sq]
  by_cases hcb : c'=b'
  · rw [hcb,sq,map_zero]
  rw [IsKleinFour.eq_mul_of_ne_all ha1 hb1 hab hc1 hca hcb,prod]
  simp only [map_add]
  rw [comm b' a' (displacement ρ b' v)]
  simp only [sq,map_zero]
  rw [comm b' a' v,sq]
  simp

omit [Finite G] in
public theorem fixedCodim_le_three_of_four_dimensional
    [FiniteDimensional (ZMod 2) V] (hdim : Module.finrank (ZMod 2) V = 4)
    (A : Subgroup G) (hA : IsPGroup 2 A) : fixedCodim ρ A ≤ 3 := by
  let := BinaryGroupAction.action ρ
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hcard : Nat.card (Multiplicative V) = 16 := by
    rw [Nat.card_congr Multiplicative.toAdd,Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod,hdim]
    rfl
  obtain ⟨v,hv,hne⟩ := hA.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := Multiplicative V) (by rw [hcard]; decide)
    (a := (1 : Multiplicative V)) (by intro a; exact smul_one a)
  have hfix : v.toAdd ∈ fixedSpace ρ A := fun a => congrArg Multiplicative.toAdd (hv a)
  let : Nontrivial (fixedSpace ρ A) := by
    apply nontrivial_of_ne (⟨v.toAdd,hfix⟩ : fixedSpace ρ A) 0
    intro he
    apply hne
    exact (congrArg Multiplicative.ofAdd (congrArg Subtype.val he)).symm
  have hpos := Module.finrank_pos (R := ZMod 2) (M := fixedSpace ρ A)
  have hsum := fixedCodim_add_finrank ρ A
  omega

public theorem no_elementary_four_of_four_dimensional_cubicRatio_two
    [FiniteDimensional (ZMod 2) V] (hdim : Module.finrank (ZMod 2) V = 4)
    (hratio : cubicRatio ρ = 2) (A : Subgroup G)
    (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 4) : False := by
  have hne : A ≠ ⊥ := by intro he; rw [he,card_bot] at hc; omega
  have he : IsElementaryTwo A := ⟨hne,hA⟩
  have hr : rank A = 2 := by norm_num [rank,hc]
  have hcub := isCubic_of_elementary_card_four ρ A hA hc
  have hlow : (2 : ℝ≥0∞) ≤ actionRatio ρ A := by
    rw [← hratio]
    exact iInf_le_of_le A (iInf_le_of_le ⟨he,hcub⟩ le_rfl)
  have hmul : 4 ≤ fixedCodim ρ A := by
    rw [actionRatio,hr,ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
      (Or.inr (by simp))] at hlow
    exact_mod_cast hlow
  let := hA
  have hu := fixedCodim_le_three_of_four_dimensional ρ hdim A
    (IsElementaryAbelian.isPGroup 2 A)
  omega
end Representation.BinaryOffender
