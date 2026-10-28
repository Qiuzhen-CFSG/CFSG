module

public import Theory.SpecificGroups.Held.OddCubeCandidates.Cardinality
public import Theory.SpecificGroups.Held.Model.FourPointBase
public import Theory.GroupTheory.PGroup.ExtraspecialPrimeCube
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# An involution inverting the extraspecial seven-center in Held

The literal order-343 subgroup is the existing closure of `sevenFirst` and
`sevenSecond`. Its nontrivial central commutator generates its center. Put
x=(ab)⁵(b²a). The word t=(x²b²x)⁷ is an involution and inverts that commutator,
hence the entire center. The two word identities are checked on the certified
four-point base of the actual degree-2058 carrier. Nontriviality of the
commutator is checked at point zero; no group order or recognition premise
enters the proof.

Source: the ATLAS `HeG1-p2058B0` and `HeG1-max6W1` words already retained in
`Held/Model/Source` and `Held/OddCubeCandidates/source`. The discovery script
and action convention are recorded in `InvertedSevenCenter/source`.
This is the model input for the faithful degree bound consumed by K.4.
-/

open Subgroup
open scoped commutatorElement
namespace Held.InvertedSevenCenter
open OddCubeCandidates

public theorem seven_isExtraspecial : IsExtraspecial 7 seven := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact IsExtraspecial.of_noncommutative_card_prime_cube card_seven seven_not_commutative

attribute [local instance] seven_isExtraspecial

private def first : seven := ⟨sevenFirst, sevenFirst_mem⟩
private def second : seven := ⟨sevenSecond, sevenSecond_mem⟩
private def centralWord : seven := second⁻¹ * first⁻¹ * second * first

@[expose] public def inverter : He :=
  let x := (a * b) ^ 5 * (b ^ 2 * a)
  (x ^ 2 * b ^ 2 * x) ^ 7

private lemma inverter_square : inverter ^ 2 = 1 := by
  apply eq_of_four_point_images
  decide +kernel

private lemma inverter_centralWord :
    inverter * (centralWord : He) * inverter⁻¹ = (centralWord : He)⁻¹ := by
  apply eq_of_four_point_images
  decide +kernel

private lemma centralWord_ne_one : centralWord ≠ 1 := by
  have hn : representation (centralWord : He) (0 : Fin 2058) ≠ 0 := by decide +kernel
  intro h
  exact hn (congrArg (fun g : seven => representation (g : He) (0 : Fin 2058)) h)

private lemma centralWord_mem_center : centralWord ∈ center seven := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : IsMulCommutative (seven ⧸ center seven) :=
    (IsExtraspecial.quotient_elementary_abelian 7 seven).toIsMulCommutative
  have hc : commutator seven ≤ center seven :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := center seven)).mp
      inferInstance
  have hh := hc (Subgroup.commutator_mem_commutator
    (H₁ := (⊤ : Subgroup seven)) (H₂ := ⊤)
    (show second⁻¹ ∈ (⊤ : Subgroup seven) from mem_top _)
    (show first⁻¹ ∈ (⊤ : Subgroup seven) from mem_top _))
  simpa only [centralWord, commutatorElement_def, inv_inv] using hh

private lemma centralWord_order : orderOf centralWord = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have h := pow_card_eq_one' (x := (⟨centralWord, centralWord_mem_center⟩ : center seven))
  rw [IsExtraspecial.center_order_p 7 seven] at h
  have hh := congrArg (fun z : center seven => (z : seven)) h
  have hp : centralWord ^ 7 = 1 := by
    simpa only [SubmonoidClass.coe_pow, OneMemClass.coe_one] using hh
  exact orderOf_eq_prime hp centralWord_ne_one

private lemma centralWord_generates : zpowers centralWord = center seven := by
  apply eq_of_le_of_card_ge (zpowers_le.mpr centralWord_mem_center)
  rw [Nat.card_zpowers, centralWord_order, IsExtraspecial.center_order_p 7 seven]

public theorem inverter_isInvolution : inverter ≠ 1 ∧ inverter ^ 2 = 1 := by
  refine ⟨?_, inverter_square⟩
  intro ht
  have hc := inverter_centralWord
  rw [ht, one_mul, inv_one, mul_one] at hc
  have hs : (centralWord : He) ^ 2 = 1 := by
    rw [pow_two]
    calc
      _ = (centralWord : He)⁻¹ * (centralWord : He) :=
        congrArg (fun g : He => g * (centralWord : He)) hc
      _ = 1 := inv_mul_cancel _
  have hs' : centralWord ^ 2 = 1 := Subtype.ext hs
  have hdiv := orderOf_dvd_of_pow_eq_one hs'
  rw [centralWord_order] at hdiv
  norm_num at hdiv

public theorem inverter_center (z : center seven) :
    inverter * (z : He) * inverter⁻¹ = (z : He)⁻¹ := by
  have hz : (z : seven) ∈ zpowers centralWord := by rw [centralWord_generates]; exact z.property
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hz
  have he : (z : He) = (centralWord : He) ^ n := congrArg Subtype.val hn.symm
  rw [he, ← conj_zpow, inverter_centralWord, inv_zpow]

end Held.InvertedSevenCenter
