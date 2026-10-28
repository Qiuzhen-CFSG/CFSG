module

public import Theory.SpecificGroups.MinusExtraspecial.InvolutionCentralizerGeometry
public import Theory.ElementaryAbelian.Basic
import Mathlib.Tactic

/-!
# Elementary subgroups of the minus-extraspecial group of order 32

If an elementary subgroup is central it has order at most two. Otherwise a
noncentral involution in it has exactly four commuting square-one elements,
so the whole elementary subgroup has order at most four. Transport retains
the actual subgroup in any specified model of the minus group.

This excludes the elementary-eight intersection in Baumeister's J₃
triangle construction, Lemma 2.6 (2007), p.496.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative

namespace MinusExtraspecial

private theorem model_elementary_card_le_four (A : Subgroup Model)
    (hA : IsElementaryAbelian 2 A) : Nat.card A ≤ 4 := by
  classical
  let : IsElementaryAbelian 2 A := hA
  by_cases hcentral : A ≤ center Model
  · exact (card_le_of_le hcentral).trans (by rw [card_center]; decide)
  obtain ⟨u, huA, huc⟩ := SetLike.not_le_iff_exists.mp hcentral
  have hu1 : u ≠ 1 := by
    intro he
    exact huc (he ▸ (center Model).one_mem)
  have huz : u ≠ quaternion z := by
    intro he
    exact huc (he ▸ (mem_center_iff _).mpr (Or.inr rfl))
  have hpow (x : A) : (x : Model) ^ 2 = 1 :=
    congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) x)
  let t : Finset Model := {1, quaternion z, u, quaternion z * u}
  have hmem (x : A) : (x : Model) ∈ t := by
    have hc : (x : Model) * u = u * (x : Model) :=
      congrArg Subtype.val (mul_comm x (⟨u, huA⟩ : A))
    have hx := commuting_square_one_of_equiv (MulEquiv.refl Model)
      ((mem_center_iff _).mpr (Or.inr rfl))
      (by decide : quaternion z ≠ 1) (hpow ⟨u, huA⟩) hu1 huz hc (hpow x)
    simpa only [t, Finset.mem_insert, Finset.mem_singleton] using hx
  let f : A → t := fun x => ⟨x, hmem x⟩
  have hf : Function.Injective f := by
    intro x y h
    have hv : (f x : Model) = (f y : Model) := congrArg (fun z : t => (z : Model)) h
    exact Subtype.ext hv
  calc
    Nat.card A ≤ Nat.card t := Nat.card_le_card_of_injective f hf
    _ = t.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ 4 := Finset.card_le_four

/-- Every actual elementary subgroup of a specified minus group of order 32
has order at most four. -/
theorem elementary_subgroup_card_le_four {K : Type*} [Group K]
    (e : K ≃* Model) (A : Subgroup K) (hA : IsElementaryAbelian 2 A) :
    Nat.card A ≤ 4 := by
  let : IsElementaryAbelian 2 A := hA
  have hm : IsElementaryAbelian 2 (A.map e.toMonoidHom) := IsElementaryAbelian.map _
  have hb := model_elementary_card_le_four (A.map e.toMonoidHom) hm
  rwa [card_map_of_injective e.injective] at hb

end MinusExtraspecial
