module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# An involution centralizer controls a nilpotent overgroup

A subgroup of order two has trivial automorphism group, so its normalizer
centralizes it. If it is self-centralizing in a finite nilpotent overgroup,
the normalizer condition forces equality with that overgroup.

This supplies the fixed-subgroup reduction in the linear case of GLS,
Volume 4, Chapter 2, Lemmas 15.6–15.7. The theorem concerns arbitrary
nilpotent groups; no classification or model hypothesis is used.
-/

namespace Subgroup

/-- Every element normalizing a subgroup of order two centralizes it. -/
public theorem normalizer_le_centralizer_of_card_two
    {G : Type*} [Group G] (J : Subgroup G) (hJ : Nat.card J = 2) :
    normalizer (J : Set G) ≤ centralizer (J : Set G) := by
  obtain ⟨u, _, hu⟩ := (Nat.card_eq_two_iff' (1 : J)).mp hJ
  intro g hg x hx
  by_cases hx1 : x = 1
  · simp [hx1]
  let a : J := ⟨x, hx⟩
  let b : J := ⟨g * x * g⁻¹, (hg x).mp hx⟩
  have hb1 : b ≠ 1 := by
    intro hb
    apply hx1
    exact (MulAut.conj g).injective ((congrArg Subtype.val hb).trans
      (map_one (MulAut.conj g)).symm)
  have ha1 : a ≠ 1 := fun ha => hx1 (congrArg Subtype.val ha)
  have hab : b = a := (hu b hb1).trans (hu a ha1).symm
  have hc : g * x * g⁻¹ = x := congrArg Subtype.val hab
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

/-- A self-centralizing subgroup of order two equals any finite nilpotent
overgroup in which it is self-centralizing. -/
public theorem le_of_nilpotent_of_card_two_of_centralizer_le
    {G : Type*} [Group G] (W J : Subgroup G) [Finite W]
    [Group.IsNilpotent W] (hJW : J ≤ W) (hJ : Nat.card J = 2)
    (hc : W ⊓ centralizer (J : Set G) ≤ J) : W ≤ J := by
  have hn : normalizer (J.subgroupOf W : Set W) = J.subgroupOf W := by
    apply le_antisymm _ le_normalizer
    rw [← subgroupOf_normalizer_eq hJW]
    intro x hx
    exact hc ⟨x.property, normalizer_le_centralizer_of_card_two J hJ hx⟩
  exact subgroupOf_eq_top.mp
    (normalizerCondition_iff_only_full_group_self_normalizing.mp
      (Group.normalizerCondition_of_isNilpotent (G := W)) _ hn)

/-- Localization of an involution centralizer transfers fixed-point control
from a normal subgroup `A` to a two-subgroup `V`. -/
public theorem inf_centralizer_eq_of_card_two_of_localization
    {H : Type*} [Group H] [Finite H] (V A J : Subgroup H) [A.Normal]
    (hV : IsPGroup 2 V) (hJV : J ≤ V) (hJ : Nat.card J = 2)
    (hlocal : V ⊓ centralizer (J : Set H) ≤ A ⊔ J)
    (k : H) (hJk : J ≤ centralizer ({k} : Set H))
    (hAk : A ⊓ centralizer ({k} : Set H) = ⊥) :
    V ⊓ centralizer ({k} : Set H) = J := by
  let W := V ⊓ centralizer ({k} : Set H)
  have hJW : J ≤ W := le_inf hJV hJk
  have hWp : IsPGroup 2 W := hV.to_le inf_le_left
  let : Group.IsNilpotent W := hWp.isNilpotent
  apply le_antisymm _ hJW
  apply le_of_nilpotent_of_card_two_of_centralizer_le W J hJW hJ
  intro x hx
  have hprod : x ∈ A ⊔ J := hlocal ⟨hx.1.1, hx.2⟩
  obtain ⟨a, ha, j, hj, rfl⟩ := mem_sup_of_normal_left.mp hprod
  have hjk : j * k = k * j := mem_centralizer_singleton_iff.mp (hJk hj)
  have hxk : a * j * k = k * (a * j) := mem_centralizer_singleton_iff.mp hx.1.2
  have hak : a * k = k * a := by
    apply mul_right_cancel (b := j)
    calc
      a * k * j = a * (k * j) := mul_assoc _ _ _
      _ = a * (j * k) := by rw [hjk]
      _ = a * j * k := (mul_assoc _ _ _).symm
      _ = k * (a * j) := hxk
      _ = k * a * j := (mul_assoc _ _ _).symm
  have ha1 : a = 1 := by
    have ham : a ∈ A ⊓ centralizer ({k} : Set H) :=
      ⟨ha, mem_centralizer_singleton_iff.mpr hak⟩
    simpa only [hAk, mem_bot] using ham
  simpa only [ha1, one_mul] using hj

end Subgroup

