module

public import Theory.GroupTheory.PGroup.ExtraspecialCentralProductOrder
public import Theory.GroupTheory.PGroup.ExtraspecialInvolution
public import Theory.GroupTheory.PGroup.Omega

/-!
# Second omega in an extraspecial–cyclic central product

For commuting factors `A` and `B`, with `A` extraspecial at two, the second
omega of their product is `A Ω₂(B)`: every element of `A` has fourth power
one, so the fourth-power condition on a product reduces to its `B` component.
When `A` has order eight and `B` is cyclic of order at least four in a finite
two-group with cyclic center, this subgroup has order sixteen.

If the product is characteristic, so is its second omega. If the centralizer
of `Ω₂(B)` lies in the product, the centralizer of this second omega lies in
`B`, hence is cyclic. The extraspecial factor makes the subgroup nonabelian.
Neither factor is required to be characteristic.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, p.392, the characteristic
order-sixteen detection subgroup for a large cyclic Hall tail.
-/

open Subgroup
open scoped IsMulCommutative

namespace Subgroup

private theorem omega_two_card_of_cyclic
    {B : Type*} [Group B] [Finite B] [IsCyclic B]
    (hB : IsPGroup 2 B) (hcard : 4 ≤ Nat.card B) :
    Nat.card (omega B (p := 2) 2) = 4 := by
  have heq : omega B (p := 2) 2 = (powMonoidHom 4 : B →* B).ker := by
    apply le_antisymm
    · apply (closure_le _).mpr
      intro x hx
      exact hx
    · intro x hx
      exact subset_closure hx
  rw [heq, IsCyclic.card_powMonoidHom_ker]
  apply Nat.gcd_eq_right
  obtain ⟨n, hn⟩ := hB.exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra h
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> simp_all
  rw [hn]
  exact pow_dvd_pow 2 hn2

/-- In a commuting product with an extraspecial binary factor, second omega
is the product of that factor with second omega of the other factor. -/
public theorem omega_two_map_eq_sup_of_extraspecial
    {P : Type*} [Group P] (A B : Subgroup P) [B.Normal]
    [IsExtraspecial 2 A] (hc : B ≤ centralizer (A : Set P)) :
    (omega (A ⊔ B : Subgroup P) (p := 2) 2).map (A ⊔ B).subtype =
      A ⊔ (omega B (p := 2) 2).map B.subtype := by
  let M := A ⊔ B
  let D := (omega B (p := 2) 2).map B.subtype
  let N := (omega M (p := 2) 2).map M.subtype
  have hAN : A ≤ N := by
    intro a ha
    refine ⟨⟨a, mem_sup_left ha⟩, subset_closure ?_, rfl⟩
    exact Subtype.ext (congrArg (fun a : A => (a : P)) (IsExtraspecial.pow_four_eq_one (⟨a, ha⟩ : A)))
  have hDN : D ≤ N := by
    apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    intro b hb
    refine ⟨⟨b, mem_sup_right b.property⟩, subset_closure ?_, rfl⟩
    exact Subtype.ext (congrArg (fun b : B => (b : P)) hb)
  apply le_antisymm ?_ (sup_le hAN hDN)
  apply map_le_iff_le_comap.mpr
  apply (closure_le _).mpr
  intro x hx
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_normal_right.mp x.property
  have ha4 : a ^ 4 = 1 := congrArg Subtype.val
    (IsExtraspecial.pow_four_eq_one (⟨a, ha⟩ : A))
  have hb4 : b ^ 4 = 1 := by
    have hx4 : (x : P) ^ 4 = 1 := congrArg Subtype.val hx
    rw [← hab, (show Commute a b from hc hb a ha).mul_pow, ha4, one_mul] at hx4
    exact hx4
  change (x : P) ∈ A ⊔ D
  rw [← hab]
  exact (A ⊔ D).mul_mem (mem_sup_left ha)
    (mem_sup_right ⟨⟨b, hb⟩, subset_closure (Subtype.ext hb4), rfl⟩)

/-- An extraspecial factor of order eight and a cyclic factor of order at
least four produce a characteristic nonabelian subgroup of order sixteen
with cyclic centralizer, provided their product is characteristic and the
centralizer of the cyclic factor's second omega lies in that product. -/
public theorem exists_characteristic_sixteen_of_extraspecial_cyclic_product
    {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (hP : IsPGroup 2 P) (A B : Subgroup P) [A.Normal] [B.Normal]
    [IsExtraspecial 2 A] [IsCyclic B] (hA : Nat.card A = 8)
    (hB : 4 ≤ Nat.card B) (hc : B ≤ centralizer (A : Set P))
    (hM : (A ⊔ B).Characteristic)
    (hcut : centralizer (((omega B (p := 2) 2).map B.subtype : Subgroup P) : Set P) ≤ A ⊔ B) :
    ∃ N : Subgroup P, N.Characteristic ∧ ¬ IsMulCommutative N ∧
      Nat.card N = 16 ∧ IsCyclic (centralizer (N : Set P)) := by
  let M := A ⊔ B
  let D := (omega B (p := 2) 2).map B.subtype
  let N := (omega M (p := 2) 2).map M.subtype
  let : M.Characteristic := hM
  let : (omega M (p := 2) 2).Characteristic := omega_characteristic M 2
  let : (omega B (p := 2) 2).Characteristic := omega_characteristic B 2
  have hN : N = A ⊔ D := omega_two_map_eq_sup_of_extraspecial A B hc
  have hAN : A ≤ N := hN ▸ le_sup_left
  have hDN : D ≤ N := hN ▸ le_sup_right
  have hDB : D ≤ B := map_subtype_le _
  have hDc : Nat.card D = 4 := (card_map_of_injective B.subtype_injective).trans
    (omega_two_card_of_cyclic (hP.to_subgroup B) hB)
  have hDne : D ≠ ⊥ := by intro h; simp [h] at hDc
  let : D.Normal := inferInstance
  have hi := card_inf_eq_two_of_extraspecial_of_cyclic_center hP A D hDne (hDB.trans hc)
  have hNc : Nat.card N = 16 := by
    have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes A D
      ((hDB.trans hc).trans (centralizer_le_normalizer _))
    rw [hA, hDc, hi, ← hN] at h
    omega
  have hncomm : ¬ IsMulCommutative N := by
    intro hn
    let : IsMulCommutative N := hn
    have hz : center A = ⊤ := by
      apply top_unique
      intro a _
      apply mem_center_iff.mpr
      intro b
      exact Subtype.ext (congrArg (fun n : N => (n : P))
        (mul_comm (⟨b, hAN b.property⟩ : N) (⟨a, hAN a.property⟩ : N)))
    have h := IsExtraspecial.center_order_p 2 A
    rw [hz, card_top, hA] at h
    contradiction
  have hBne : B ≠ ⊥ := by intro h; simp [h] at hB
  have hiB : A ⊓ B = (center A).map A.subtype := by
    apply eq_of_le_of_card_ge
    · rintro x ⟨ha, hb⟩
      exact ⟨⟨x, ha⟩, mem_center_iff.mpr (fun a => Subtype.ext (hc hb a a.property)), rfl⟩
    · rw [card_map_of_injective A.subtype_injective, IsExtraspecial.center_order_p 2 A,
        card_inf_eq_two_of_extraspecial_of_cyclic_center hP A B hBne hc]
  have hCB : centralizer (N : Set P) ≤ B := by
    intro x hx
    have hxM : x ∈ A ⊔ B := hcut (fun d hd => hx d (hDN hd))
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_normal_right.mp hxM
    have haZ : a ∈ (center A).map A.subtype := by
      refine ⟨⟨a, ha⟩, mem_center_iff.mpr ?_, rfl⟩
      intro c
      apply Subtype.ext
      apply mul_right_cancel (b := b)
      calc
        (c : P) * a * b = (c : P) * (a * b) := mul_assoc _ _ _
        _ = (a * b) * c := hx c (hAN c.property)
        _ = a * c * b := by rw [mul_assoc, ← hc hb c c.property, ← mul_assoc]
    exact B.mul_mem (show a ∈ B from (hiB.symm ▸ haZ : a ∈ A ⊓ B).2) hb
  exact ⟨N, inferInstance, hncomm, hNc,
    isCyclic_of_injective (inclusion hCB) (inclusion_injective hCB)⟩
end Subgroup
