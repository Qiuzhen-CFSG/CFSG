module

public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# The actual elementary join of a plane and independent commuting lifts

An elementary plane and two commuting involutions centralizing it generate
an elementary group. Independent images of the involutions modulo the
given homomorphism kernel make its order sixteen and identify its kernel
intersection with the original plane. The conclusion retains the literal
subgroup join used by the HS source assembly.
-/

public section
open Subgroup
namespace CFSG.Quasithin.HigmanSims

private theorem zpowers_two_cases {K : Type*} [Group K] {x y : K}
    (hx : x ^ 2 = 1) (hx1 : x ≠ 1) (hy : y ∈ zpowers x) : y = 1 ∨ y = x := by
  classical
  have ho : orderOf x = 2 := orderOf_eq_prime hx hx1
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hx⟩
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, ho] at hy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
  have hi2 : i < 2 := Finset.mem_range.mp hi
  interval_cases i <;> simp

/-- Two independent commuting square-one lifts extend the actual kernel
plane to an elementary sixteen-group, meeting the kernel in that plane. -/
theorem elementary_plane_join
    {G K : Type*} [Group G] [Finite G] [Group K]
    (f : G →* K) (W : Subgroup G) [IsElementaryAbelian 2 W]
    (hW4 : Nat.card W = 4) (hWker : W ≤ f.ker)
    (a b : G) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : Commute a b)
    (haW : a ∈ centralizer (W : Set G)) (hbW : b ∈ centralizer (W : Set G))
    (hfa : f a ≠ 1) (hfb : f b ≠ 1) (hfab : f a ≠ f b) :
    let A := W ⊔ (zpowers a ⊔ zpowers b)
    IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧ A ⊓ f.ker = W := by
  let N := W ⊔ zpowers a
  let A := N ⊔ zpowers b
  have hfa2 : f a ^ 2 = 1 := by rw [← map_pow, ha, map_one]
  have hfb2 : f b ^ 2 = 1 := by rw [← map_pow, hb, map_one]
  have hfbout : f b ∉ zpowers (f a) := by
    intro he
    rcases zpowers_two_cases hfa2 hfa he with hh | hh
    · exact hfb hh
    · exact hfab hh.symm
  have hNmap : N.map f = zpowers (f a) := by
    rw [Subgroup.map_sup, (map_eq_bot_iff W).mpr hWker, MonoidHom.map_zpowers, bot_sup_eq]
  have haout : a ∉ W := fun haW => hfa (hWker haW)
  have hbout : b ∉ N := fun hbN =>
    hfbout (hNmap ▸ mem_map_of_mem f hbN)
  have hbza : b ∈ centralizer (zpowers a : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
    exact mem_centralizer_singleton_iff.mpr hab.eq.symm
  have hbN : b ∈ centralizer (N : Set G) := by
    have hh : zpowers b ≤ centralizer (N : Set G) := le_centralizer_iff.mpr
      (sup_le (le_centralizer_iff.mp (zpowers_le.mpr hbW))
        (le_centralizer_iff.mp (zpowers_le.mpr hbza)))
    exact hh (mem_zpowers b)
  let : IsElementaryAbelian 2 (zpowers a) := IsElementaryAbelian.zpowers_of_pow_eq_one ha
  let : IsElementaryAbelian 2 (zpowers b) := IsElementaryAbelian.zpowers_of_pow_eq_one hb
  let : IsElementaryAbelian 2 N :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr haW)
  have hAe : IsElementaryAbelian 2 A :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hbN)
  have hNc : Nat.card N = 8 := by
    rw [card_sup_zpowers_of_normalizing_involution W a ha haout
      (centralizer_le_normalizer _ haW), hW4]
  have hAc : Nat.card A = 16 := by
    rw [card_sup_zpowers_of_normalizing_involution N b hb hbout
      (centralizer_le_normalizer _ hbN), hNc]
  have hmap : Nat.card (A.map f) = 4 := by
    rw [Subgroup.map_sup, hNmap, MonoidHom.map_zpowers]
    have hbfa : f b ∈ centralizer (zpowers (f a) : Set K) := by
      rw [zpowers_eq_closure, centralizer_closure]
      exact mem_centralizer_singleton_iff.mpr (hab.map f).eq.symm
    rw [card_sup_zpowers_of_normalizing_involution (zpowers (f a)) (f b) hfb2 hfbout
      (centralizer_le_normalizer _ hbfa), Nat.card_zpowers, orderOf_eq_prime hfa2 hfa]
  have hIc : Nat.card (A ⊓ f.ker : Subgroup G) = 4 := by
    have hh := (f.ker.subgroupOf A).card_mul_index
    change Nat.card (f.ker.subgroupOf A) * f.ker.relIndex A = Nat.card A at hh
    rw [relIndex_ker, hmap, hAc] at hh
    have hc : Nat.card (f.ker.subgroupOf A) = 4 := by omega
    rw [← card_subtype A (f.ker.subgroupOf A), subgroupOf_map_subtype, inf_comm] at hc
    exact hc
  have hi : A ⊓ f.ker = W := (eq_of_le_of_card_ge
    (le_inf (le_sup_left.trans le_sup_left) hWker) (by rw [hIc, hW4])).symm
  have heq : W ⊔ (zpowers a ⊔ zpowers b) = A := (sup_assoc W (zpowers a) (zpowers b)).symm
  dsimp only
  rw [heq]
  exact ⟨hAe, hAc, hi⟩

end CFSG.Quasithin.HigmanSims
