module

public import Theory.GroupAction.FiveThirtyTwoCentralizer

/-!
# Two-subgroups centralizing a five-action on an abelian group of order thirty-two

For a group action on an abelian group of order thirty-two with two-group
kernel, every two-subgroup commuting with an order-five subgroup lies in the kernel.
The five-subgroup embeds in the automorphism group; its centralizer has
order dividing fifteen, so the two-subgroup has trivial image.

This is the action-theoretic step used with the source residual configuration in
Aschbacher--Smith 14.2.21, printed p.989, and Thompson VI, printed p.630.
The centralizer bound is proved in `FiveThirtyTwoCentralizer`.
-/

open Subgroup

/-- A commuting two-subgroup acts trivially on the abelian group of order thirty-two. -/
public theorem Subgroup.two_subgroup_le_kernel_of_centralizes_five_on_thirtyTwo {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
    [IsMulCommutative V]
    (ρ : G →* MulAut V) (hk : IsPGroup 2 ρ.ker) (hV : Nat.card V = 32)
    (A D : Subgroup G) (hA : Nat.card A = 5) (hD : IsPGroup 2 D)
    (hDA : D ≤ centralizer (A : Set G)) : D ≤ ρ.ker := by
  let B := A.map ρ
  have hAfive : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hdisj : Disjoint A ρ.ker := hAfive.disjoint_of_coprime hk (by decide)
  have hinj : Function.Injective (ρ.comp A.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply eq_bot_iff.mpr
    intro a ha
    exact Subtype.ext (hdisj.le_bot ⟨a.property, ha⟩)
  have hB : Nat.card B = 5 := by
    have he : (ρ.comp A.subtype).range = A.map ρ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    change Nat.card (A.map ρ) = 5
    rw [← he, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact hA
  have hC : Nat.card (centralizer (B : Set (MulAut V))) ∣ 15 :=
    FiveThirtyTwo.centralizer_card_dvd_fifteen B hB hV
  have hle : D.map ρ ≤ centralizer (B : Set (MulAut V)) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    exact map_mul ρ a d ▸ map_mul ρ d a ▸
      congrArg ρ (mem_centralizer_iff.mp (hDA hd) a ha)
  have hd15 : Nat.card (D.map ρ) ∣ 15 := (card_dvd_of_le hle).trans hC
  have hdcard : Nat.card (D.map ρ) = 1 := by
    rcases (hD.map ρ).card_eq_or_dvd with h | h
    · exact h
    · have hf := h.trans hd15
      norm_num at hf
  have hbot : D.map ρ = ⊥ := card_eq_one.mp hdcard
  intro d hd
  exact mem_bot.mp (hbot ▸ mem_map_of_mem ρ hd)
