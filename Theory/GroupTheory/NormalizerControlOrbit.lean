module

public import Theory.GroupTheory.CommutatorOrbitCard

/-!
# Normalizer control from a commutator orbit bound

Suppose every subgroup of A of order greater than two controls its normalizer.
If B ≤ A has order greater than four and [U,B] has order at most two, then U
normalizes A. For each u in U, orbit-stabilizer gives |C_B(u)| ≥ |B|/2 > 2;
normalizer control for C_B(u) then puts u in N(A).

This is the orbit argument in Aschbacher--Smith, proof of 12.9.1,
printed p.864 of `refs/quasithin.pdf`.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A commutator contained in an order-two subgroup forces normalizer control. -/
theorem normalizes_of_order_two_commutator_and_normalizer_control {U A B Z : Subgroup G} (hBA : B ≤ A) (hbig : 4 < Nat.card B)
    (hline : Nat.card Z = 2) (hcomm : ⁅U, B⁆ ≤ Z)
    (control : ∀ C : Subgroup G, C ≤ A → 2 < Nat.card C →
      normalizer (C : Set G) ≤ normalizer (A : Set G)) :
    U ≤ normalizer (A : Set G) := by
  intro u hu
  let C := B ⊓ centralizer ({u} : Set G)
  have hC : 2 < Nat.card C := by
    have hcount := card_le_commutator_card_mul_centralizer B u
    have hcom : ⁅B, zpowers u⁆ ≤ Z := by
      rw [commutator_comm]
      exact (commutator_mono (zpowers_le.mpr hu) le_rfl).trans hcomm
    have hcomcard : Nat.card (⁅B, zpowers u⁆ : Subgroup G) ≤ 2 := by
      rw [← hline]
      exact Nat.card_le_card_of_injective (inclusion hcom) (inclusion_injective _)
    have hccard : Nat.card ((centralizer ({u} : Set G)).subgroupOf B) = Nat.card C := by
      have he : (centralizer ({u} : Set G)).subgroupOf B = C.subgroupOf B := by
        ext x
        change _ ↔ x.val ∈ B ∧ _
        exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩
      rw [he]
      exact Nat.card_congr (subgroupOfEquivOfLe (show C ≤ B from inf_le_left)).toEquiv
    rw [hccard] at hcount
    have hcount' := hcount.trans (Nat.mul_le_mul_right (Nat.card C) hcomcard)
    omega
  have huC : u ∈ centralizer (C : Set G) := by
    apply mem_centralizer_iff.mpr
    intro c hc
    exact mem_centralizer_singleton_iff.mp hc.2
  exact control C (inf_le_left.trans hBA) hC (Subgroup.centralizer_le_normalizer _ huC)


end Subgroup
