module

public import Theory.ElementaryAbelian.Join
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.SubgroupProductCard

/-!
# Counting a central elementary replacement

Let V ≤ C ≤ U in a finite group, where V is elementary and centralizes C.
Suppose elements of U outside C have centralizer in V contained in Z, and
|U| ≤ q|C|, q|Z| ≤ |V|. Then (E ∩ C)V is elementary of order at least |E|
for every elementary E ≤ U. The proof compares the actual set products EC
and (E ∩ C)V. Neither ambient nor relative normality is required.

The literal Ree application is in `ElementaryTwoBound.Replacement`.
Source: the replacement step in GLS3 Lemma 3.3.9, printed p.135.
-/

public section
namespace Subgroup
open scoped Pointwise IsMulCommutative

private theorem replacement_product_card_le {G : Type*} [Group G] [Finite G]
    (A B L : Subgroup G) (hA : A ≤ L) (hB : B ≤ L) :
    Nat.card A * Nat.card B ≤ Nat.card L * Nat.card (A ⊓ B : Subgroup G) := by
  rw [← card_set_mul_mul_card_inf]
  apply Nat.mul_le_mul_right
  let f : ((A : Set G) * (B : Set G)) → L := fun z =>
    ⟨z, by
      obtain ⟨a, ha, b, hb, hab⟩ := z.property
      exact hab ▸ L.mul_mem (hA ha) (hB hb)⟩
  exact Nat.card_le_card_of_injective f (fun x y h =>
    Subtype.ext (congrArg (fun z : L => (z : G)) h))

/-- The source's replacement has at least the original order. The centralizer
and cardinal hypotheses concern the fixed sections, not the subgroup E. -/
theorem elementary_central_replacement {G : Type*} [Group G] [Finite G]
    (p q : ℕ) (U C V Z E : Subgroup G)
    (hCU : C ≤ U) (hVC : V ≤ C) (hCV : C ≤ centralizer (V : Set G))
    (hV : IsElementaryAbelian p V)
    (houtside : ∀ x ∈ U, x ∉ C → V ⊓ centralizer ({x} : Set G) ≤ Z)
    (hU : Nat.card U ≤ q * Nat.card C) (hVcard : q * Nat.card Z ≤ Nat.card V)
    (hEU : E ≤ U) (hE : IsElementaryAbelian p E) :
    (E ⊓ C) ⊔ V ≤ C ∧ IsElementaryAbelian p ((E ⊓ C) ⊔ V : Subgroup G) ∧
      Nat.card E ≤ Nat.card ((E ⊓ C) ⊔ V : Subgroup G) := by
  let := hE
  let := hV
  let : IsElementaryAbelian p (E ⊓ C : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  refine ⟨sup_le inf_le_right hVC, ?_, ?_⟩
  · exact IsElementaryAbelian.sup_of_le_centralizer
      (le_centralizer_iff.mp (inf_le_right.trans hCV))
  · by_cases hEC : E ≤ C
    · exact card_le_of_le ((le_inf le_rfl hEC).trans le_sup_left)
    · obtain ⟨x, hxE, hxC⟩ : ∃ x ∈ E, x ∉ C := by
        by_contra h
        apply hEC
        intro x hx
        by_contra hxC
        exact h ⟨x, hx, hxC⟩
      have hEZ : (E ⊓ C) ⊓ V ≤ Z := by
        intro y hy
        apply houtside x (hEU hxE) hxC
        refine ⟨hy.2, mem_centralizer_iff.mpr ?_⟩
        intro z hz
        obtain rfl : z = x := Set.mem_singleton_iff.mp hz
        exact setLike_mul_comm hxE hy.1.1
      have h₁ : Nat.card E ≤ q * Nat.card (E ⊓ C : Subgroup G) := by
        apply Nat.le_of_mul_le_mul_right (c := Nat.card C) _ Nat.card_pos
        calc
          Nat.card E * Nat.card C ≤
              Nat.card U * Nat.card (E ⊓ C : Subgroup G) :=
            replacement_product_card_le E C U hEU hCU
          _ ≤ (q * Nat.card C) * Nat.card (E ⊓ C : Subgroup G) :=
            Nat.mul_le_mul_right _ hU
          _ = (q * Nat.card (E ⊓ C : Subgroup G)) * Nat.card C := by ac_rfl
      have h₂ : q * Nat.card (E ⊓ C : Subgroup G) ≤
          Nat.card ((E ⊓ C) ⊔ V : Subgroup G) := by
        apply Nat.le_of_mul_le_mul_right (c := Nat.card Z) _ Nat.card_pos
        calc
          (q * Nat.card (E ⊓ C : Subgroup G)) * Nat.card Z =
              Nat.card (E ⊓ C : Subgroup G) * (q * Nat.card Z) := by ac_rfl
          _ ≤ Nat.card (E ⊓ C : Subgroup G) * Nat.card V :=
            Nat.mul_le_mul_left _ hVcard
          _ ≤ Nat.card ((E ⊓ C) ⊔ V : Subgroup G) *
              Nat.card ((E ⊓ C) ⊓ V : Subgroup G) :=
            replacement_product_card_le (E ⊓ C) V ((E ⊓ C) ⊔ V)
              le_sup_left le_sup_right
          _ ≤ Nat.card ((E ⊓ C) ⊔ V : Subgroup G) * Nat.card Z :=
            Nat.mul_le_mul_left _ (card_le_of_le hEZ)
      exact h₁.trans h₂

end Subgroup
