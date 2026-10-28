module
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootSubgroups
public import Theory.GroupTheory.SubgroupProductCard

/-!
# Counting elementary subgroups inside the Ree root section

GLS3 Lemma 3.3.9 finishes by comparing intersections with two seven-coordinate
subgroups of the nine-coordinate subgroup D. The square calculations put each
intersection in a five-coordinate subgroup. If an elementary subgroup has
order above q^5, the set-product formula forces nonidentity intersections with
both Y₁X₂ and X₆Y₇. Their commutation forces the first intersection into X₂ and
makes the intersection with Y₁ trivial. The X₂ centralizer lies in an
eight-coordinate subgroup, and the same counting formula gives a contradiction.

We use the actual set-product cardinal formula, so no absolute or relative
normality is silently assumed. Maximality of the elementary subgroup and
containment of the middle center are also unnecessary. All remaining root
calculations are explicit in `RootCalculationFacts`; this conditional counting
result is consumed by `ElementaryTwoBound.card_le_of_root_calculations`.

Source: GLS3, Lemma 3.3.9, printed pp.134–135,
`refs/KGroup/GLS3/chapter3.tex`. Here q is the coefficient-field order, which
GLS denotes q². Guralnick–Malle, *Classification of 2F-modules, II*, Table 13
and Lemma 8.8 use this rank calculation.
-/

public section
namespace ReeF4.ElementaryTwoBound
open Subgroup
open scoped Pointwise
open scoped IsMulCommutative

private theorem product_card_le {G : Type*} [Group G] [Finite G]
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

/-- The two-section counting step; no subgroup is assumed normal. -/
private theorem card_le_of_disjoint_section {G : Type*} [Group G] [Finite G]
    (E P L A T : Subgroup G) (q s r t : ℕ) (hq : 0 < q)
    (hEL : E ≤ L) (hPL : P ≤ L) (hET : E ⊓ P ≤ T) (hAT : A ≤ T)
    (hdisj : E ⊓ A = ⊥)
    (hP : Nat.card P = q ^ s) (hL : Nat.card L = q ^ (s + r))
    (hA : Nat.card A = q ^ r) (hT : Nat.card T = q ^ t) :
    Nat.card E ≤ q ^ t := by
  have h1 := product_card_le E P L hEL hPL
  rw [hP, hL] at h1
  have h2 := product_card_le (E ⊓ P) A T hET hAT
  have hi : (E ⊓ P) ⊓ A = ⊥ :=
    le_antisymm ((inf_le_inf inf_le_left le_rfl).trans hdisj.le) bot_le
  rw [hi, card_bot, mul_one, hA, hT] at h2
  apply Nat.le_of_mul_le_mul_right (c := q ^ (s + r))
  calc
    Nat.card E * q ^ (s + r) = (Nat.card E * q ^ s) * q ^ r := by
      rw [pow_add, mul_assoc]
    _ ≤ (q ^ (s + r) * Nat.card (E ⊓ P : Subgroup G)) * q ^ r :=
      Nat.mul_le_mul_right _ h1
    _ = q ^ (s + r) * (Nat.card (E ⊓ P : Subgroup G) * q ^ r) := mul_assoc _ _ _
    _ ≤ q ^ (s + r) * q ^ t := Nat.mul_le_mul_left _ h2
    _ = q ^ t * q ^ (s + r) := mul_comm _ _
  exact pow_pos hq _

/-- The second half of GLS3 Lemma 3.3.9 from the literal root calculations. -/
theorem card_le_in_D_of_root_calculations (m : ℕ) (h : RootCalculationFacts m)
    (E : Subgroup (Model m)) (hED : E ≤ D m) (hE : IsElementaryAbelian 2 E) :
    Nat.card E ≤ 2 ^ (5 * (2 * m + 1)) := by
  let := hE
  let q := 2 ^ (2 * m + 1)
  have hq : 0 < q := pow_pos (by decide) _
  have hT₁ : E ⊓ D₁ m ≤ T₁ m := by
    intro x hx
    exact h.square_D₁ x hx.2 (elemPow_eq_one_of_isElementaryAbelian x hx.1)
  have hT₂ : E ⊓ D₂ m ≤ T₂ m := by
    intro x hx
    exact h.square_D₂ x hx.2 (elemPow_eq_one_of_isElementaryAbelian x hx.1)
  suffices Nat.card E ≤ q ^ 5 by
    simpa only [q, ← pow_mul, Nat.mul_comm (2 * m + 1) 5] using this
  by_contra hlarge
  have hleft : E ⊓ left m ≠ ⊥ := by
    intro he
    exact hlarge (card_le_of_disjoint_section E (D₁ m) (D m) (left m) (T₁ m)
      q 7 2 5 hq hED le_sup_left hT₁ le_sup_left he
      h.card_D₁ h.card_D h.card_left h.card_T₁)
  have hright : E ⊓ right m ≠ ⊥ := by
    intro he
    have hD₂ : D₂ m ≤ D m :=
      sup_le (le_sup_right.trans le_sup_left) le_sup_right
    exact hlarge (card_le_of_disjoint_section E (D₂ m) (D m) (right m) (T₂ m)
      q 7 2 5 hq hED hD₂ hT₂ le_sup_right he
      h.card_D₂ h.card_D h.card_right h.card_T₂)
  obtain ⟨e, he⟩ := ne_bot_iff_exists_ne_one.mp hleft
  obtain ⟨f, hf⟩ := ne_bot_iff_exists_ne_one.mp hright
  have he' : (e : Model m) ≠ 1 := fun h => he (Subtype.ext h)
  have hf' : (f : Model m) ≠ 1 := fun h => hf (Subtype.ext h)
  have hcomm (a b : Model m) (ha : a ∈ E) (hb : b ∈ E) : Commute a b :=
    congrArg (fun z : E => (z : Model m)) (mul_comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have heX : (e : Model m) ∈ X m 1 :=
    h.cross_commute e e.property.2 he' f f.property.2 hf'
      (hcomm e f e.property.1 f.property.1)
  have hEY : E ⊓ Y m 0 = ⊥ := by
    apply le_antisymm _ bot_le
    intro y hy
    by_cases hy1 : y = 1
    · exact mem_bot.mpr hy1
    · have hyX := h.cross_commute y ((show Y m 0 ≤ left m from le_sup_left) hy.2)
        hy1 f f.property.2 hf' (hcomm y f hy.1 f.property.1)
      exact h.disjoint_Y₁_X₂.le ⟨hy.2, hyX⟩
  have hEK : E ≤ K m := by
    intro x hx
    apply h.centralizer_X₂ e heX he'
    refine ⟨hED hx, mem_centralizer_iff.mpr ?_⟩
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact (hcomm e x e.property.1 hx).eq
  exact hlarge (card_le_of_disjoint_section E (D₁ m) (K m) (Y m 0) (T₁ m)
    q 7 1 5 hq hEK le_sup_left hT₁ (le_sup_left.trans le_sup_left) hEY
    h.card_D₁ h.card_K (by simpa only [pow_one] using h.card_Y₁) h.card_T₁)

end ReeF4.ElementaryTwoBound
