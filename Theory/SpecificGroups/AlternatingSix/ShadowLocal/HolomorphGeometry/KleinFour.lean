module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.HolomorphGeometry.Centralizers

/-!
# The two Klein-four subgroups of the marked D₈

The subgroups `⟨r⁴,c⟩` and `⟨r⁴,r²c⟩` are the two Klein-four
subgroups in the inner dihedral group. Conjugation by `r` exchanges them;
each has normalizer `⟨r²,b,c⟩`, of order 16, in the full model.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, pp.568–570.
-/

@[expose] public section
namespace AlternatingSix.ShadowLocal.Holomorph
open Subgroup
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 2048

instance e4_isKleinFour : IsKleinFour E4 where
  card_four := by simp [E4, C2]
  exponent_two := by simp [E4, C2, Monoid.exponent_prod]

def kleinZeroEmbedding : E4 →* Model where
  toFun i := centralEmbedding i.1 * reflection ^ i.2.toAdd.val
  map_one' := rfl
  map_mul' := by decide +kernel

def kleinOneEmbedding : E4 →* Model where
  toFun i := centralEmbedding i.1 * (rotation ^ 2 * reflection) ^ i.2.toAdd.val
  map_one' := rfl
  map_mul' := by decide +kernel

def kleinZero : Subgroup Model := kleinZeroEmbedding.range
def kleinOne : Subgroup Model := kleinOneEmbedding.range

theorem kleinZeroEmbedding_injective : Function.Injective kleinZeroEmbedding := by decide +kernel
theorem kleinOneEmbedding_injective : Function.Injective kleinOneEmbedding := by decide +kernel

noncomputable def kleinZeroEquiv : kleinZero ≃* E4 :=
  (MonoidHom.ofInjective kleinZeroEmbedding_injective).symm
noncomputable def kleinOneEquiv : kleinOne ≃* E4 :=
  (MonoidHom.ofInjective kleinOneEmbedding_injective).symm

instance kleinZero_isKleinFour : IsKleinFour kleinZero where
  card_four := (Nat.card_congr kleinZeroEquiv.toEquiv).trans IsKleinFour.card_four
  exponent_two := (Monoid.exponent_eq_of_mulEquiv kleinZeroEquiv).trans IsKleinFour.exponent_two
instance kleinOne_isKleinFour : IsKleinFour kleinOne where
  card_four := (Nat.card_congr kleinOneEquiv.toEquiv).trans IsKleinFour.card_four
  exponent_two := (Monoid.exponent_eq_of_mulEquiv kleinOneEquiv).trans IsKleinFour.exponent_two

theorem mem_kleinZero (x : Model) : x ∈ kleinZero ↔ ∃ i, kleinZeroEmbedding i = x := Iff.rfl
theorem mem_kleinOne (x : Model) : x ∈ kleinOne ↔ ∃ i, kleinOneEmbedding i = x := Iff.rfl

theorem kleinZero_eq_closure : kleinZero = closure {rotation ^ 4, reflection} := by
  apply le_antisymm
  · rintro x ⟨i, rfl⟩
    exact Subgroup.mul_mem _
      (Subgroup.pow_mem _ (subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (subset_closure (by simp)) _)
  · apply (closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨(.ofAdd 1, 1), by decide +kernel⟩
    · exact ⟨(1, .ofAdd 1), by decide +kernel⟩

theorem kleinOne_eq_closure : kleinOne = closure {rotation ^ 4, rotation ^ 2 * reflection} := by
  apply le_antisymm
  · rintro x ⟨i, rfl⟩
    exact Subgroup.mul_mem _
      (Subgroup.pow_mem _ (subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (subset_closure (by simp)) _)
  · apply (closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨(.ofAdd 1, 1), by decide +kernel⟩
    · exact ⟨(1, .ofAdd 1), by decide +kernel⟩

theorem kleinZero_le_innerD : kleinZero ≤ innerD := by
  change ∀ x : Model, x ∈ kleinZero → x ∈ innerD
  simp only [mem_kleinZero, mem_innerD]
  decide +kernel

theorem kleinOne_le_innerD : kleinOne ≤ innerD := by
  change ∀ x : Model, x ∈ kleinOne → x ∈ innerD
  simp only [mem_kleinOne, mem_innerD]
  decide +kernel

theorem kleinZero_ne_kleinOne : kleinZero ≠ kleinOne := by
  intro he
  have hc : reflection ∈ kleinZero := ⟨(1, .ofAdd 1), by decide +kernel⟩
  rw [he, mem_kleinOne] at hc
  have hn : ¬ ∃ i, kleinOneEmbedding i = reflection := by decide +kernel
  exact hn hc

/-- Conjugation is by the actual rotation in the ambient model. -/
theorem rotation_conjugates_klein :
    kleinZero.map (MulAut.conj rotation).toMonoidHom = kleinOne := by
  ext x
  simp only [mem_map_equiv, mem_kleinZero, mem_kleinOne]
  revert x
  decide +kernel

theorem normalizer_kleinZero : normalizer (kleinZero : Set Model) = natural := by
  ext x
  simp only [mem_normalizer_iff, mem_kleinZero, mem_natural]
  revert x
  decide +kernel

theorem normalizer_kleinOne : normalizer (kleinOne : Set Model) = natural := by
  ext x
  simp only [mem_normalizer_iff, mem_kleinOne, mem_natural]
  revert x
  decide +kernel

theorem card_natural : Nat.card natural = 16 := by
  rw [Nat.card_congr naturalEquiv.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
  simp [C2]

theorem card_normalizer_kleinZero : Nat.card (normalizer (kleinZero : Set Model)) = 16 := by
  rw [normalizer_kleinZero, card_natural]

theorem card_normalizer_kleinOne : Nat.card (normalizer (kleinOne : Set Model)) = 16 := by
  rw [normalizer_kleinOne, card_natural]

/-- These exhaust the Klein-four subgroups of the marked inner dihedral group. -/
theorem kleinFour_subgroups_innerD (E : Subgroup Model) [IsKleinFour E] (hED : E ≤ innerD) :
    E = kleinZero ∨ E = kleinOne := by
  classical
  obtain ⟨f⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := E4) (G₂ := E)
  let j : E4 →* Model := E.subtype.comp f.toMonoidHom
  have hj : Function.Injective j := E.subtype_injective.comp f.injective
  let a₀ : E4 := (.ofAdd 1, 1)
  let b₀ : E4 := (1, .ofAdd 1)
  let a := j a₀
  let b := j b₀
  have ha : a ≠ 1 := by
    intro h
    have he : a₀ = 1 := hj (h.trans j.map_one.symm)
    exact (by decide +kernel : a₀ ≠ 1) he
  have hb : b ≠ 1 := by
    intro h
    have he : b₀ = 1 := hj (h.trans j.map_one.symm)
    exact (by decide +kernel : b₀ ≠ 1) he
  have hab : a ≠ b := fun h => (by decide +kernel : a₀ ≠ b₀) (hj h)
  have ha2 : a ^ 2 = 1 := by
    have h : a₀ ^ 2 = 1 := by decide +kernel
    simpa only [map_pow, map_one] using congrArg j h
  have hb2 : b ^ 2 = 1 := by
    have h : b₀ ^ 2 = 1 := by decide +kernel
    simpa only [map_pow, map_one] using congrArg j h
  have hc : a * b = b * a := by
    have h : a₀ * b₀ = b₀ * a₀ := by decide +kernel
    simpa only [map_mul] using congrArg j h
  have hmem (x : Model) : x ∈ E ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
    constructor
    · intro hx
      obtain ⟨t, ht⟩ := f.surjective ⟨x, hx⟩
      have hxj : j t = x := congrArg Subtype.val ht
      rw [← hxj]
      have words : ∀ t : E4, t = 1 ∨ t = a₀ ∨ t = b₀ ∨ t = a₀ * b₀ := by decide +kernel
      rcases words t with rfl | rfl | rfl | rfl
      · exact Or.inl j.map_one
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (j.map_mul _ _)))
    · rintro (rfl | rfl | rfl | rfl)
      · exact E.one_mem
      · exact (f a₀).property
      · exact (f b₀).property
      · exact E.mul_mem (f a₀).property (f b₀).property
  have table : ∀ a b : Model, (∃ d, innerEmbedding d = a) →
      (∃ d, innerEmbedding d = b) → a ≠ 1 → b ≠ 1 → a ≠ b →
      a ^ 2 = 1 → b ^ 2 = 1 → a * b = b * a →
      ((∀ x : Model, (x = 1 ∨ x = a ∨ x = b ∨ x = a * b) ↔
        ∃ i, kleinZeroEmbedding i = x) ∨
       (∀ x : Model, (x = 1 ∨ x = a ∨ x = b ∨ x = a * b) ↔
        ∃ i, kleinOneEmbedding i = x)) := by
    decide +kernel
  rcases table a b ((mem_innerD _).mp (hED (f a₀).property))
      ((mem_innerD _).mp (hED (f b₀).property)) ha hb hab ha2 hb2 hc with h | h
  · left
    ext x
    exact (hmem x).trans (h x)
  · right
    ext x
    exact (hmem x).trans (h x)

end AlternatingSix.ShadowLocal.Holomorph
