module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.NormNum

/-!
# The alternating complement on four fixed letters

Permutations supported on a finite set commute with every permutation fixing
that set pointwise. On four letters their even subgroup is the literal A₄;
adjoining any transposition supported there gives the full supported S₄.

This is the concrete complement construction used in original 2.4.36, where
the four fixed letters include the two letters of the distinguished outer
transposition in S₈. All identifications preserve the actual ambient embedding.
-/

@[expose] public section

open Equiv Subgroup

namespace Theory.SpecificGroups.SymmetricEight.FourPointComplement

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- All permutations supported on the selected letters. -/
def symmetric (P : Finset α) : Subgroup (Perm α) :=
  (Perm.ofSubtype : Perm P →* Perm α).range

/-- The literal embedding of the alternating group on the selected letters. -/
def embedding (P : Finset α) : alternatingGroup P →* Perm α :=
  (Perm.ofSubtype : Perm P →* Perm α).comp (alternatingGroup P).subtype

/-- The even permutations supported on the selected letters. -/
def alternating (P : Finset α) : Subgroup (Perm α) :=
  (embedding P).range

omit [Fintype α] in
theorem embedding_injective (P : Finset α) : Function.Injective (embedding P) :=
  Perm.ofSubtype_injective.comp Subtype.val_injective

theorem alternating_eq (P : Finset α) :
    alternating P = symmetric P ⊓ alternatingGroup α := by
  rw [alternating, embedding, MonoidHom.range_comp, Subgroup.range_subtype,
    alternatingGroup.map_ofSubtype]
  rfl

theorem alternating_le (P : Finset α) : alternating P ≤ alternatingGroup α := by
  rw [alternating_eq]
  exact inf_le_right

theorem alternating_le_symmetric (P : Finset α) : alternating P ≤ symmetric P := by
  rw [alternating_eq]
  exact inf_le_left

theorem mem_symmetric_iff (P : Finset α) (g : Perm α) :
    g ∈ symmetric P ↔ g.support ⊆ P := by
  exact Perm.mem_range_ofSubtype_iff

theorem symmetric_le_centralizer (P : Finset α) (L : Subgroup (Perm α))
    (hfix : ∀ g ∈ L, ∀ x ∈ P, g x = x) :
    symmetric P ≤ Subgroup.centralizer (L : Set (Perm α)) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hdis : Perm.Disjoint g l := by
    rw [Perm.disjoint_iff_eq_or_eq]
    intro x
    by_cases hx : x ∈ P
    · exact Or.inr (hfix l hl x hx)
    · left
      exact Perm.notMem_support.mp fun h => hx ((mem_symmetric_iff P g).mp hg h)
  exact hdis.commute.eq.symm

theorem alternating_le_centralizer (P : Finset α) (L : Subgroup (Perm α))
    (hfix : ∀ g ∈ L, ∀ x ∈ P, g x = x) :
    alternating P ≤ Subgroup.centralizer (L : Set (Perm α)) :=
  (alternating_le_symmetric P).trans (symmetric_le_centralizer P L hfix)

theorem symmetric_le_normalizer (P : Finset α) :
    symmetric P ≤ Subgroup.normalizer (alternating P : Set (Perm α)) := by
  rw [alternating_eq]
  exact (le_inf (symmetric P).le_normalizer Subgroup.le_normalizer_of_normal).trans
    Subgroup.inf_normalizer_le_normalizer_inf

omit [Fintype α] in
theorem swap_mem_symmetric (P : Finset α) {a b : α} (ha : a ∈ P) (hb : b ∈ P) :
    Equiv.swap a b ∈ symmetric P := by
  refine ⟨Equiv.swap (⟨a, ha⟩ : P) ⟨b, hb⟩, ?_⟩
  exact Perm.ofSubtype_swap_eq _ _

theorem swap_normalizes (P : Finset α) {a b : α} (ha : a ∈ P) (hb : b ∈ P) :
    Equiv.swap a b ∈ Subgroup.normalizer (alternating P : Set (Perm α)) :=
  symmetric_le_normalizer P (swap_mem_symmetric P ha hb)

/-- An odd transposition supplies precisely the missing sign coset. -/
theorem join_swap_eq_symmetric (P : Finset α) {a b : α}
    (ha : a ∈ P) (hb : b ∈ P) (hab : a ≠ b) :
    alternating P ⊔ zpowers (Equiv.swap a b) = symmetric P := by
  have ht : Equiv.swap a b ∈ symmetric P := swap_mem_symmetric P ha hb
  apply le_antisymm
  · exact sup_le (alternating_le_symmetric P) (zpowers_le.mpr ht)
  · intro g hg
    have hm : ∀ k, k ∈ symmetric P → Perm.sign k = 1 →
        k ∈ alternating P ⊔ zpowers (Equiv.swap a b) := by
      intro k hk hsign
      apply (le_sup_left : alternating P ≤ alternating P ⊔ zpowers (Equiv.swap a b))
      rw [alternating_eq]
      exact ⟨hk, Perm.mem_alternatingGroup.mpr hsign⟩
    rcases Int.units_eq_one_or (Perm.sign g) with hsign | hsign
    · exact hm g hg hsign
    · have heven : g * Equiv.swap a b ∈ alternating P ⊔ zpowers (Equiv.swap a b) := by
        apply hm _ ((symmetric P).mul_mem hg ht)
        simp [map_mul, hsign, Perm.sign_swap hab]
      have htjoin : Equiv.swap a b ∈ alternating P ⊔ zpowers (Equiv.swap a b) :=
        (le_sup_right : zpowers (Equiv.swap a b) ≤
          alternating P ⊔ zpowers (Equiv.swap a b)) (mem_zpowers _)
      simpa [mul_assoc] using mul_mem heven htjoin

noncomputable def alternatingEquiv (P : Finset α) (hP : P.card = 4) :
    alternating P ≃* alternatingGroup (Fin 4) :=
  (MonoidHom.ofInjective (embedding_injective P)).symm.trans
    (Equiv.altCongrHom (Fintype.equivFinOfCardEq (by simpa using hP)))

noncomputable def symmetricEquiv (P : Finset α) (hP : P.card = 4) :
    symmetric P ≃* Perm (Fin 4) :=
  (MonoidHom.ofInjective (Perm.ofSubtype_injective (p := (· ∈ P)))).symm.trans
    (Fintype.equivFinOfCardEq (by simpa using hP)).permCongrHom

noncomputable def extensionEquiv (P : Finset α) (hP : P.card = 4) {a b : α}
    (ha : a ∈ P) (hb : b ∈ P) (hab : a ≠ b) :
    (alternating P ⊔ zpowers (Equiv.swap a b) : Subgroup (Perm α)) ≃* Perm (Fin 4) :=
  (MulEquiv.subgroupCongr (join_swap_eq_symmetric P ha hb hab)).trans
    (symmetricEquiv P hP)

omit [Fintype α] in
theorem alternating_card (P : Finset α) (hP : P.card = 4) :
    Nat.card (alternating P) = 12 := by
  rw [Nat.card_congr (alternatingEquiv P hP).toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

theorem extension_card (P : Finset α) (hP : P.card = 4) {a b : α}
    (ha : a ∈ P) (hb : b ∈ P) (hab : a ≠ b) :
    Nat.card (alternating P ⊔ zpowers (Equiv.swap a b) : Subgroup (Perm α)) = 24 := by
  rw [Nat.card_congr (extensionEquiv P hP ha hb hab).toEquiv, Nat.card_perm]
  norm_num [Nat.factorial]

theorem exists_complement (P : Finset α) (hP : P.card = 4) {a b : α}
    (ha : a ∈ P) (hb : b ∈ P) (hab : a ≠ b) (L : Subgroup (Perm α))
    (hfix : ∀ g ∈ L, ∀ x ∈ P, g x = x) :
    ∃ B : Subgroup (Perm α), B ≤ alternatingGroup α ∧
      B ≤ Subgroup.centralizer (L : Set (Perm α)) ∧
      Nonempty (B ≃* alternatingGroup (Fin 4)) ∧
      Equiv.swap a b ∈ Subgroup.normalizer (B : Set (Perm α)) ∧
      Nonempty ((B ⊔ zpowers (Equiv.swap a b) : Subgroup (Perm α)) ≃* Perm (Fin 4)) :=
  ⟨alternating P, alternating_le P, alternating_le_centralizer P L hfix,
    ⟨alternatingEquiv P hP⟩, swap_normalizes P ha hb, ⟨extensionEquiv P hP ha hb hab⟩⟩

end Theory.SpecificGroups.SymmetricEight.FourPointComplement

