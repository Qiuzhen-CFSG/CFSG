module

public import Theory.SpecificGroups.SymmetricEight.ComponentMarking.PermutationFacts
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The even pointwise stabilizer of a pair in eight letters

All pointwise pair stabilizers in A₈ are conjugate and have order 360.
Their fixed points are exactly the marked pair, so their normalizers preserve
that pair. The orbit-stabilizer formula bounds each normalizer by 2 · 360.
The conjugation and cardinality assertions use the actual eight-letter action.

These permutation calculations supply the image-conjugacy and normalizer
steps in Aschbacher–Smith, K.1.1, printed p.452, via GL₄(2) ≃ A₈.
-/

@[expose] public section

open Subgroup MulAction Equiv Equiv.Perm
namespace Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings
abbrev A8 := alternatingGroup (Fin 8)

def pairFixer (a b : Fin 8) : Subgroup A8 := stabilizer A8 a ⊓ stabilizer A8 b

private theorem exists_pair_transport (a b : Fin 8) (hab : a ≠ b) :
    ∃ p : A8, p.val 0 = a ∧ p.val 1 = b := by
  let x : Fin 2 → Fin 8 := ![0, 1]
  let y : Fin 2 → Fin 8 := ![a, b]
  have hx : Function.Injective x := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [x]
  have hy : Function.Injective y := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [y]
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair x y hx hy
  have hp0 : p 0 = a := hp 0
  have hp1 : p 1 = b := hp 1
  rcases Int.units_eq_one_or (sign p) with hs | hs
  · exact ⟨⟨p, hs⟩, hp0, hp1⟩
  · refine ⟨⟨p * swap 2 3, ?_⟩, ?_, ?_⟩
    · simp [mem_alternatingGroup, hs]
    · simpa [Equiv.swap_apply_def] using hp0
    · simpa [Equiv.swap_apply_def] using hp1

theorem pairFixer_map (a b : Fin 8) (p : A8) :
    (pairFixer a b).map (MulAut.conj p).toMonoidHom = pairFixer (p.val a) (p.val b) := by
  unfold pairFixer
  rw [Subgroup.map_inf _ _ _ (MulAut.conj p).injective,
    ← stabilizer_smul_eq_stabilizer_map_conj, ← stabilizer_smul_eq_stabilizer_map_conj]
  rfl

theorem standard_card : Nat.card (pairFixer 0 1) = 360 := by
  have he : (pairFixer 0 1).map A8.subtype = alternatingGroup (Fin 8) ⊓
      (stabilizer (Perm (Fin 8)) (0 : Fin 8) ⊓ stabilizer (Perm (Fin 8)) (1 : Fin 8)) := by
    ext g
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.property, ha⟩
    · rintro ⟨ha, hg⟩
      exact ⟨⟨g, ha⟩, hg, rfl⟩
  rw [← Subgroup.card_map_of_injective A8.subtype_injective, he]
  exact Theory.SpecificGroups.SymmetricEight.ComponentMarking.card_evenPairFixer

theorem pairFixer_card (a b : Fin 8) (hab : a ≠ b) : Nat.card (pairFixer a b) = 360 := by
  obtain ⟨p, hp0, hp1⟩ := exists_pair_transport a b hab
  rw [← hp0, ← hp1, ← pairFixer_map]
  rw [Subgroup.card_map_of_injective (MulAut.conj p).injective, standard_card]

theorem pairFixer_conjugate (a b c d : Fin 8) (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ p : A8, (pairFixer a b).map (MulAut.conj p).toMonoidHom = pairFixer c d := by
  obtain ⟨p, hp0, hp1⟩ := exists_pair_transport a b hab
  obtain ⟨q, hq0, hq1⟩ := exists_pair_transport c d hcd
  refine ⟨q * p⁻¹, ?_⟩
  rw [pairFixer_map, ← hp0, ← hp1]
  simpa using congrArg₂ pairFixer hq0 hq1

private def cycle234 : A8 := ⟨swap 2 3 * swap 3 4, by simp [mem_alternatingGroup]⟩
private def cycle567 : A8 := ⟨swap 5 6 * swap 6 7, by simp [mem_alternatingGroup]⟩

private theorem fixed_standard (x : Fin 8) :
    (∀ g : A8, g ∈ pairFixer 0 1 → g.val x = x) ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro h
    have h1 := h cycle234 (by change cycle234.val 0 = 0 ∧ cycle234.val 1 = 1; decide)
    have h2 := h cycle567 (by change cycle567.val 0 = 0 ∧ cycle567.val 1 = 1; decide)
    have hc : ∀ i : Fin 8, cycle234.val i = i → cycle567.val i = i → i = 0 ∨ i = 1 :=
      by decide
    exact hc x h1 h2
  · rintro (rfl | rfl) g hg
    · exact hg.1
    · exact hg.2

private theorem normalizer_preserves_pair (p : normalizer (pairFixer 0 1 : Set A8))
    (x : Fin 8) (hx : x = 0 ∨ x = 1) : p.val.val x = 0 ∨ p.val.val x = 1 := by
  apply (fixed_standard _).mp
  intro g hg
  have hconj : p.val⁻¹ * g * p.val ∈ pairFixer 0 1 := by
    simpa using (mem_normalizer_iff.mp
      ((normalizer (pairFixer 0 1 : Set A8)).inv_mem p.property) g).mp hg
  have he := (fixed_standard x).mpr hx _ hconj
  have he' := congrArg p.val.val he
  simpa using he'

theorem standard_normalizer_card_le :
    Nat.card (normalizer (pairFixer 0 1 : Set A8)) ≤ 720 := by
  let N := normalizer (pairFixer 0 1 : Set A8)
  have horbit : orbit N (0 : Fin 8) ⊆ ({0, 1} : Set (Fin 8)) := by
    rintro x ⟨g, rfl⟩
    exact normalizer_preserves_pair g 0 (Or.inl rfl)
  have hoc : Nat.card (orbit N (0 : Fin 8)) ≤ 2 := by
    have h := Nat.card_le_card_of_injective (Set.inclusion horbit) (Set.inclusion_injective horbit)
    have ht : Nat.card ({0, 1} : Set (Fin 8)) = 2 := by rw [Nat.card_eq_fintype_card]; decide
    rwa [ht] at h
  have hsle : (stabilizer N (0 : Fin 8)).map N.subtype ≤ pairFixer 0 1 := by
    rintro g ⟨p, hp, rfl⟩
    refine ⟨hp, ?_⟩
    have h1 := normalizer_preserves_pair p 1 (Or.inr rfl)
    rcases h1 with h1 | h1
    · have he : p.val.val 1 = p.val.val 0 := h1.trans (show p.val.val 0 = 0 from hp).symm
      exact ((by decide : (1 : Fin 8) ≠ 0) (p.val.val.injective he)).elim
    · exact h1
  have hsc : Nat.card (stabilizer N (0 : Fin 8)) ≤ 360 := by
    have h := Subgroup.card_le_of_le hsle
    rwa [Subgroup.card_map_of_injective N.subtype_injective, standard_card] at h
  have hc := Nat.card_congr (orbitProdStabilizerEquivGroup N (0 : Fin 8))
  rw [Nat.card_prod] at hc
  calc
    Nat.card N = Nat.card (orbit N (0 : Fin 8)) * Nat.card (stabilizer N (0 : Fin 8)) := hc.symm
    _ ≤ 2 * 360 := Nat.mul_le_mul hoc hsc
    _ = 720 := by decide

theorem pairFixer_normalizer_card_le (a b : Fin 8) (hab : a ≠ b) :
    Nat.card (normalizer (pairFixer a b : Set A8)) ≤ 720 := by
  obtain ⟨p, hp⟩ := pairFixer_conjugate 0 1 a b (by decide) hab
  rw [← hp, ← Subgroup.map_equiv_normalizer_eq,
    Subgroup.card_map_of_injective (MulAut.conj p).injective]
  exact standard_normalizer_card_le
end Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings
