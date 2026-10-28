module

public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.LocalQuotients.Labelled
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
/-!
# Coordinates for the even 3+2+2 partition stabilizer

The restriction to the first three labels and the swap of the last two labels
identify the even partition stabilizer with S₃ × C₂. The middle pair is swapped
exactly when the signs of these two coordinates differ. We construct the inverse
by combining permutations of the three blocks. Preservation of the blocks gives
exhaustiveness; the remaining calculations involve only the 24 block permutations.
Fixing the last four labels leaves precisely the three powers of (0 1 2).

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma 5.2.20(2--3), printed pp. 656--657 (PDF pp. 673--674).
-/

open Equiv
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry

private def blockPerm (a : Perm (Fin 3)) (b c : Bool) : Perm (Fin 7) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr a
    (finSumFinEquiv.permCongr (Equiv.sumCongr
      (if b then Equiv.swap 0 1 else 1 : Perm (Fin 2))
      (if c then Equiv.swap 0 1 else 1 : Perm (Fin 2)))))

private def evenPerm (x : Perm (Fin 3) × Multiplicative (ZMod 2)) : Perm (Fin 7) :=
  blockPerm x.1 ((Equiv.Perm.sign x.1 = -1) != (x.2.toAdd = 1)) (x.2.toAdd = 1)

private theorem evenPerm_mem : ∀ x, evenPerm x ∈ heptadEvenPartition := by
  simp only [heptadEvenPartition, Subgroup.mem_inf, mem_heptadPartitionStabilizer,
    Equiv.Perm.mem_alternatingGroup]
  decide +kernel
private theorem evenPerm_mul : ∀ x y, evenPerm (x*y) = evenPerm x * evenPerm y := by decide +kernel
private theorem evenPerm_injective : Function.Injective evenPerm := by decide +kernel

private theorem maps_part (p : Perm (Fin 7)) (s : Finset (Fin 7))
    (h : p • s = s) (i : Fin 7) (hi : i ∈ s) : p i ∈ s := by
  rw [← h]
  exact (Finset.smul_mem_smul_finset_iff p).mpr hi

private theorem partition_cases (p : Perm (Fin 7)) (hp : p ∈ heptadPartitionStabilizer) :
    ∃ a b c, p = blockPerm a b c := by
  obtain ⟨ht, hm, hp⟩ := (mem_heptadPartitionStabilizer p).mp hp
  have ht' (i : Fin 3) : (p (i.castAdd 4)).val < 3 := by
    have hi : i.castAdd 4 ∈ heptadTripleLabels := by fin_cases i <;> decide
    have h := maps_part p _ ht _ hi
    simp only [heptadTripleLabels, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h <;> simp [h]
  let f : Fin 3 → Fin 3 := fun i => ⟨(p (i.castAdd 4)).val, ht' i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have he : p (i.castAdd 4) = p (j.castAdd 4) := Fin.ext (congrArg (Fin.val : Fin 3 → ℕ) hij)
    exact congrArg (Fin.val : Fin 7 → ℕ) (p.injective he)
  let a : Perm (Fin 3) := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  have h3 := maps_part p _ hm 3 (by decide : (3 : Fin 7) ∈ heptadMiddleLabels)
  have h4 := maps_part p _ hm 4 (by decide : (4 : Fin 7) ∈ heptadMiddleLabels)
  have h5 := maps_part p _ hp 5 (by decide : (5 : Fin 7) ∈ heptadPairLabels)
  have h6 := maps_part p _ hp 6 (by decide : (6 : Fin 7) ∈ heptadPairLabels)
  simp only [heptadMiddleLabels, heptadPairLabels, Finset.mem_insert,
    Finset.mem_singleton] at h3 h4 h5 h6
  refine ⟨a, decide (p 3 = 4), decide (p 5 = 6), ?_⟩
  have ha (i : Fin 3) : (a i).val = (p (i.castAdd 4)).val := rfl
  have h34 : p 3 ≠ p 4 := p.injective.ne (by decide)
  have h56 : p 5 ≠ p 6 := p.injective.ne (by decide)
  ext i
  fin_cases i
  · exact (ha 0).symm
  · exact (ha 1).symm
  · exact (ha 2).symm
  all_goals
    rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4 <;>
      rcases h5 with h5 | h5 <;> rcases h6 with h6 | h6 <;>
      simp_all <;> rfl

private theorem block_even : ∀ a b c, Perm.sign (blockPerm a b c) = 1 →
    ∃ x, evenPerm x = blockPerm a b c := by decide +kernel

private theorem evenPerm_surjective (p : heptadEvenPartition) : ∃ x, evenPerm x = p.val := by
  obtain ⟨a, b, c, he⟩ := partition_cases p.val p.property.2
  rw [he]
  apply block_even
  rw [← he]
  exact Perm.mem_alternatingGroup.mp p.property.1

private def evenHom : (Perm (Fin 3) × Multiplicative (ZMod 2)) →* heptadEvenPartition where
  toFun x := ⟨evenPerm x, evenPerm_mem x⟩
  map_one' := by apply Subtype.ext; change evenPerm 1 = 1; decide +kernel
  map_mul' x y := Subtype.ext (evenPerm_mul x y)

/-- Restriction to the first triple and the swap coordinate on the last pair. -/
public noncomputable def heptadEvenPartitionEquiv :
    heptadEvenPartition ≃* (Perm (Fin 3) × Multiplicative (ZMod 2)) :=
  (MulEquiv.ofBijective evenHom ⟨fun x y h => evenPerm_injective (congrArg Subtype.val h),
    fun p => by obtain ⟨x, hx⟩ := evenPerm_surjective p; exact ⟨x, Subtype.ext hx⟩⟩).symm

/-- The S₃ coordinate is the actual restriction to labels 0, 1, 2. -/
public theorem heptadEvenPartitionEquiv_apply_triple
    (p : heptadEvenPartition) (i : Fin 3) :
    ((heptadEvenPartitionEquiv p).1 i).castAdd 4 = p.val (i.castAdd 4) := by
  have h : ∀ x : Perm (Fin 3) × Multiplicative (ZMod 2), ∀ i : Fin 3,
      (x.1 i).castAdd 4 = evenPerm x (i.castAdd 4) := by decide +kernel
  have he := congrArg Subtype.val (heptadEvenPartitionEquiv.symm_apply_apply p)
  change evenPerm (heptadEvenPartitionEquiv p) = p.val at he
  rw [← he]
  exact h _ _

/-- The C₂ coordinate records whether labels 5 and 6 are exchanged. -/
public theorem heptadEvenPartitionEquiv_apply_pair (p : heptadEvenPartition) :
    (heptadEvenPartitionEquiv p).2.toAdd = 1 ↔ p.val 5 = 6 := by
  have h : ∀ x : Perm (Fin 3) × Multiplicative (ZMod 2),
      x.2.toAdd = 1 ↔ evenPerm x 5 = 6 := by decide +kernel
  have he := congrArg Subtype.val (heptadEvenPartitionEquiv.symm_apply_apply p)
  change evenPerm (heptadEvenPartitionEquiv p) = p.val at he
  rw [← he]
  exact h _

/-- The C₂ coordinate determines both labels of the last pair. -/
public theorem heptadEvenPartitionEquiv_apply_pair_labels (p : heptadEvenPartition) :
    p.val 5 = (if (heptadEvenPartitionEquiv p).2.toAdd = 1 then 6 else 5) ∧
    p.val 6 = (if (heptadEvenPartitionEquiv p).2.toAdd = 1 then 5 else 6) := by
  have h : ∀ x : Perm (Fin 3) × Multiplicative (ZMod 2),
      evenPerm x 5 = (if x.2.toAdd = 1 then 6 else 5) ∧
      evenPerm x 6 = (if x.2.toAdd = 1 then 5 else 6) := by decide +kernel
  have he := congrArg Subtype.val (heptadEvenPartitionEquiv.symm_apply_apply p)
  change evenPerm (heptadEvenPartitionEquiv p) = p.val at he
  rw [← he]
  exact h _

/-- Evenness determines the middle pair from the two coordinates. -/
public theorem heptadEvenPartitionEquiv_apply_middle_labels (p : heptadEvenPartition) :
    p.val 3 = (if (Perm.sign (heptadEvenPartitionEquiv p).1 = -1 ↔
        (heptadEvenPartitionEquiv p).2.toAdd = 1) then 3 else 4) ∧
    p.val 4 = (if (Perm.sign (heptadEvenPartitionEquiv p).1 = -1 ↔
        (heptadEvenPartitionEquiv p).2.toAdd = 1) then 4 else 3) := by
  have h : ∀ x : Perm (Fin 3) × Multiplicative (ZMod 2),
      evenPerm x 3 = (if (Perm.sign x.1 = -1 ↔ x.2.toAdd = 1) then 3 else 4) ∧
      evenPerm x 4 = (if (Perm.sign x.1 = -1 ↔ x.2.toAdd = 1) then 4 else 3) := by
    decide +kernel
  have he := congrArg Subtype.val (heptadEvenPartitionEquiv.symm_apply_apply p)
  change evenPerm (heptadEvenPartitionEquiv p) = p.val at he
  rw [← he]
  exact h _

public theorem heptadEvenFourFixer_le_evenPartition : heptadEvenFourFixer ≤ heptadEvenPartition := by
  intro p hp
  obtain ⟨he, hf⟩ := (mem_heptadEvenFourFixer p).mp hp
  refine ⟨he, (mem_heptadPartitionStabilizer p).mpr ?_⟩
  have h3 := hf 3 (by decide)
  have h4 := hf 4 (by decide)
  have h5 := hf 5 (by decide)
  have h6 := hf 6 (by decide)
  have ht : p • heptadTripleLabels ⊆ heptadTripleLabels := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_smul_finset.mp hj
    have ht4 : ∀ i : Fin 7, i ∉ heptadTripleLabels ↔ i ∈ heptadFourLabels := by decide +kernel
    by_contra h
    have hpi := hf (p i) ((ht4 _).mp h)
    have hii := p.injective hpi
    have : i ∈ heptadFourLabels := by simpa [hii] using (ht4 _).mp h
    exact ((ht4 _).mpr this) hi
  refine ⟨Finset.eq_of_subset_of_card_le ht (by rw [Finset.card_smul_finset]), ?_, ?_⟩
  · simp [heptadMiddleLabels, Finset.smul_finset_insert, Finset.smul_finset_singleton, h3, h4, Equiv.Perm.smul_def]
  · simp [heptadPairLabels, Finset.smul_finset_insert, Finset.smul_finset_singleton, h5, h6, Equiv.Perm.smul_def]

private theorem evenPerm_fixer : ∀ x : Perm (Fin 3) × Multiplicative (ZMod 2),
    (∀ i ∈ heptadFourLabels, evenPerm x i = i) →
    ∃ n : Fin 3, evenPerm x = (heptadTripleCycle : Perm (Fin 7)) ^ n.val := by
  decide +kernel

/-- The even pointwise stabilizer of the last four labels is the specified C₃. -/
public theorem heptadEvenFourFixer_eq_zpowers :
    heptadEvenFourFixer = Subgroup.zpowers (heptadTripleCycle : Perm (Fin 7)) := by
  apply le_antisymm
  · intro p hp
    obtain ⟨x, hx⟩ := evenPerm_surjective ⟨p, heptadEvenFourFixer_le_evenPartition hp⟩
    obtain ⟨n, hn⟩ := evenPerm_fixer x (by
      rw [hx]; exact ((mem_heptadEvenFourFixer p).mp hp).2)
    change evenPerm x = p at hx
    rw [← hx, hn]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · apply Subgroup.zpowers_le.mpr
    rw [mem_heptadEvenFourFixer]
    exact ⟨heptadTripleCycle.property, by decide +kernel⟩
end Sporadic.Mathieu.M23Geometry
