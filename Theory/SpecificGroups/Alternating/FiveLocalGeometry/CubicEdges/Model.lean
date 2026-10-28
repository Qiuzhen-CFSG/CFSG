module

public import Theory.SpecificGroups.Alternating.FiveLocalGeometry
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Finset.Range
/-!
# Marked cubic pairs in the natural A₅

Ten explicit three-cycles represent all cubic subgroups. Six elementary
normalizer adjustments reduce ordered pairs to the diagonal, an A₄ pair,
or an A₅-generating pair. The A₄ is identified through its actual embedding
on four letters. Small kernel-checked permutation identities supply the
edge reversal and the two triangles; their joins are proved structurally.

Source: Aschbacher, *Sporadic Groups* (1994), 47.6 and 47.10,
pp.264, 266–267.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace alternatingGroup.FiveLocalGeometry.CubicEdges

def cyclePerm (i : Fin 10) : Equiv.Perm (Fin 5) :=
  Equiv.swap (![0,0,0,0,0,0,1,1,1,2] i) (![1,1,1,2,2,3,2,2,3,3] i) *
    Equiv.swap (![1,1,1,2,2,3,2,2,3,3] i) (![2,3,4,3,4,4,3,4,4,4] i)

theorem cyclePerm_even : ∀ i, cyclePerm i ∈ alternatingGroup (Fin 5) := by
  intro i
  rw [Equiv.Perm.mem_alternatingGroup]
  revert i
  decide +kernel

def cycle (i : Fin 10) : A5 := ⟨cyclePerm i, cyclePerm_even i⟩
def C (i : Fin 10) : Subgroup A5 := zpowers (cycle i)

theorem cycle_order (i : Fin 10) : orderOf (cycle i) = 3 := by
  apply orderOf_eq_prime
  · have h : ∀ i, (cycle i) ^ 3 = 1 := by decide +kernel
    exact h i
  · have h : ∀ i, cycle i ≠ 1 := by decide +kernel
    exact h i

theorem card_C (i : Fin 10) : Nat.card (C i) = 3 := by
  rw [C, Nat.card_zpowers, cycle_order]

theorem mem_C (i : Fin 10) (x : A5) :
    x ∈ C i ↔ x = 1 ∨ x = cycle i ∨ x = (cycle i)⁻¹ := by
  have hs : ∀ i, (cycle i)^2 = (cycle i)⁻¹ := by decide +kernel
  rw [C, mem_zpowers_iff_mem_range_orderOf, cycle_order]
  simp only [Finset.range_add_one, Finset.range_zero, Finset.image_insert,
    Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false,
    pow_zero, pow_one, hs]
  tauto

theorem cubic_representative (P : Subgroup A5) (hP : Nat.card P = 3) :
    ∃ i, P = C i := by
  obtain ⟨g, hg⟩ := cubic_conjugate (MulEquiv.refl A5) (C 0) P (card_C 0) hP
  have hc : ∀ g : A5, ∃ i, g * cycle 0 * g⁻¹ = cycle i ∨
      g * cycle 0 * g⁻¹ = (cycle i)⁻¹ := by decide +kernel
  obtain ⟨i, hi⟩ := hc g
  refine ⟨i, hg.symm.trans ?_⟩
  rw [C, MonoidHom.map_zpowers]
  change zpowers (g * cycle 0 * g⁻¹) = C i
  rcases hi with hi | hi <;> simp [hi, C]

def normalizingInvolution : A5 := ⟨Equiv.swap 0 1 * Equiv.swap 3 4, by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩

def adjustment (i : Fin 10) : A5 :=
  cycle 0 ^ (![0,0,0,1,2,0,2,1,0,1] i : ℕ) *
    normalizingInvolution ^ (![0,0,1,0,1,0,0,1,1,0] i : ℕ)

def representative (i : Fin 10) : Fin 10 := ![0,1,1,1,1,5,1,1,5,5] i

theorem adjustment_maps (i : Fin 10) :
    (C 0).map (MulAut.conj (adjustment i)).toMonoidHom = C 0 ∧
    (C i).map (MulAut.conj (adjustment i)).toMonoidHom = C (representative i) := by
  have h : ∀ i, (adjustment i * cycle 0 * (adjustment i)⁻¹ = cycle 0 ∨
      adjustment i * cycle 0 * (adjustment i)⁻¹ = (cycle 0)⁻¹) ∧
      (adjustment i * cycle i * (adjustment i)⁻¹ = cycle (representative i) ∨
      adjustment i * cycle i * (adjustment i)⁻¹ = (cycle (representative i))⁻¹) := by
    decide +kernel
  have go (j k : Fin 10) (h : adjustment i * cycle j * (adjustment i)⁻¹ = cycle k ∨
      adjustment i * cycle j * (adjustment i)⁻¹ = (cycle k)⁻¹) :
      (C j).map (MulAut.conj (adjustment i)).toMonoidHom = C k := by
    rw [C, MonoidHom.map_zpowers]
    change zpowers (adjustment i * cycle j * (adjustment i)⁻¹) = _
    rcases h with h | h <;> simp [h, C]
  exact ⟨go 0 0 (h i).1, go i _ (h i).2⟩

def fourLetters : Finset (Fin 5) := {0,1,2,3}
def fourEmbedding : alternatingGroup fourLetters →* A5 := alternatingGroup.ofSubtype fourLetters

theorem mem_fourEmbedding (g : A5) : g ∈ fourEmbedding.range ↔ g.val 4 = 4 := by
  rw [fourEmbedding, alternatingGroup.mem_range_ofSubtype_iff]
  have h : ∀ g : Equiv.Perm (Fin 5), g.support ⊆ fourLetters ↔ g 4 = 4 := by
    decide +kernel
  exact h g

theorem join_model : C 0 ⊔ C 1 = fourEmbedding.range := by
  apply le_antisymm
  · apply sup_le
    · rw [C, zpowers_le]
      exact (mem_fourEmbedding _).mpr (by decide +kernel)
    · rw [C, zpowers_le]
      exact (mem_fourEmbedding _).mpr (by decide +kernel)
  · intro g hg
    have hcover : ∀ g : A5, g.val 4 = 4 → ∃ a : Fin 3, ∃ b : Fin 4,
        g = cycle 0 ^ a.val * (![1, cycle 1, (cycle 1)⁻¹,
          cycle 1 * cycle 0 * cycle 0] b) := by decide +kernel
    obtain ⟨a, b, rfl⟩ := hcover g ((mem_fourEmbedding g).mp hg)
    have hp : cycle 0 ∈ C 0 ⊔ C 1 := (le_sup_left : C 0 ≤ C 0 ⊔ C 1) (mem_zpowers _)
    have hq : cycle 1 ∈ C 0 ⊔ C 1 := (le_sup_right : C 1 ≤ C 0 ⊔ C 1) (mem_zpowers _)
    apply mul_mem
    · exact pow_mem hp _
    · fin_cases b
      · exact one_mem _
      · exact hq
      · exact inv_mem hq
      · exact mul_mem (mul_mem hq hp) hp

noncomputable def modelEquiv : ↥(C 0 ⊔ C 1) ≃* alternatingGroup (Fin 4) :=
  (MulEquiv.subgroupCongr join_model).trans
    ((MonoidHom.ofInjective (alternatingGroup.ofSubtype_injective (s := fourLetters))).symm.trans
      (Equiv.altCongrHom (Fintype.equivFinOfCardEq (by decide +kernel :
        Fintype.card fourLetters = 4))))

theorem model_card : Nat.card (C 0 ⊔ C 1 : Subgroup A5) = 12 := by
  rw [Nat.card_congr modelEquiv.toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

theorem nonedge_join : C 0 ⊔ C 5 = ⊤ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let J : Subgroup A5 := C 0 ⊔ C 5
  have hp : cycle 0 ∈ J := (le_sup_left : C 0 ≤ J) (mem_zpowers _)
  have hq : cycle 5 ∈ J := (le_sup_right : C 5 ≤ J) (mem_zpowers _)
  have ho : orderOf (cycle 0 * cycle 5) = 5 :=
    orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have h3 : 3 ∣ Nat.card J := by
    simpa only [cycle_order] using J.orderOf_dvd_natCard hp
  have h5 : 5 ∣ Nat.card J := by
    simpa only [ho] using J.orderOf_dvd_natCard (J.mul_mem hp hq)
  have h15 : 15 ∣ Nat.card J := (show Nat.Coprime 3 5 by decide).mul_dvd_of_dvd_of_dvd h3 h5
  have hb : 15 ≤ Nat.card J := Nat.le_of_dvd Nat.card_pos h15
  have hmul := J.card_mul_index
  rw [card] at hmul
  have hi : J.index ≤ 4 := by nlinarith
  change J = ⊤
  apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
  have hf := Nat.factorial_le hi
  rw [card]
  norm_num [Nat.factorial] at hf ⊢
  omega

theorem map_C_of_cycle {g : A5} {i j : Fin 10}
    (h : g * cycle i * g⁻¹ = cycle j ∨ g * cycle i * g⁻¹ = (cycle j)⁻¹) :
    (C i).map (MulAut.conj g).toMonoidHom = C j := by
  rw [C, MonoidHom.map_zpowers]
  change zpowers (g * cycle i * g⁻¹) = C j
  rcases h with h | h <;> simp [h, C]

theorem normalizer_inf_model :
    normalizer (C 0 : Set A5) ⊓ normalizer (C 1 : Set A5) = ⊥ := by
  have hc : ∀ g : A5,
      (g * cycle 0 * g⁻¹ = 1 ∨ g * cycle 0 * g⁻¹ = cycle 0 ∨
        g * cycle 0 * g⁻¹ = (cycle 0)⁻¹) →
      (g * cycle 1 * g⁻¹ = 1 ∨ g * cycle 1 * g⁻¹ = cycle 1 ∨
        g * cycle 1 * g⁻¹ = (cycle 1)⁻¹) → g = 1 := by decide +kernel
  apply eq_bot_iff.mpr
  intro g hg
  exact hc g ((mem_C _ _).mp ((hg.1 _).mp (mem_zpowers _)))
    ((mem_C _ _).mp ((hg.2 _).mp (mem_zpowers _)))

def reversal : A5 := ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩

theorem reversal_maps :
    (C 0).map (MulAut.conj reversal).toMonoidHom = C 1 ∧
    (C 1).map (MulAut.conj reversal).toMonoidHom = C 0 := by
  constructor <;> apply map_C_of_cycle <;> decide +kernel

theorem reversal_order : orderOf reversal = 2 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

def triangleMover (i : Fin 4) : A5 :=
  ⟨![Equiv.swap 1 3 * Equiv.swap 2 3, Equiv.swap 1 2 * Equiv.swap 2 3,
     Equiv.swap 2 3 * Equiv.swap 3 4, Equiv.swap 2 4 * Equiv.swap 3 4] i, by
    rw [Equiv.Perm.mem_alternatingGroup]
    have h : ∀ i : Fin 4, (![Equiv.swap 1 3 * Equiv.swap 2 3,
      Equiv.swap 1 2 * Equiv.swap 2 3, Equiv.swap 2 3 * Equiv.swap 3 4,
      Equiv.swap 2 4 * Equiv.swap 3 4] i : Equiv.Perm (Fin 5)).sign = 1 := by
      decide +kernel
    exact h i⟩

theorem triangleMover_maps (i : Fin 4) :
    (C 0).map (MulAut.conj (triangleMover i)).toMonoidHom = C (![1,3,1,2] i) ∧
    (C 1).map (MulAut.conj (triangleMover i)).toMonoidHom = C (![3,0,2,0] i) := by
  have hc : ∀ i : Fin 4,
      (triangleMover i * cycle 0 * (triangleMover i)⁻¹ = cycle (![1,3,1,2] i) ∨
      triangleMover i * cycle 0 * (triangleMover i)⁻¹ = (cycle (![1,3,1,2] i))⁻¹) ∧
      (triangleMover i * cycle 1 * (triangleMover i)⁻¹ = cycle (![3,0,2,0] i) ∨
      triangleMover i * cycle 1 * (triangleMover i)⁻¹ = (cycle (![3,0,2,0] i))⁻¹) := by
    decide +kernel
  exact ⟨map_C_of_cycle (hc i).1, map_C_of_cycle (hc i).2⟩

theorem triangle_small_join : (C 0 ⊔ C 1) ⊔ C 3 = C 0 ⊔ C 1 := by
  apply sup_eq_left.mpr
  rw [join_model, C, zpowers_le]
  exact (mem_fourEmbedding _).mpr (by decide +kernel)

theorem triangle_large_join : (C 0 ⊔ C 1) ⊔ C 2 = ⊤ := by
  let J : Subgroup A5 := C 0 ⊔ C 1
  let L : Subgroup A5 := J ⊔ C 2
  have hi : J.index = 5 := by
    have h := J.card_mul_index
    rw [card, show Nat.card J = 12 from model_card] at h
    omega
  have hd : L.index ∣ 5 := by
    simpa only [hi] using (index_dvd_of_le (show J ≤ L from le_sup_left))
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with h | h
  · exact Subgroup.index_eq_one.mp h
  · have he : J = L := by
      by_contra hne
      have hs := index_strictAnti (lt_of_le_of_ne (show J ≤ L from le_sup_left) hne)
      omega
    have hc : cycle 2 ∈ J := he ▸ (show cycle 2 ∈ L from
      (le_sup_right : C 2 ≤ L) (mem_zpowers _))
    have hf : (cycle 2).val 4 = 4 := (mem_fourEmbedding _).mp (join_model ▸ hc)
    have hn : (cycle 2).val 4 ≠ 4 := by decide +kernel
    exact (hn hf).elim

end alternatingGroup.FiveLocalGeometry.CubicEdges
