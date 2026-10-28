module

public import Theory.Mathieu.M22.Properties.HexadExtension
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.KernelGeometry
public import Theory.GroupAction.SimpleCosets
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# Ordinary maximality of order-384 hexad subgroups

A subgroup of order 384 containing the pointwise hexad kernel has index
fifteen in the hexad stabilizer. Every intermediate subgroup still contains
the kernel, so its index is also the index of a subgroup of the genuine A₆
quotient. Simplicity and the faithful coset action exclude indices three
and five. This proves ordinary subgroup maximality.

Source motivation: Aschbacher–Smith 13.8.21(2), printed p.956 (PDF p.973).
The order and placement hypotheses must be discharged separately.
-/

public section

open Subgroup MulAction
open scoped Pointwise
namespace Sporadic.Mathieu.M22SolvableSylow

set_option maxRecDepth 2048 in
theorem isCoatom_of_card_384 {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (X : Subgroup M22) (hX : X ≤ stabilizer M22 B)
    (hK : m22HexadPointwiseKernel B ≤ X) (hc : Nat.card X = 384) :
    IsCoatom (X.subgroupOf (stabilizer M22 B)) := by
  let L := X.subgroupOf (stabilizer M22 B)
  have hL : Nat.card L = 384 :=
    (Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv).trans hc
  have hi : L.index = 15 := by
    have hm := L.card_mul_index
    rw [hL, m22Hexad_stabilizer_card hB] at hm
    omega
  let f : stabilizer M22 B →* alternatingGroup (Fin 6) :=
    (m22HexadQuotientAlternatingEquiv hB).toMonoidHom.comp
      (QuotientGroup.mk' (m22SetAction B).ker)
  have hf : Function.Surjective f :=
    (m22HexadQuotientAlternatingEquiv hB).surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker ≤ L := by
    rw [show f.ker = (m22SetAction B).ker by
      dsimp [f]
      rw [MonoidHom.ker_mulEquiv_comp, QuotientGroup.ker_mk']]
    intro u hu
    exact hK ⟨u, hu, rfl⟩
  have hA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  let := alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 6))
  refine ⟨?_, ?_⟩
  · intro he
    change L = ⊤ at he
    rw [he, index_top] at hi
    contradiction
  · intro Y hY
    change L < Y at hY
    have hd := index_dvd_of_le hY.le
    rw [hi] at hd
    have hd' : Y.index ∈ (15 : ℕ).divisors := Nat.mem_divisors.mpr ⟨hd, by decide⟩
    have hdiv : (15 : ℕ).divisors = {1, 3, 5, 15} := by decide +kernel
    rw [hdiv] at hd'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd'
    rcases hd' with h1 | h3 | h5 | h15
    · exact index_eq_one.mp h1
    · have hmap : (Y.map f).index = 3 := (Y.index_map_eq hf (hk.trans hY.le)).trans h3
      have hn : Y.map f ≠ ⊤ := by intro he; rw [he, index_top] at hmap; contradiction
      have he := (Y.map f).card_dvd_factorial_index_of_simple hn
      rw [hA, hmap] at he
      norm_num [Nat.factorial] at he
    · have hmap : (Y.map f).index = 5 := (Y.index_map_eq hf (hk.trans hY.le)).trans h5
      have hn : Y.map f ≠ ⊤ := by intro he; rw [he, index_top] at hmap; contradiction
      have he := (Y.map f).card_dvd_factorial_index_of_simple hn
      rw [hA, hmap] at he
      norm_num [Nat.factorial] at he
    · have hl := index_strictAnti hY
      rw [hi, h15] at hl
      exact (lt_irrefl _ hl).elim

end Sporadic.Mathieu.M22SolvableSylow
