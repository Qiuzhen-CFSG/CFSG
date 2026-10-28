module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair
public import Theory.GroupTheory.SubgroupClosureFinite
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Tactic.FinCases

/-!
# A noncyclic three-subgroup in the actual J₂ carrier

For the defining generators a and b, set x = (abab⁻¹)⁴ and y = gbg⁻¹,
where g is the word `babbaabbabababbababbababbbbabb`. These elements commute
and have cube one. Their nine normal forms xⁱyʲ, for 0 ≤ i,j < 3, have
distinct images of point zero. Right multiplication by either generator
permutes these normal forms, so they exhaust the generated subgroup.
It has order nine and exponent three, and is therefore noncyclic.

The permutation calculations use the kernel-checked lookup tables for the
exact carrier. Source for a and b: R. A. Wilson et al., ATLAS of Finite
Group Representations, `J2G1-p100B0`; original data and attribution remain
in `Theory/SpecificGroups/LeechRelated/AtlasCarriers/J2/source/`.
This witness supplies the J₂ input to the comparison of Aschbacher–Smith,
1.1.5(3)(f), printed pp.501–503, with 15.4.20, printed p.1164.
-/

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels
namespace JankoTwoWitness

open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair

def word {G : Type*} [Group G] (a b : G) : G :=
  b * a * b * b * a * a * b * b * a * b * a * b * a * b * b *
    a * b * a * b * b * a * b * a * b * b * b * b * a * b * b

def x : Carrier := (a * b * a * b⁻¹) ^ 4
def g : Carrier := word a b
def y : Carrier := g * b * g⁻¹

theorem x_cube : x ^ 3 = 1 := by
  simpa only [x, ← pow_mul] using comm_word_pow_twelve

theorem y_cube : y ^ 3 = 1 := by
  simpa only [MulAut.conj_apply, y] using
    (map_pow (MulAut.conj g) b 3).symm.trans
      ((congrArg (MulAut.conj g) b_pow_three).trans (map_one _))

set_option maxRecDepth 20000 in
theorem xy_commute : Commute x y := by
  apply Subtype.ext
  change (generatorA * generatorB * generatorA * generatorB⁻¹) ^ 4 *
      (word generatorA generatorB * generatorB * (word generatorA generatorB)⁻¹) =
    (word generatorA generatorB * generatorB * (word generatorA generatorB)⁻¹) *
      (generatorA * generatorB * generatorA * generatorB⁻¹) ^ 4
  rw [generatorA_eq_table, generatorB_eq_table]
  decide +kernel

def nf (i : Fin 3 × Fin 3) : Carrier := x ^ i.1.val * y ^ i.2.val
def images : Fin 3 → Fin 3 → Fin 100 :=
  ![![0, 39, 88], ![61, 14, 34], ![21, 77, 74]]

set_option maxRecDepth 20000 in
theorem nf_images : ∀ i : Fin 3 × Fin 3, inclusion (nf i) 0 = images i.1 i.2 := by
  change ∀ i : Fin 3 × Fin 3,
    (((generatorA * generatorB * generatorA * generatorB⁻¹) ^ 4) ^ i.1.val *
      (word generatorA generatorB * generatorB * (word generatorA generatorB)⁻¹) ^
        i.2.val) 0 = images i.1 i.2
  rw [generatorA_eq_table, generatorB_eq_table]
  decide +kernel

theorem nf_injective : Function.Injective nf := by
  have hinj : Function.Injective (fun i : Fin 3 × Fin 3 => images i.1 i.2) := by
    decide +kernel
  intro i j hij
  apply hinj
  simpa only [nf_images] using congrArg (fun z : Carrier => inclusion z 0) hij

def generators : Fin 2 → Carrier := ![x, y]
def P : Subgroup Carrier := Subgroup.closure (Set.range generators)

theorem nf_mem (i : Fin 3 × Fin 3) : nf i ∈ P := by
  have hx : x ∈ P := Subgroup.subset_closure (show x ∈ Set.range generators from ⟨0, rfl⟩)
  have hy : y ∈ P := Subgroup.subset_closure (show y ∈ Set.range generators from ⟨1, rfl⟩)
  exact P.mul_mem (P.pow_mem hx _) (P.pow_mem hy _)

theorem pow_fin_succ (z : Carrier) (hz : z ^ 3 = 1) (i : Fin 3) :
    z ^ i.val * z = z ^ (i + 1 : Fin 3).val := by
  fin_cases i
  · change z ^ 0 * z = z ^ 1
    simp
  · change z ^ 1 * z = z ^ 2
    exact (pow_succ z 1).symm
  · change z ^ 2 * z = z ^ 0
    simpa only [← pow_succ, pow_zero] using hz

def next (i : Fin 3 × Fin 3) (t : Fin 2) : Fin 3 × Fin 3 :=
  if t = 0 then (i.1 + 1, i.2) else (i.1, i.2 + 1)
def prev (i : Fin 3 × Fin 3) (t : Fin 2) : Fin 3 × Fin 3 :=
  if t = 0 then (i.1 - 1, i.2) else (i.1, i.2 - 1)

theorem nf_next (i : Fin 3 × Fin 3) (t : Fin 2) :
    nf i * generators t = nf (next i t) := by
  fin_cases t
  · change (x ^ i.1.val * y ^ i.2.val) * x = x ^ (i.1 + 1 : Fin 3).val * y ^ i.2.val
    rw [mul_assoc, ← (xy_commute.pow_right i.2.val).eq, ← mul_assoc,
      pow_fin_succ x x_cube]
  · change (x ^ i.1.val * y ^ i.2.val) * y = x ^ i.1.val * y ^ (i.2 + 1 : Fin 3).val
    rw [mul_assoc, pow_fin_succ y y_cube]

theorem mem_range_nf {z : Carrier} (hz : z ∈ P) : z ∈ Set.range nf :=
  Theory.GroupTheory.SubgroupEnumeration.closure_range_subset_range_of_transitions
    generators nf (0, 0) next prev (by simp [nf]) nf_next (by decide +kernel) hz

theorem card_P : Nat.card P = 9 := by
  let f : (Fin 3 × Fin 3) → P := fun i => ⟨nf i, nf_mem i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact nf_injective (congrArg Subtype.val hij)
    · intro z
      obtain ⟨i, hi⟩ := mem_range_nf z.property
      exact ⟨i, Subtype.ext hi⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp only [Nat.card_prod, Nat.card_fin]

theorem nf_cube (i : Fin 3 × Fin 3) : nf i ^ 3 = 1 := by
  rw [nf, (xy_commute.pow_pow i.1.val i.2.val).mul_pow]
  have hx : (x ^ i.1.val) ^ 3 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, x_cube, one_pow]
  have hy : (y ^ i.2.val) ^ 3 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, y_cube, one_pow]
  rw [hx, hy, one_mul]

theorem P_cube (z : P) : z ^ 3 = 1 := by
  apply Subtype.ext
  obtain ⟨i, hi⟩ := mem_range_nf z.property
  change z.val ^ 3 = 1
  rw [← hi, nf_cube]

theorem not_cyclic_P : ¬ IsCyclic P := by
  intro hc
  let := hc
  obtain ⟨z, hz⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P)
  have hd : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one (P_cube z)
  rw [hz, card_P] at hd
  exact (by decide : ¬ 9 ∣ 3) hd

end JankoTwoWitness

/-- The fixed ATLAS J₂ carrier contains a noncyclic subgroup of order a power of three. -/
public theorem j2_noncyclic_three_subgroup :
    ∃ P : Subgroup Sporadic.LeechRelated.J2.Carrier, IsPGroup 3 P ∧ ¬ IsCyclic P := by
  exact ⟨JankoTwoWitness.P, IsPGroup.of_card (n := 2) JankoTwoWitness.card_P,
    JankoTwoWitness.not_cyclic_P⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels
