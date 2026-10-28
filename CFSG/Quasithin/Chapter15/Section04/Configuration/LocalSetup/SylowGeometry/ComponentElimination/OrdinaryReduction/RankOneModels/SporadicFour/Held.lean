module

public import Theory.SpecificGroups.Held.Model.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.FinCases

/-!
# A noncyclic three-subgroup in the concrete Held group

In the defining ATLAS generators, put x = (a⁻¹b⁻¹ab)² and y = g⁻¹xg,
where g = ababab⁻¹ab². The checked sixth relator gives x³ = 1, and
conjugation gives y³ = 1. Kernel reduction on all 2058 points certifies
that x and y commute. Their generated subgroup therefore has exponent
three. The images of point zero under 1, x, x², y are respectively
0, 373, 1225, 875, so that subgroup cannot be cyclic.

The action formulas are proved first for arbitrary permutations, avoiding
expansion of the large concrete lookup tables during symbolic rewriting.
The finite checks use exactly the tables of the existing Held carrier.

Source for the generators: R. A. Wilson et al., ATLAS of Finite Group
Representations, `HeG1-p2058B0`. Original data and attribution remain in
`Theory/SpecificGroups/Held/Model/Source/`. This supplies precisely the Held
subgroup witness for the comparison of Aschbacher–Smith, 1.1.5(3)(f),
printed pp.501–503, with the ordinary rank-one case on p.1164 in 15.4.20.
-/

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels
namespace HeldThreeWitness

def first {G : Type*} [Group G] (a b : G) : G := (a⁻¹ * b⁻¹ * a * b) ^ 2
def conjugator {G : Type*} [Group G] (a b : G) : G :=
  a * b * a * b * a * b⁻¹ * a * b ^ 2
def second {G : Type*} [Group G] (a b : G) : G :=
  (conjugator a b)⁻¹ * first a b * conjugator a b

theorem first_cube : (first Held.a Held.b) ^ 3 = 1 := by
  simp only [first, ← pow_mul]
  exact Held.relations 5

theorem second_cube : (second Held.a Held.b) ^ 3 = 1 := by
  have h := @conj_pow _ _ 3 (conjugator Held.a Held.b)⁻¹ (first Held.a Held.b)
  simpa only [second, inv_inv, first_cube, mul_one, inv_mul_cancel] using h

theorem map_first {G H : Type*} [Group G] [Group H] (f : G →* H) (a b : G) :
    f (first a b) = first (f a) (f b) := by
  simp only [first, map_pow, map_mul, map_inv]

theorem map_second {G H : Type*} [Group G] [Group H] (f : G →* H) (a b : G) :
    f (second a b) = second (f a) (f b) := by
  simp only [second, conjugator, first, map_pow, map_mul, map_inv]

def firstFun (i : Fin 2058) : Fin 2058 :=
  Held.atlasAFun (Held.atlasBInvFun (Held.atlasAFun (Held.atlasBFun (Held.atlasAFun (Held.atlasBInvFun (Held.atlasAFun (Held.atlasBFun (i))))))))
def conjugatorFun (i : Fin 2058) : Fin 2058 :=
  Held.atlasAFun (Held.atlasBFun (Held.atlasAFun (Held.atlasBFun (Held.atlasAFun (Held.atlasBInvFun (Held.atlasAFun (Held.atlasBFun (Held.atlasBFun (i)))))))))
def conjugatorInvFun (i : Fin 2058) : Fin 2058 :=
  Held.atlasBInvFun (Held.atlasBInvFun (Held.atlasAFun (Held.atlasBFun (Held.atlasAFun (Held.atlasBInvFun (Held.atlasAFun (Held.atlasBInvFun (Held.atlasAFun (i)))))))))
def secondFun (i : Fin 2058) : Fin 2058 :=
  conjugatorInvFun (firstFun (conjugatorFun i))

theorem first_apply {α : Type*} (a b : Equiv.Perm α) (i : α) :
    first a b i = a⁻¹ (b⁻¹ (a (b (a⁻¹ (b⁻¹ (a (b i))))))) := by
  simp only [first, pow_two, Equiv.Perm.mul_apply]

theorem conjugator_apply {α : Type*} (a b : Equiv.Perm α) (i : α) :
    conjugator a b i = a (b (a (b (a (b⁻¹ (a (b (b i)))))))) := by
  simp only [conjugator, pow_two, Equiv.Perm.mul_apply]

theorem conjugator_inv_apply {α : Type*} (a b : Equiv.Perm α) (i : α) :
    (conjugator a b)⁻¹ i = b⁻¹ (b⁻¹ (a⁻¹ (b (a⁻¹ (b⁻¹ (a⁻¹ (b⁻¹ (a⁻¹ i)))))))) := by
  simp only [conjugator, pow_two, mul_inv_rev, inv_inv, Equiv.Perm.mul_apply]

theorem atlasA_apply (i : Fin 2058) : Held.atlasA i = Held.atlasAFun i := rfl
theorem atlasAi_apply (i : Fin 2058) : Held.atlasA⁻¹ i = Held.atlasAFun i := rfl
theorem atlasB_apply (i : Fin 2058) : Held.atlasB i = Held.atlasBFun i := rfl
theorem atlasBi_apply (i : Fin 2058) : Held.atlasB⁻¹ i = Held.atlasBInvFun i := rfl

theorem first_action (i : Fin 2058) : first Held.atlasA Held.atlasB i = firstFun i := by
  rw [first_apply]
  simp only [atlasA_apply, atlasAi_apply, atlasB_apply, atlasBi_apply, firstFun]

theorem second_action (i : Fin 2058) : second Held.atlasA Held.atlasB i = secondFun i := by
  simp only [second, Equiv.Perm.mul_apply, conjugator_inv_apply, first_apply,
    conjugator_apply, atlasA_apply, atlasAi_apply, atlasB_apply, atlasBi_apply,
    secondFun, conjugatorInvFun, firstFun, conjugatorFun]

theorem allPointsByBlocks (P : Fin 2058 → Prop)
    (h : ∀ q : Fin 17, ∀ r : Fin 128,
      P ⟨(q.val * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) : ∀ i, P i := by
  intro i
  have hi := h ⟨i.val / 128, by omega⟩ ⟨i.val % 128, Nat.mod_lt _ (by decide)⟩
  have he : i.val / 128 * 128 + i.val % 128 = i.val := by omega
  simpa only [he, Nat.mod_eq_of_lt i.isLt] using hi

set_option maxRecDepth 2048 in
theorem commute_block_0 : ∀ r : Fin 128,
    firstFun (secondFun ⟨(0 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) =
      secondFun (firstFun ⟨(0 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) := by
  decide +kernel

set_option maxRecDepth 2048 in
theorem commute_block_1 : ∀ r : Fin 128,
    firstFun (secondFun ⟨(1 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) =
      secondFun (firstFun ⟨(1 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) := by
  decide +kernel

set_option maxRecDepth 2048 in
theorem commute_block_2 : ∀ r : Fin 128,
    firstFun (secondFun ⟨(2 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) =
      secondFun (firstFun ⟨(2 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) := by
  decide +kernel

set_option maxRecDepth 2048 in
theorem commute_block_3 : ∀ r : Fin 128,
    firstFun (secondFun ⟨(3 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) =
      secondFun (firstFun ⟨(3 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) := by
  decide +kernel

set_option maxRecDepth 2048 in
theorem commute_block_4 : ∀ r : Fin 128,
    firstFun (secondFun ⟨(4 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) =
      secondFun (firstFun ⟨(4 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) := by
  decide +kernel

set_option maxRecDepth 2048 in
theorem commute_block_5 : ∀ r : Fin 128,
    firstFun (secondFun ⟨(5 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) =
      secondFun (firstFun ⟨(5 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) := by
  decide +kernel

set_option maxRecDepth 2048 in
theorem commute_block_6 : ∀ r : Fin 128,
    firstFun (secondFun ⟨(6 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) =
      secondFun (firstFun ⟨(6 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) := by
  decide +kernel

set_option maxRecDepth 2048 in
theorem commute_block_7 : ∀ r : Fin 128,
    firstFun (secondFun ⟨(7 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) =
      secondFun (firstFun ⟨(7 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) := by
  decide +kernel

set_option maxRecDepth 2048 in
theorem commute_block_8 : ∀ r : Fin 128,
    firstFun (secondFun ⟨(8 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) =
      secondFun (firstFun ⟨(8 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) := by
  decide +kernel

set_option maxRecDepth 2048 in
theorem commute_block_9 : ∀ r : Fin 128,
    firstFun (secondFun ⟨(9 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) =
      secondFun (firstFun ⟨(9 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) := by
  decide +kernel

set_option maxRecDepth 2048 in
theorem commute_block_10 : ∀ r : Fin 128,
    firstFun (secondFun ⟨(10 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) =
      secondFun (firstFun ⟨(10 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) := by
  decide +kernel

set_option maxRecDepth 2048 in
theorem commute_block_11 : ∀ r : Fin 128,
    firstFun (secondFun ⟨(11 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) =
      secondFun (firstFun ⟨(11 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) := by
  decide +kernel

set_option maxRecDepth 2048 in
theorem commute_block_12 : ∀ r : Fin 128,
    firstFun (secondFun ⟨(12 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) =
      secondFun (firstFun ⟨(12 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) := by
  decide +kernel

set_option maxRecDepth 2048 in
theorem commute_block_13 : ∀ r : Fin 128,
    firstFun (secondFun ⟨(13 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) =
      secondFun (firstFun ⟨(13 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) := by
  decide +kernel

set_option maxRecDepth 2048 in
theorem commute_block_14 : ∀ r : Fin 128,
    firstFun (secondFun ⟨(14 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) =
      secondFun (firstFun ⟨(14 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) := by
  decide +kernel

set_option maxRecDepth 2048 in
theorem commute_block_15 : ∀ r : Fin 128,
    firstFun (secondFun ⟨(15 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) =
      secondFun (firstFun ⟨(15 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) := by
  decide +kernel

set_option maxRecDepth 2048 in
theorem commute_block_16 : ∀ r : Fin 128,
    firstFun (secondFun ⟨(16 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) =
      secondFun (firstFun ⟨(16 * 128 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) := by
  decide +kernel

theorem functions_commute (i : Fin 2058) :
    firstFun (secondFun i) = secondFun (firstFun i) := by
  apply allPointsByBlocks (fun i => firstFun (secondFun i) = secondFun (firstFun i)) _ i
  intro q
  fin_cases q
  · exact commute_block_0
  · exact commute_block_1
  · exact commute_block_2
  · exact commute_block_3
  · exact commute_block_4
  · exact commute_block_5
  · exact commute_block_6
  · exact commute_block_7
  · exact commute_block_8
  · exact commute_block_9
  · exact commute_block_10
  · exact commute_block_11
  · exact commute_block_12
  · exact commute_block_13
  · exact commute_block_14
  · exact commute_block_15
  · exact commute_block_16

theorem first_second_commute : Commute (first Held.a Held.b) (second Held.a Held.b) := by
  apply Held.representation_injective
  simp only [map_mul, map_first, map_second]
  apply Equiv.ext
  intro i
  simp only [show Held.representation Held.a = Held.atlasA from rfl,
    show Held.representation Held.b = Held.atlasB from rfl,
    Equiv.Perm.mul_apply, first_action, second_action]
  exact functions_commute i

def four : Fin 4 → Held.He :=
  ![1, first Held.a Held.b, (first Held.a Held.b) ^ 2, second Held.a Held.b]

def images : Fin 4 → Fin 2058 := ![0, 373, 1225, 875]

theorem four_images (i : Fin 4) : Held.representation (four i) 0 = images i := by
  fin_cases i
  · rfl
  · change Held.representation (first Held.a Held.b) 0 = 373
    rw [map_first]
    change first Held.atlasA Held.atlasB 0 = 373
    rw [first_action]
    decide +kernel
  · change Held.representation ((first Held.a Held.b) ^ 2) 0 = 1225
    rw [map_pow, map_first]
    change (first Held.atlasA Held.atlasB ^ 2) 0 = 1225
    rw [pow_two, Equiv.Perm.mul_apply, first_action, first_action]
    decide +kernel
  · change Held.representation (second Held.a Held.b) 0 = 875
    rw [map_second]
    change second Held.atlasA Held.atlasB 0 = 875
    rw [second_action]
    decide +kernel

theorem four_injective : Function.Injective four := by
  have hi : Function.Injective images := by decide +kernel
  intro i j hij
  apply hi
  rw [← four_images i, ← four_images j, hij]

open scoped IsMulCommutative

theorem noncyclic_three_of_commuting {G : Type*} [Group G] [Finite G] (x y : G)
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : Commute x y)
    (hn : Function.Injective (![1, x, x ^ 2, y] : Fin 4 → G)) :
    ∃ P : Subgroup G, IsPGroup 3 P ∧ ¬ IsCyclic P := by
  classical
  let P := Subgroup.closure ({x, y} : Set G)
  have hxP : x ∈ P := Subgroup.subset_closure (by simp)
  have hyP : y ∈ P := Subgroup.subset_closure (by simp)
  have hcomm : IsMulCommutative P := Subgroup.isMulCommutative_closure (by
    intro u hu v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · rfl
    · exact hxy.eq
    · exact hxy.eq.symm
    · rfl)
  let := hcomm
  have hpow (g : P) : g ^ 3 = 1 := by
    obtain ⟨g, hg⟩ := g
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      apply Subtype.ext
      rcases (show g = x ∨ g = y by simpa using hg) with rfl | rfl
      · exact hx
      · exact hy
    | one => exact one_pow 3
    | mul a b ha hb iha ihb =>
      change (⟨a, ha⟩ * ⟨b, hb⟩ : P) ^ 3 = 1
      rw [mul_pow, iha, ihb, one_mul]
    | inv a ha ih =>
      change ((⟨a, ha⟩ : P)⁻¹) ^ 3 = 1
      rw [inv_pow, ih, inv_one]
  refine ⟨P, fun g => ⟨1, by simpa using hpow g⟩, ?_⟩
  intro hc
  let := hc
  let := Fintype.ofFinite P
  have hcard : Fintype.card P ≤ 3 := by
    have h := IsCyclic.card_pow_eq_one_le (α := P) (n := 3) (by decide)
    simpa [hpow] using h
  let f : Fin 4 → P := fun i => ⟨![1, x, x ^ 2, y] i, by
    fin_cases i
    · exact P.one_mem
    · exact hxP
    · exact P.pow_mem hxP 2
    · exact hyP⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply hn
    exact congrArg Subtype.val hij
  have hle := Fintype.card_le_of_injective f hf
  norm_num at hle
  omega

end HeldThreeWitness

/-- The actual degree-2058 ATLAS Held carrier contains a noncyclic three-subgroup. -/
public theorem held_noncyclic_three_subgroup :
    ∃ P : Subgroup Held.He, IsPGroup 3 P ∧ ¬ IsCyclic P := by
  exact HeldThreeWitness.noncyclic_three_of_commuting
    (HeldThreeWitness.first Held.a Held.b) (HeldThreeWitness.second Held.a Held.b)
    HeldThreeWitness.first_cube HeldThreeWitness.second_cube
    HeldThreeWitness.first_second_commute HeldThreeWitness.four_injective

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels
