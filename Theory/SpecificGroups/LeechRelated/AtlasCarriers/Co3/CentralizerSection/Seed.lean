module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co3.CentralizerSection.PointTables
import Mathlib.Tactic.FinCases

/-!
# An involution and a centralizing subgroup in the fixed Co₃ carrier

The involution is the square of the second ATLAS generator. Three explicit
words give a subgroup of its centralizer. Every membership is a word in the
defining generators; involution and commutation certificates are checked on
all 276 points. The anticipated quotient is obtained from the 36 fixed points.
This does not assert equality with the whole centralizer or an ambient order.

Source: the `2Sp₆(2)` row in GLS3 Table 5.3j, used in Aschbacher--Smith A.2.19.
-/

@[expose] public section
namespace Sporadic.LeechRelated.Co3.CentralizerSection

set_option maxRecDepth 20000

/-- The original first generator, inside the fixed generated carrier. -/
def a : Carrier := ⟨generatorA, Subgroup.subset_closure (by simp)⟩

/-- The original second generator, inside the fixed generated carrier. -/
def b : Carrier := ⟨generatorB, Subgroup.subset_closure (by simp)⟩

def involution : Carrier := b ^ 2

def v : Carrier := a * b⁻¹ * a

def w : Carrier := a * b * a⁻¹

def c : Carrier := v * (involution * v⁻¹ * involution * v)

def d : Carrier := w * (involution * w⁻¹ * involution * w) ^ 2

/-- Generators of the chosen centralizing numerator. -/
def generator : Fin 3 → Carrier := ![b, c, d]

private theorem inclusion_a : inclusion a = Tables.tableA := Tables.generatorA_eq_table

private theorem inclusion_b : inclusion b = Tables.tableB := Tables.generatorB_eq_table

theorem inclusion_involution : inclusion involution = Tables.tableZ := by
  rw [involution, map_pow, inclusion_b]
  exact Tables.tableZ_eq

private theorem inclusion_v : inclusion v = Tables.wordV := by
  simp only [v, map_mul, map_inv, inclusion_a, inclusion_b]
  rfl

private theorem inclusion_w : inclusion w = Tables.wordW := by
  simp only [w, map_mul, map_inv, inclusion_a, inclusion_b]
  rfl

private theorem inclusion_c : inclusion c = Tables.tableC := by
  change inclusion (v * (involution * v⁻¹ * involution * v)) = _
  simp only [map_mul, map_inv, inclusion_v, inclusion_involution]
  exact Tables.tableC_eq

private theorem inclusion_d : inclusion d = Tables.tableD := by
  change inclusion (w * (involution * w⁻¹ * involution * w) ^ 2) = _
  simp only [map_mul, map_inv, map_pow, inclusion_w, inclusion_involution]
  exact Tables.tableD_eq

theorem inclusion_generator (i : Fin 3) : inclusion (generator i) = Tables.generatorTable i := by
  fin_cases i
  · exact Tables.generatorB_eq_table
  · exact inclusion_c
  · exact inclusion_d

theorem involution_sq : involution ^ 2 = 1 := by
  apply inclusion_injective
  rw [map_pow, map_one, inclusion_involution]
  exact Tables.tableZ_sq

theorem involution_ne_one : involution ≠ 1 := by
  intro h
  have hp := congrArg (fun g : Carrier => inclusion g 0) h
  rw [inclusion_involution, map_one] at hp
  exact Tables.tableZ_moves_zero hp

theorem involution_order : orderOf involution = 2 :=
  orderOf_eq_prime involution_sq involution_ne_one

theorem generator_commutes (i : Fin 3) : generator i * involution = involution * generator i := by
  apply inclusion_injective
  simp only [map_mul, inclusion_involution, inclusion_generator]
  exact Tables.generatorTable_commutes i

/-- A concrete subgroup of the actual Co₃ carrier. -/
def numerator : Subgroup Carrier := Subgroup.closure (Set.range generator)

theorem generator_mem (i : Fin 3) : generator i ∈ numerator :=
  Subgroup.subset_closure ⟨i, rfl⟩

theorem numerator_centralizes : numerator ≤ Subgroup.centralizer ({involution} : Set Carrier) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr (generator_commutes i)

/-- The chosen generators viewed in the numerator. -/
def numeratorGenerator (i : Fin 3) : numerator := ⟨generator i, generator_mem i⟩

end Sporadic.LeechRelated.Co3.CentralizerSection
