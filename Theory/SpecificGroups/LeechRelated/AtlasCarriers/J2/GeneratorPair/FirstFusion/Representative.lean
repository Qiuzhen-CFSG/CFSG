module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair
public import Theory.GroupTheory.WordSubgroup
import Mathlib.Tactic.FinCases

/-!
# A concrete commutator involution for first-generator fusion in J₂

The element `t = (abab⁻¹)⁶` is a nonidentity involution in the actual
ATLAS degree-100 carrier. The inverse-closed alphabet `a, b, b⁻¹` generates
that carrier and supports the finite conjugation certificates in this directory.

Source: ATLAS `J2G1-p100B0`, retained under `AtlasCarriers/source/`.
The eventual application concerns the two involution classes in GLS3,
Table 5.3g; class coverage is proved separately, not assumed here.
-/

@[expose] public section
open Theory.GroupTheory
namespace Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion

def t : Carrier := (a * b * a * b⁻¹) ^ 6

theorem t_pow_two : t ^ 2 = 1 := by
  rw [t, ← pow_mul]
  exact comm_word_pow_twelve

def tPerm : Equiv.Perm (Fin 100) :=
  (tableA * tableB * tableA * tableB⁻¹) ^ 6

theorem inclusion_t : inclusion t = tPerm := by
  simp only [t, map_pow, map_mul, map_inv]
  change (generatorA * generatorB * generatorA * generatorB⁻¹) ^ 6 = tPerm
  rw [generatorA_eq_table, generatorB_eq_table]
  rfl

set_option maxRecDepth 20000 in
theorem t_ne_one : t ≠ 1 := by
  intro h
  have hh := congrArg inclusion h
  rw [inclusion_t, map_one] at hh
  exact (by decide +kernel : tPerm ≠ 1) hh

def letter : Fin 3 → Carrier := ![a, b, b⁻¹]
def permLetter : Fin 3 → Equiv.Perm (Fin 100) := ![tableA, tableB, tableB⁻¹]
def invLetter : Fin 3 → Fin 3 := ![0, 2, 1]

theorem inclusion_letter (i : Fin 3) : inclusion (letter i) = permLetter i := by
  fin_cases i
  · exact generatorA_eq_table
  · exact generatorB_eq_table
  · change generatorB⁻¹ = tableB⁻¹
    rw [generatorB_eq_table]

theorem letter_inv (i : Fin 3) : letter (invLetter i) = (letter i)⁻¹ := by
  have ha : a = a⁻¹ := eq_inv_of_mul_eq_one_left (by simpa only [pow_two] using a_pow_two)
  fin_cases i
  · exact ha
  · rfl
  · exact (inv_inv b).symm

theorem letter_generates : Subgroup.closure (Set.range letter) = ⊤ := by
  apply top_unique
  rw [← closure_pair_eq_top]
  apply Subgroup.closure_mono
  intro x hx
  rcases hx with rfl | hx
  · exact ⟨0, rfl⟩
  · rcases hx with rfl
    exact ⟨1, rfl⟩

end Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion
