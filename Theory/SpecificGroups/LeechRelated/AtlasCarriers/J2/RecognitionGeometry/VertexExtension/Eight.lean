module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.VertexExtension.Basic
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.VertexExtension.EightData
import Mathlib.Tactic.FinCases

/-!
# An order-eight element in the actual J₂ vertex quotient

A fixed ATLAS word inverts the marked element x and has order eight.
Both assertions are checked against a single degree-100 permutation table.
Its fourth power cannot lie in X, since X has order three. Consequently
its image in the literal quotient M/X also has order eight.

This is the concrete witness needed to distinguish the exceptional
PGL₂(9) extension from the natural S₆ extension after the central quotient
has been identified with A₆. No group is identified by its order here.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.3(1), p.262,
the semidihedral Sylow two-subgroup. ATLAS attribution and reproducibility
are recorded in `source/README.md`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.VertexExtension
open Subgroup GeneratorPair Theory.GroupTheory

/-- A fixed word in the actual ATLAS generators. -/
def eight : Carrier := evalWord ![a, b, b⁻¹] EightData.word

private theorem inclusion_word (w : List (Fin 3)) :
    inclusion (evalWord ![a, b, b⁻¹] w) = evalWord ![tableA, tableB, tableB⁻¹] w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [evalWord, map_mul, ih, evalWord]
    congr 1
    fin_cases i
    · exact generatorA_eq_table
    · exact generatorB_eq_table
    · exact (map_inv inclusion b).trans (congrArg Inv.inv
        (show inclusion b = tableB from generatorB_eq_table))

private theorem inclusion_eight : inclusion eight = EightData.permutation :=
  (inclusion_word EightData.word).trans
    (by decide +kernel : evalWord ![tableA, tableB, tableB⁻¹] EightData.word = EightData.permutation)

private def xPerm : Equiv.Perm (Fin 100) := (tableA * tableB * tableA * tableB⁻¹) ^ 4

private theorem inclusion_x : inclusion x = xPerm := by
  simp only [x, xPerm, map_pow, map_mul, map_inv,
    (show inclusion a = tableA from generatorA_eq_table),
    (show inclusion b = tableB from generatorB_eq_table)]

theorem eight_pow_eight : eight ^ 8 = 1 := by
  apply inclusion_injective
  rw [map_pow, inclusion_eight, map_one]
  decide +kernel

theorem eight_pow_four_ne : eight ^ 4 ≠ 1 := by
  intro h
  have he := congrArg inclusion h
  rw [map_pow, inclusion_eight, map_one] at he
  exact (by decide +kernel : EightData.permutation ^ 4 ≠ 1) he

theorem orderOf_eight : orderOf eight = 8 :=
  orderOf_eq_prime_pow (p := 2) (n := 2) eight_pow_four_ne eight_pow_eight

theorem eight_inverts_x : eight * x * eight⁻¹ = x⁻¹ := by
  apply inclusion_injective
  simp only [map_mul, map_inv, inclusion_eight, inclusion_x]
  decide +kernel

theorem eight_mem_M : eight ∈ M := mem_M_of_inverts eight eight_inverts_x

/-- The same word as an element of the literal normalizer. -/
def eightM : M := ⟨eight, eight_mem_M⟩

/-- Its image under the actual quotient map, not a separate model element. -/
def eightQuotient : VertexQuotient := vertexQuotientMap eightM

private theorem eight_pow_four_not_mem_X : eight ^ 4 ∉ X := by
  intro h
  have h12 : eight ^ 12 = 1 := by
    have he : (⟨eight ^ 4, h⟩ : X) ^ Nat.card X = 1 := pow_card_eq_one'
    rw [card_X] at he
    have he' := congrArg (fun z : X => (z : Carrier)) he
    change (eight ^ 4) ^ 3 = 1 at he'
    simpa only [← pow_mul] using he'
  have hd := orderOf_dvd_of_pow_eq_one h12
  rw [orderOf_eight] at hd
  norm_num at hd

/-- The order-eight obstruction survives the actual central quotient. -/
theorem orderOf_eightQuotient : orderOf eightQuotient = 8 := by
  apply orderOf_eq_prime_pow (p := 2) (n := 2)
  · intro h
    change vertexQuotientMap eightM ^ 4 = 1 at h
    rw [← map_pow] at h
    have hx : eightM ^ 4 ∈ XM := (QuotientGroup.eq_one_iff _).mp h
    exact eight_pow_four_not_mem_X hx
  · change vertexQuotientMap eightM ^ 8 = 1
    rw [← map_pow, show eightM ^ 8 = 1 from Subtype.ext eight_pow_eight, map_one]

end Sporadic.LeechRelated.J2.RecognitionGeometry.VertexExtension
