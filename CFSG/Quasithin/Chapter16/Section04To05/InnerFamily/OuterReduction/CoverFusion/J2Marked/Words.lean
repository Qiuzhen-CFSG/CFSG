module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Seed
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.Representative
import Mathlib.Tactic.FinCases

/-!
# Words for the marked outer J₂ fusion

Four words in the actual ATLAS generators certify the calculation needed in
16.4.9. The first two are fixed by the displayed outer involution and have
cube one. Their product is a conjugate of the known two-central involution.
The fourth word gives the required conjugator inside the J₂ carrier.

Every identity is checked by the Lean kernel on the degree-100 permutations.
The GAP discovery script in `source/discover.g` only finds the words; none
of its order, centralizer, or membership calculations is a proof premise.
The original right-action generators are inverted in the existing carrier,
so the conversion preserves word order.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.5(8), printed p.1172, and the proof of 16.4.9, pp.1190–1191;
R. A. Wilson et al., ATLAS `J2G1-p100B0`, with original data and license
retained in `Theory/SpecificGroups/LeechRelated/AtlasCarriers/source/`.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction.CoverFusion.J2Marked
open Theory.GroupTheory Sporadic.LeechRelated.J2
open Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.ExceptionalParabolics

def xWord : List (Fin 3) :=
  [0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1]

def yWord : List (Fin 3) :=
  [2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0]

def kWord : List (Fin 3) :=
  [1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2]

def lWord : List (Fin 3) :=
  [1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1, 0, 2, 0, 1, 0, 1, 0, 1]

def permWord (w : List (Fin 3)) : Equiv.Perm (Fin 100) :=
  evalWord ![tableA, tableB, tableB⁻¹] w

theorem word_inclusion (w : List (Fin 3)) :
    inclusion (Seed.localWord w) = permWord w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change inclusion (![a, b, b⁻¹] i * Seed.localWord w) = _
    rw [map_mul, ih]
    congr 1
    fin_cases i <;> simp [a, b, Sporadic.LeechRelated.J2.inclusion, generatorA_eq_table, generatorB_eq_table]

set_option maxRecDepth 100000 in
theorem certificate :
    involution * permWord xWord * involution⁻¹ = permWord xWord ∧
    involution * permWord yWord * involution⁻¹ = permWord yWord ∧
    permWord xWord ^ 3 = 1 ∧ permWord yWord ^ 3 = 1 ∧
    permWord xWord * permWord yWord =
      (permWord kWord)⁻¹ * FirstFusion.tPerm * permWord kWord ∧
    involution * (permWord lWord)⁻¹ * involution⁻¹ * permWord lWord =
      (permWord kWord)⁻¹ * FirstFusion.tPerm * permWord kWord := by
  decide +kernel

end CFSG.Quasithin.Chapter16.Intersections.OuterReduction.CoverFusion.J2Marked
