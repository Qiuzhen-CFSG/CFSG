module
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.Evaluator
import Mathlib.Tactic.FinCases

/-!
# Inner realization of the source reflection

The literal word below fixes the ATLAS involution and inverts its order-seven
generator. Each identity is checked on the degree-2058 permutation model.
This is the concrete input to reflection compatibility in central covers;
it asserts no faithfulness of the source presentation.

Source: John Bray's `Held/Model/Source/HeG1-P1.M` and the retained
`HeG1-p2058B0.g1` and `.g2` permutation tables. GAP discovers the word;
Lean checks its two actions on all points, in blocks of 64, using the
existing certified packed ATLAS tables to avoid repeated permutation reduction.
-/

namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd.ReflectionModel
@[expose] public def word {G : Type*} [Group G] (a b : G) : G :=
  b⁻¹ * b⁻¹ * a * b * b * a * b⁻¹ * b⁻¹ * a * b * b * a * b⁻¹ * b⁻¹ * a * b * b * b * a * b⁻¹ * b⁻¹ * a * b⁻¹ * a * b * a * b⁻¹ * a * b * a * b * b * a * b⁻¹ * a * b⁻¹ * a * b⁻¹ * a * b⁻¹ * a * b * b * a * b⁻¹ * b⁻¹ * a * b⁻¹ * b⁻¹ * a * b * b * a * b⁻¹ * a * b⁻¹ * a * b⁻¹


private theorem map_word {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a b : G) : f (word a b) = word (f a) (f b) := by
  simp only [word, map_mul, map_inv]


private abbrev fastA := Held.Realization.MarkedConjugacy.NormalizedPairs.ClassA.fastA
private abbrev fastB := Held.Realization.MarkedConjugacy.NormalizedPairs.ClassA.fastB
private abbrev fastBi := Held.Realization.MarkedConjugacy.NormalizedPairs.ClassA.fastBi
private theorem fastA_correct (p : Fin 2058) : fastA p.val = (atlasA p).val :=
  (Held.Realization.MarkedConjugacy.NormalizedPairs.ClassA.fast_correct p).1
private theorem fastB_correct (p : Fin 2058) : fastB p.val = (atlasB p).val :=
  (Held.Realization.MarkedConjugacy.NormalizedPairs.ClassA.fast_correct p).2.1
private theorem fastBi_correct (p : Fin 2058) : fastBi p.val = (atlasB⁻¹ p).val :=
  (Held.Realization.MarkedConjugacy.NormalizedPairs.ClassA.fast_correct p).2.2

private def fastReflector (p : Nat) : Nat :=
  fastBi (fastBi (fastA (fastB (fastB (fastA (fastBi (fastBi (fastA (fastB (fastB (fastA (fastBi (fastBi (fastA (fastB (fastB (fastB (fastA (fastBi (fastBi (fastA (fastBi (fastA (fastB (fastA (fastBi (fastA (fastB (fastA (fastB (fastB (fastA (fastBi (fastA (fastBi (fastA (fastBi (fastA (fastBi (fastA (fastB (fastB (fastA (fastBi (fastBi (fastA (fastBi (fastBi (fastA (fastB (fastB (fastA (fastBi (fastA (fastBi (fastA (fastBi (p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem fastReflector_correct (p : Fin 2058) :
    fastReflector p.val = ((word atlasA atlasB) p).val := by
  simp only [fastReflector, word, Equiv.Perm.mul_apply,
    fastA_correct, fastB_correct, fastBi_correct]

private theorem allPoints (P : Fin 2058 → Prop)
    (h : ∀ q : Fin 33, ∀ r : Fin 64,
      P ⟨(q.val * 64 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩) : ∀ p, P p := by
  intro p
  have hp := h ⟨p.val / 64, by omega⟩ ⟨p.val % 64, Nat.mod_lt _ (by decide)⟩
  have he : p.val / 64 * 64 + p.val % 64 = p.val := by omega
  simpa only [he, Nat.mod_eq_of_lt p.isLt] using hp


set_option maxRecDepth 2048 in
private theorem commute_a_0 : ∀ r : Fin 64,
    fastReflector (fastA ((0 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((0 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_1 : ∀ r : Fin 64,
    fastReflector (fastA ((1 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((1 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_2 : ∀ r : Fin 64,
    fastReflector (fastA ((2 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((2 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_3 : ∀ r : Fin 64,
    fastReflector (fastA ((3 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((3 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_4 : ∀ r : Fin 64,
    fastReflector (fastA ((4 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((4 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_5 : ∀ r : Fin 64,
    fastReflector (fastA ((5 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((5 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_6 : ∀ r : Fin 64,
    fastReflector (fastA ((6 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((6 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_7 : ∀ r : Fin 64,
    fastReflector (fastA ((7 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((7 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_8 : ∀ r : Fin 64,
    fastReflector (fastA ((8 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((8 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_9 : ∀ r : Fin 64,
    fastReflector (fastA ((9 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((9 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_10 : ∀ r : Fin 64,
    fastReflector (fastA ((10 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((10 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_11 : ∀ r : Fin 64,
    fastReflector (fastA ((11 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((11 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_12 : ∀ r : Fin 64,
    fastReflector (fastA ((12 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((12 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_13 : ∀ r : Fin 64,
    fastReflector (fastA ((13 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((13 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_14 : ∀ r : Fin 64,
    fastReflector (fastA ((14 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((14 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_15 : ∀ r : Fin 64,
    fastReflector (fastA ((15 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((15 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_16 : ∀ r : Fin 64,
    fastReflector (fastA ((16 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((16 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_17 : ∀ r : Fin 64,
    fastReflector (fastA ((17 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((17 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_18 : ∀ r : Fin 64,
    fastReflector (fastA ((18 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((18 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_19 : ∀ r : Fin 64,
    fastReflector (fastA ((19 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((19 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_20 : ∀ r : Fin 64,
    fastReflector (fastA ((20 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((20 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_21 : ∀ r : Fin 64,
    fastReflector (fastA ((21 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((21 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_22 : ∀ r : Fin 64,
    fastReflector (fastA ((22 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((22 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_23 : ∀ r : Fin 64,
    fastReflector (fastA ((23 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((23 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_24 : ∀ r : Fin 64,
    fastReflector (fastA ((24 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((24 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_25 : ∀ r : Fin 64,
    fastReflector (fastA ((25 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((25 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_26 : ∀ r : Fin 64,
    fastReflector (fastA ((26 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((26 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_27 : ∀ r : Fin 64,
    fastReflector (fastA ((27 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((27 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_28 : ∀ r : Fin 64,
    fastReflector (fastA ((28 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((28 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_29 : ∀ r : Fin 64,
    fastReflector (fastA ((29 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((29 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_30 : ∀ r : Fin 64,
    fastReflector (fastA ((30 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((30 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_31 : ∀ r : Fin 64,
    fastReflector (fastA ((31 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((31 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem commute_a_32 : ∀ r : Fin 64,
    fastReflector (fastA ((32 * 64 + r.val) % 2058)) =
      fastA (fastReflector ((32 * 64 + r.val) % 2058)) := by
  decide +kernel

private theorem commute_a_fast : ∀ p : Fin 2058,
    fastReflector (fastA p.val) = fastA (fastReflector p.val) := by
  apply allPoints
  intro q
  fin_cases q
  · exact commute_a_0
  · exact commute_a_1
  · exact commute_a_2
  · exact commute_a_3
  · exact commute_a_4
  · exact commute_a_5
  · exact commute_a_6
  · exact commute_a_7
  · exact commute_a_8
  · exact commute_a_9
  · exact commute_a_10
  · exact commute_a_11
  · exact commute_a_12
  · exact commute_a_13
  · exact commute_a_14
  · exact commute_a_15
  · exact commute_a_16
  · exact commute_a_17
  · exact commute_a_18
  · exact commute_a_19
  · exact commute_a_20
  · exact commute_a_21
  · exact commute_a_22
  · exact commute_a_23
  · exact commute_a_24
  · exact commute_a_25
  · exact commute_a_26
  · exact commute_a_27
  · exact commute_a_28
  · exact commute_a_29
  · exact commute_a_30
  · exact commute_a_31
  · exact commute_a_32

private theorem commute_a_perm : word atlasA atlasB * atlasA = atlasA * word atlasA atlasB := by
  apply Equiv.ext
  intro p
  apply Fin.ext
  simpa only [fastA_correct, fastB_correct, fastBi_correct, fastReflector_correct,
    Equiv.Perm.mul_apply] using commute_a_fast p

set_option maxRecDepth 2048 in
private theorem invert_b_0 : ∀ r : Fin 64,
    fastB (fastReflector ((0 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((0 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_1 : ∀ r : Fin 64,
    fastB (fastReflector ((1 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((1 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_2 : ∀ r : Fin 64,
    fastB (fastReflector ((2 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((2 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_3 : ∀ r : Fin 64,
    fastB (fastReflector ((3 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((3 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_4 : ∀ r : Fin 64,
    fastB (fastReflector ((4 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((4 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_5 : ∀ r : Fin 64,
    fastB (fastReflector ((5 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((5 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_6 : ∀ r : Fin 64,
    fastB (fastReflector ((6 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((6 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_7 : ∀ r : Fin 64,
    fastB (fastReflector ((7 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((7 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_8 : ∀ r : Fin 64,
    fastB (fastReflector ((8 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((8 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_9 : ∀ r : Fin 64,
    fastB (fastReflector ((9 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((9 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_10 : ∀ r : Fin 64,
    fastB (fastReflector ((10 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((10 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_11 : ∀ r : Fin 64,
    fastB (fastReflector ((11 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((11 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_12 : ∀ r : Fin 64,
    fastB (fastReflector ((12 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((12 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_13 : ∀ r : Fin 64,
    fastB (fastReflector ((13 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((13 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_14 : ∀ r : Fin 64,
    fastB (fastReflector ((14 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((14 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_15 : ∀ r : Fin 64,
    fastB (fastReflector ((15 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((15 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_16 : ∀ r : Fin 64,
    fastB (fastReflector ((16 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((16 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_17 : ∀ r : Fin 64,
    fastB (fastReflector ((17 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((17 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_18 : ∀ r : Fin 64,
    fastB (fastReflector ((18 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((18 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_19 : ∀ r : Fin 64,
    fastB (fastReflector ((19 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((19 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_20 : ∀ r : Fin 64,
    fastB (fastReflector ((20 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((20 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_21 : ∀ r : Fin 64,
    fastB (fastReflector ((21 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((21 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_22 : ∀ r : Fin 64,
    fastB (fastReflector ((22 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((22 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_23 : ∀ r : Fin 64,
    fastB (fastReflector ((23 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((23 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_24 : ∀ r : Fin 64,
    fastB (fastReflector ((24 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((24 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_25 : ∀ r : Fin 64,
    fastB (fastReflector ((25 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((25 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_26 : ∀ r : Fin 64,
    fastB (fastReflector ((26 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((26 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_27 : ∀ r : Fin 64,
    fastB (fastReflector ((27 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((27 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_28 : ∀ r : Fin 64,
    fastB (fastReflector ((28 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((28 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_29 : ∀ r : Fin 64,
    fastB (fastReflector ((29 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((29 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_30 : ∀ r : Fin 64,
    fastB (fastReflector ((30 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((30 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_31 : ∀ r : Fin 64,
    fastB (fastReflector ((31 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((31 * 64 + r.val) % 2058)) := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem invert_b_32 : ∀ r : Fin 64,
    fastB (fastReflector ((32 * 64 + r.val) % 2058)) =
      fastReflector (fastBi ((32 * 64 + r.val) % 2058)) := by
  decide +kernel

private theorem invert_b_fast : ∀ p : Fin 2058,
    fastB (fastReflector p.val) = fastReflector (fastBi p.val) := by
  apply allPoints
  intro q
  fin_cases q
  · exact invert_b_0
  · exact invert_b_1
  · exact invert_b_2
  · exact invert_b_3
  · exact invert_b_4
  · exact invert_b_5
  · exact invert_b_6
  · exact invert_b_7
  · exact invert_b_8
  · exact invert_b_9
  · exact invert_b_10
  · exact invert_b_11
  · exact invert_b_12
  · exact invert_b_13
  · exact invert_b_14
  · exact invert_b_15
  · exact invert_b_16
  · exact invert_b_17
  · exact invert_b_18
  · exact invert_b_19
  · exact invert_b_20
  · exact invert_b_21
  · exact invert_b_22
  · exact invert_b_23
  · exact invert_b_24
  · exact invert_b_25
  · exact invert_b_26
  · exact invert_b_27
  · exact invert_b_28
  · exact invert_b_29
  · exact invert_b_30
  · exact invert_b_31
  · exact invert_b_32

private theorem invert_b_perm : atlasB * word atlasA atlasB = word atlasA atlasB * atlasB⁻¹ := by
  apply Equiv.ext
  intro p
  apply Fin.ext
  simpa only [fastA_correct, fastB_correct, fastBi_correct, fastReflector_correct,
    Equiv.Perm.mul_apply] using invert_b_fast p
/-- The checked group word implementing reflection of the source pair. -/
@[expose] public def reflector : He := word a b

/-- The actual reflector fixes the first standard generator. -/
public theorem reflector_conj_a : reflector⁻¹ * a * reflector = a := by
  have hc : a * reflector = reflector * a := by
    apply representation_injective
    simpa only [map_mul, reflector, map_word, representation, a, b, Subgroup.subtype_apply] using commute_a_perm.symm
  rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]

/-- The actual reflector inverts the second standard generator. -/
public theorem reflector_conj_b : reflector⁻¹ * b * reflector = b⁻¹ := by
  have hc : b * reflector = reflector * b⁻¹ := by
    apply representation_injective
    simpa only [map_mul, map_inv, reflector, map_word, representation, a, b, Subgroup.subtype_apply] using invert_b_perm
  rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd.ReflectionModel
