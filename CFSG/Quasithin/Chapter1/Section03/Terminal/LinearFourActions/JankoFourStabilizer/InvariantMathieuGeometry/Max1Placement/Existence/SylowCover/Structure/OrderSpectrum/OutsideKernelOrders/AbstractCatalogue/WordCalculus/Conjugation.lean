module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.WordCalculus.Basic

/-!
# The five inverse-conjugation displacements

Conjugating a slice word is evaluation of the concatenated presentation
conjugate words. Their quotient images are combined with the xor law from
`Basic`. Only short finite calculations of binary codes remain; no table
of products in the presentation is assumed.

This proves the exact product orientation of `WordCalculus.conjugate`,
for conjugators g0, g1, g2, g4 and g5, respectively.
Source context: Aschbacher–Smith A.3.12, pp.47–48; the literal relations
and provenance in `SylowNormalEights/PresentationData.lean` and its source README.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.WordProof
open Janko4.LocalStructure.SylowNormalEights Presentation Profiles

abbrev envelopeIndices : List (Fin 21) := [9, 11, 13, 14, 15, 16, 17, 18, 19, 20]

def letterCode (i : Fin 21) : Code :=
  match i.val with
  | 9 => 1 | 11 => 2 | 13 => 4 | 14 => 8 | 15 => 16 | 17 => 32 | _ => 0

def wordCode : List (Fin 21) → Code
  | [] => 0
  | i :: w => codeXor (letterCode i) (wordCode w)

theorem q_letter (i : Fin 21) (hi : i ∈ envelopeIndices) :
    q (generator i) = v (letterCode i) := by
  simp only [envelopeIndices, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change q (generator 9) = q (generator 9 * 1); rw [mul_one]
  · change q (generator 11) = q (generator 11 * 1); rw [mul_one]
  · change q (generator 13) = q (generator 13 * 1); rw [mul_one]
  · change q (generator 14) = q (generator 14 * 1); rw [mul_one]
  · change q (generator 15) = q (generator 15 * 1); rw [mul_one]
  · exact q_generator_core 16 (by decide)
  · change q (generator 17) = q (generator 17 * 1); rw [mul_one]
  · exact q_generator_core 18 (by decide)
  · exact q_generator_core 19 (by decide)
  · exact q_generator_core 20 (by decide)

theorem q_word (w : List (Fin 21)) (hw : ∀ i ∈ w, i ∈ envelopeIndices) :
    q (wordValue w) = v (wordCode w) := by
  induction w with
  | nil => exact map_one q
  | cons i w ih =>
    rw [wordValue_cons, map_mul, q_letter i (hw i List.mem_cons_self),
      ih (fun k hk => hw k (List.mem_cons_of_mem i hk)), v_mul]
    rfl

private theorem conjugate_lt : ∀ j : Fin 5, ∀ i : Fin 21,
    i ∈ sliceIndices → conjugatorIndex j < i := by decide +kernel

def conjugatedWord (j : Fin 5) (w : List (Fin 21)) : List (Fin 21) :=
  w.flatMap (conjugateWord (conjugatorIndex j))

theorem conjugatedWord_value (j : Fin 5) (w : List (Fin 21))
    (hw : ∀ i ∈ w, i ∈ sliceIndices) :
    wordValue (conjugatedWord j w) =
      (generator (conjugatorIndex j))⁻¹ * wordValue w * generator (conjugatorIndex j) := by
  let f := (MulAut.conj (generator (conjugatorIndex j))⁻¹).toMonoidHom
  have hf : wordValue (conjugatedWord j w) = f (wordValue w) := by
    induction w with
    | nil => exact (map_one f).symm
    | cons i w ih =>
      change wordValue (conjugateWord (conjugatorIndex j) i ++ conjugatedWord j w) = _
      rw [wordValue_append, wordValue_cons, map_mul,
        ih (fun k hk => hw k (List.mem_cons_of_mem i hk))]
      congr 1
      have he := generator_relations.conjugate (conjugatorIndex j) i
        (conjugate_lt j i (hw i List.mem_cons_self))
      simpa only [wordValue, f, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using he.symm
  simpa only [f, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hf

private theorem conjugated_slice_support : ∀ j : Fin 5, ∀ n : Code,
    ∀ i ∈ conjugatedWord j (sliceWord n), i ∈ envelopeIndices := by decide +kernel

private theorem slice_support : ∀ n : Code, ∀ i ∈ sliceWord n, i ∈ sliceIndices := by
  decide +kernel

private theorem displacement_code : ∀ j : Fin 5, ∀ n : Code,
    wordCode (conjugatedWord j (sliceWord n)) = codeXor n (displacement j n) := by
  decide +kernel

theorem v_conjugate (j : Fin 5) (n : Code) :
    q ((generator (conjugatorIndex j))⁻¹ * sliceValue n * generator (conjugatorIndex j)) =
      v n * v (displacement j n) := by
  change q ((generator (conjugatorIndex j))⁻¹ * wordValue (sliceWord n) *
    generator (conjugatorIndex j)) = _
  rw [← conjugatedWord_value j (sliceWord n) (slice_support n),
    q_word _ (conjugated_slice_support j n), displacement_code, v_mul]

theorem conjugate_mem (j : Fin 5) (n : Code) :
    (generator (conjugatorIndex j))⁻¹ * sliceValue n * generator (conjugatorIndex j) *
      (sliceValue n)⁻¹ * (sliceValue (displacement j n))⁻¹ ∈ core := by
  apply q_eq_one.mp
  rw [map_mul, map_mul, v_conjugate, map_inv, map_inv]
  change v n * v (displacement j n) * (v n)⁻¹ * (v (displacement j n))⁻¹ = 1
  have hc : Commute (v n) (v (displacement j n)) := by
    change v n * v (displacement j n) = v (displacement j n) * v n
    rw [v_mul, v_mul]
    congr 1
    exact Fin.ext (Nat.xor_comm _ _ |> congrArg (· % 64))
  rw [hc.eq, mul_inv_cancel_right, mul_inv_cancel]

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.WordProof
