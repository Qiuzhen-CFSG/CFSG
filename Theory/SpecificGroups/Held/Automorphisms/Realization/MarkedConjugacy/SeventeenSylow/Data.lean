module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedSubgroup
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.GraphCardBound.Refinement

/-!
# Finite data for the Held seventeen-centralizer

The product of the literal ATLAS generators fixes only vertex 293. Its orbit
on vertex 0, together with 293, distinguishes vertices 1 and 3 by adjacency;
adding those two vertices also distinguishes vertex 2. These facts will reduce
a commuting graph automorphism fixing 0 to the certified four-point stabilizer.

The four bits recording adjacency of x to c x, c² x, c³ x, c⁴ x define
an invariant of every graph automorphism commuting with c. The cell of 0
has 255 vertices, fewer than 17². All finite assertions use kernel reduction.

Source: ATLAS HeG1-p2058B0, retained in Held/Model/Source, and the relation
in Normalizer/GraphData. No graph-preservation assertion is assumed here.
-/

namespace Held.Realization.MarkedConjugacy.Seventeen
open Held.NormalizerGraph Held.NormalizerGraph.CardBound
public section

abbrev c : Equiv.Perm (Fin 2058) := atlasA * atlasB

@[expose] def anchors : List (Fin 2058) :=
  [0, 402, 1171, 1618, 1606, 459, 1967, 1081, 225, 23, 1340, 213,
   1240, 439, 1246, 22, 174, 293]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
lemma anchors_eq : anchors = (List.range 17).map (fun n => (c ^ n) 0) ++ [293] := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
lemma c_fixed_iff : ∀ x : Fin 2058, c x = x ↔ x = 293 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
lemma unique_one : ∀ x : Fin 2058,
    baseSignature anchors x = baseSignature anchors 1 → x = 1 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
lemma unique_three : ∀ x : Fin 2058,
    baseSignature anchors x = baseSignature anchors 3 → x = 3 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
lemma unique_two : ∀ x : Fin 2058,
    baseSignature (anchors ++ [1, 3]) x = baseSignature (anchors ++ [1, 3]) 2 → x = 2 := by
  decide +kernel

@[expose] def code : ℕ → Fin 2058 → Fin 2058 → ℕ
  | 0, _, _ => 0
  | n + 1, x, y => 2 * code n x (c y) + if Adj x y then 1 else 0

@[expose] def cycleCode (x : Fin 2058) : ℕ := code 4 x (c x)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
lemma cycleCode_count : (List.finRange 2058).countP (fun x => cycleCode x == cycleCode 0) = 255 := by
  decide +kernel

lemma cycleCode_card : Nat.card {x : Fin 2058 // cycleCode x = cycleCode 0} = 255 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← List.toFinset_finRange 2058, (List.nodup_finRange 2058).card_eq_countP]
  exact cycleCode_count

end
end Held.Realization.MarkedConjugacy.Seventeen
