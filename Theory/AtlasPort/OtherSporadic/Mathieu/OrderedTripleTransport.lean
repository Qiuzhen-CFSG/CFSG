/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu24FiveTransitive

/-!
# Transport of ordered triples of Golay coordinates

Any ordered triple of distinct coordinates can be carried to any other
by a Golay automorphism. Encode the triples as embeddings of `Fin 3` and
restrict the proved five-transitivity to those embeddings.

Source: `Atlas/Mathieu/OrderedTripleTransport.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

def distinctCoordinateTriple (i j k : Omega) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    Fin 3 ↪ Omega := ⟨![i,j,k],by
      intro a b h
      fin_cases a <;> fin_cases b <;> simp_all⟩

theorem mathieu24_ordered_triple_transport (i j a k l b : Omega)
    (hij : i ≠ j) (hai : a ≠ i) (haj : a ≠ j)
    (hkl : k ≠ l) (hbk : b ≠ k) (hbl : b ≠ l) :
    ∃ g : Mathieu24CodeModel, g.val i = k ∧ g.val j = l ∧ g.val a = b := by
  let e := distinctCoordinateTriple i j a hij hai haj
  let f := distinctCoordinateTriple k l b hkl hbk hbl
  have ht : MulAction.IsMultiplyPretransitive Mathieu24CodeModel Omega 3 := by
    let := mathieu24_five_transitive
    exact MulAction.isMultiplyPretransitive_of_le (by decide : 3 ≤ 5)
      (by norm_num [Omega,HexIndex])
  obtain ⟨g,hg⟩ := MulAction.isMultiplyPretransitive_iff.mp ht e f
  exact ⟨g,congrArg (fun e => e 0) hg,congrArg (fun e => e 1) hg,congrArg (fun e => e 2) hg⟩

end Atlas.Codes
