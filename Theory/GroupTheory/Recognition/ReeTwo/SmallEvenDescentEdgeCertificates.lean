module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenDescentEdgeData
public import Theory.GroupTheory.SubgroupClosureWords
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenDescentEdgeCertificateChecks
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenDescentEdgeCertificatesA
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenDescentEdgeCertificatesB
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenDescentEdgeCertificatesC
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenDescentEdgeCertificatesD

/-!
# Assembly of encoded small even descent edge certificates

Each encoded certificate supplies forward and backward generator words, hence
both containments of the required conjugacy equation. The first hundred rows
and four remaining disjoint ranges are checked separately and assembled below
to prove all 3617 equations. Their checks use the fixed predicate and witnesses
without altering any edge number, target node, generator, or conjugator.

Source: Shinoda (1975), (2.3), pp. 81–82, with diagnostic provenance recorded in
`SmallEvenDescentEdgeData`.
-/

namespace ReeTwo.SylowModel.SmallEvenDescentEdges
open Theory.GroupTheory.SubgroupEnumeration
open Certificates

/-- An encoded word certificate proves the original subgroup equality. -/
public theorem edge_eq_nodeClosure_of_encoded (e : Fin 3617) (h : EncodedValid e) :
    (edge e).map (MulAut.conj (conjugator e)).toMonoidHom =
      nodeClosure (targetIndex e) :=
  (words e).sound _ _ _ (encoded_valid_words e h)

/-- The first hundred original edge rows satisfy the required conjugacy. -/
public theorem edge_eq_nodeClosure_lt100 (e : Fin 3617) (h : e.val < 100) :
    (edge e).map (MulAut.conj (conjugator e)).toMonoidHom =
      nodeClosure (targetIndex e) :=
  edge_eq_nodeClosure_of_encoded e (encoded_valid_initial ⟨e.val, h⟩)

/-- Four independent finite checks complete the remaining edge equations. -/
public theorem edge_eq_nodeClosure_of_encoded_batches
    (hA : ∀ e : Fin 3617, 100 ≤ e.val → e.val < 1000 → EncodedValid e)
    (hB : ∀ e : Fin 3617, 1000 ≤ e.val → e.val < 1900 → EncodedValid e)
    (hC : ∀ e : Fin 3617, 1900 ≤ e.val → e.val < 2800 → EncodedValid e)
    (hD : ∀ e : Fin 3617, 2800 ≤ e.val → EncodedValid e)
    (e : Fin 3617) :
    (edge e).map (MulAut.conj (conjugator e)).toMonoidHom =
      nodeClosure (targetIndex e) := by
  apply edge_eq_nodeClosure_of_encoded
  by_cases h0 : e.val < 100
  · exact encoded_valid_initial ⟨e.val, h0⟩
  by_cases h1 : e.val < 1000
  · exact hA e (by omega) h1
  by_cases h2 : e.val < 1900
  · exact hB e (by omega) h2
  by_cases h3 : e.val < 2800
  · exact hC e (by omega) h3
  exact hD e (by omega)

/-- Every recorded edge is conjugate to the closure of its target node generators. -/
public theorem edge_eq_nodeClosure (e : Fin 3617) :
    (edge e).map (MulAut.conj (conjugator e)).toMonoidHom =
      nodeClosure (targetIndex e) :=
  edge_eq_nodeClosure_of_encoded_batches
    encoded_valid_A encoded_valid_B encoded_valid_C encoded_valid_D e

end ReeTwo.SylowModel.SmallEvenDescentEdges
