module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenDescentEdgeData
public import Theory.GroupTheory.SubgroupClosureWords
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenDescentEdgeCertificates
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenDescentNodeWords

/-!
# Assembly of the small even descent edge certificates

The recorded edge subgroups, targets and conjugators are defined in
`SmallEvenDescentEdgeData`. Word certificates prove their conjugacy to the
recorded node generators. Identification of those generators with the existing
600-node family then gives the edge equations in the public node numbering.
The two independent finite checks are proved in `SmallEvenDescentEdgeCertificates`
and `SmallEvenDescentNodeWords`; together they certify all 3617 edge equations.

Source: the root convention of Shinoda (1975), (2.3), pp. 81–82, and the
diagnostic data attributed in `SmallEvenDescentEdgeData`.
-/

namespace ReeTwo.SylowModel.SmallEvenDescentEdges
open Theory.GroupTheory.SubgroupEnumeration

/-- A checked word table proves the edge equation for the word-based node. -/
public theorem edge_eq_nodeClosure_of_words (e : Fin 3617)
    (words : ClosureWords 10 10)
    (valid : words.Valid (generator e) (nodeGenerator (targetIndex e))
      (MulAut.conj (conjugator e)).toMonoidHom) :
    (edge e).map (MulAut.conj (conjugator e)).toMonoidHom =
      nodeClosure (targetIndex e) :=
  words.sound _ _ _ valid

/-- Identification and checked edge equations assemble in the original numbering. -/
public theorem edge_equations_of_certificates
    (hnodes : ∀ i, nodeClosure i = smallEvenDescentNode i.succ)
    (hedges : ∀ e, (edge e).map (MulAut.conj (conjugator e)).toMonoidHom =
      nodeClosure (targetIndex e)) :
    ∀ e, (edge e).map (MulAut.conj (conjugator e)).toMonoidHom =
      smallEvenDescentNode (target e) := by
  intro e
  exact (hedges e).trans (hnodes (targetIndex e))

/-- Every recorded edge conjugates to its target in the original 600-node family. -/
public theorem edge_equations (e : Fin 3617) :
    (edge e).map (MulAut.conj (conjugator e)).toMonoidHom =
      smallEvenDescentNode (target e) :=
  edge_equations_of_certificates nodeClosure_eq edge_eq_nodeClosure e

end ReeTwo.SylowModel.SmallEvenDescentEdges
