module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenDescentEdgeWords
public import Theory.SpecificGroups.ReeTwo.SylowPackedArithmetic

/-!
# Encoded equation checks for the small even descent edges

The certificate predicate uses integer-encoded products, each proved equal to
its operation in the original Sylow group. Its soundness gives the original
`ClosureWords.Valid` equations. The first hundred edge rows are checked here;
further disjoint ranges can be checked independently against the same predicate.

Source: Shinoda (1975), (2.3), pp. 81–82. Word witnesses and diagnostic provenance
are documented in `SmallEvenDescentEdgeWords` and `SmallEvenDescentEdgeData`.
-/

namespace ReeTwo.SylowModel.SmallEvenDescentEdges.Certificates
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration
open Collected

@[expose] public def EncodedValid (e : Fin 3617) : Prop :=
  (∀ k, packedEval (fun j => code (fastNodeGenerator (targetIndex e) j))
    ((words e).forward k) = packedConj (code (fastConjugator e)) (code (fastGenerator e k))) ∧
  (∀ k, packedEval (fun j => packedConj (code (fastConjugator e)) (code (fastGenerator e j)))
    ((words e).backward k) = code (fastNodeGenerator (targetIndex e) k))
public instance (e : Fin 3617) : Decidable (EncodedValid e) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem packedWords_valid {n m : Nat} (w : ClosureWords n m)
    (a : Fin n → SylowModel) (b : Fin m → SylowModel) (g : SylowModel)
    (h : (∀ k, packedEval (fun j => code (b j)) (w.forward k) =
      packedConj (code g) (code (a k))) ∧
      (∀ k, packedEval (fun j => packedConj (code g) (code (a j))) (w.backward k) =
        code (b k))) : w.Valid a b (MulAut.conj g).toMonoidHom := by
  obtain ⟨hf, hb⟩ := h
  constructor
  · intro k
    apply code_injective
    simpa only [packedEval_code, packedConj_code, MulEquiv.coe_toMonoidHom] using hf k
  · intro k
    apply code_injective
    simpa only [packedConj_code, packedEval_code, MulEquiv.coe_toMonoidHom] using hb k

public theorem encoded_valid_words (e : Fin 3617) (h : EncodedValid e) :
    (words e).Valid (generator e) (nodeGenerator (targetIndex e))
      (MulAut.conj (conjugator e)).toMonoidHom := by
  have hd := rawWord_eq.trans fastWord_eq
  have hg : fastGenerator e = generator e := by
    funext k
    exact congrFun hd ((row e).generatorIndex k)
  have hn : fastNodeGenerator (targetIndex e) = nodeGenerator (targetIndex e) := by
    funext k
    exact congrFun hd (nodeGeneratorIndex (targetIndex e) k)
  have hc : fastConjugator e = conjugator e := congrFun hd (row e).conjugatorIndex
  have hv := packedWords_valid (words e) (fastGenerator e)
    (fastNodeGenerator (targetIndex e)) (fastConjugator e) h
  rw [hg, hn, hc] at hv
  exact hv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
public theorem encoded_valid_initial : ∀ i : Fin 100, EncodedValid (i.castLE (by decide)) := by decide +kernel


end ReeTwo.SylowModel.SmallEvenDescentEdges.Certificates
