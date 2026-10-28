module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowGeometry
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport

/-!
# The two-core at every natural binary line

Even permutation transitivity marks any natural line by the canonical
line. The already-proved conjugation formula for its stabilizer two-core
therefore transports the concrete order eight to every line, preserving
the actual representation stabilizer.
Source: Aschbacher--Smith13.7.9(1) and13.7.12(1), printed pp.941--942.
-/

public section

namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Subgroup BinaryPermutation Representation.BinaryOffender
open NaturalGeometry NaturalPairing
 theorem line_core_card (P:Submodule (ZMod 2) (natural (Fin 6)))
    (hP:Module.finrank (ZMod 2) P=1) :
    Nat.card ((subspaceStabilizer (naturalRepresentation (Fin 6)) P).pCoreIn 2)=8 := by
  have hP0:P≠⊥:=by intro he;rw [he,finrank_bot] at hP;contradiction
  obtain ⟨v,hv,hv0⟩:=(Submodule.ne_bot_iff P).mp hP0
  obtain ⟨g,hg⟩:=NaturalTransport.exists_even_image v hv0
  have hmark:canonicalLine.map (naturalRepresentation (Fin 6) g.val)=P := by
    rw [canonicalLine,Submodule.map_span,Set.image_singleton,hg]
    exact (eq_span_singleton_of_mem_of_finrank_eq_one hP hv hv0).symm
  rw [←hmark]
  change Nat.card ((flagStabilizer (move g.val canonicalLine)).pCoreIn 2)=8
  rw [line_core_of_marking,card_map_of_injective (MulAut.conj g.val).injective,pointCore_card]
end Theory.SpecificGroups.SymmetricSix.BinaryFlags
