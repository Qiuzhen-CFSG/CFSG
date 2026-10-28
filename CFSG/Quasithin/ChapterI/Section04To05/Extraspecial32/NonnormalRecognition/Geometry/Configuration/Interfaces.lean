module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Definitions

/-!+# The remaining middle-normalizer output of source Lemma 3.1

The endpoint construction supplies a literal second intersection F and
E ∩ F = ⟨z⟩. The splitting argument of 2.8 supplies complements in both
endpoint normalizers. The record below isolates the independent remaining
argument: the elementary sixteen A, its ambient normalizer and the exact
fusion union. It is an output contract, not an existence theorem.

The middle-normalizer producer may take a complement to E explicitly;
`Configuration` retains its discharge and final assembly. No recognition
of the ambient group or D-system is part of this contract.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois
J. Math. 47 (2003), Lemma 3.1, printed pp.36–37.
-/

@[expose] public section

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration

open Subgroup

variable {G : Type*} [Group G]

/-- The middle subgroup and fusion conclusions, with the second endpoint fixed. -/
structure MiddleData (z g y : G) where
  fusion_union : ∀ x : G, (x ∈ coreInG z ∧ IsConj z x) ↔
    (x ∈ coreIntersection z g ∨ x ∈ coreIntersection z y) ∧ x ≠ 1
  A : Subgroup G
  elementary : IsElementaryAbelian 2 A
  card : Nat.card A = 16
  self_centralizing : centralizer (A : Set G) = A
  normalizer_quotient : Nonempty
    ((normalizer (A : Set G) ⧸ A.subgroupOf (normalizer (A : Set G))) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
  S : Sylow 2 (Centralizer z)
  A_le_sylow : A ≤ (S : Subgroup (Centralizer z)).map (Centralizer z).subtype
  normalizer_intersection : Centralizer z ⊓ normalizer (A : Set G) =
    (S : Subgroup (Centralizer z)).map (Centralizer z).subtype

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration

end
