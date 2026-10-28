module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.MarkedTransport

/-!
# The literal marked quotient cardinal

The vector-stabilizer transport identifies the quotient of the marked
centralizer by the centralizer of the original module with the point
stabilizer in the finite model.  This leaf records the cardinal identity in
the exact subgroup types used by Case-I residual intersection.

Source: Aschbacher--Smith, original 15.1.16--18, printed p.1092.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G]

/-- The literal quotient `C_M(Z₁) / C_M(V)` has the cardinality of the
point-stabilizer selected in the model. -/
theorem marked_quotient_card
    (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (v : Additive V) (K : Subgroup (internalActionImage M V hn))
    (hK : ∀ d, d ∈ K ↔ imageRepresentation M V hn d v = v)
    (_hZV : zpowers (v.toMul : G) ≤ V) :
    Nat.card ((M ⊓ centralizer (zpowers (v.toMul : G) : Set G) : Subgroup G) ⧸
      (M ⊓ centralizer (V : Set G)).subgroupOf
        (M ⊓ centralizer (zpowers (v.toMul : G) : Set G))) = Nat.card K := by
  let C := M ⊓ centralizer (zpowers (v.toMul : G) : Set G)
  let N := M ⊓ centralizer (V : Set G)
  have hNsub : N.subgroupOf C = (centralizer (V : Set G)).subgroupOf C := by
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      exact ⟨x.property.1, hx⟩
  obtain ⟨q,hq,hker,_⟩ := vector_stabilizer_projection M V hn v K hK
  have hcard : Nat.card (C ⧸ q.ker) = Nat.card K :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv
  change Nat.card (C ⧸ N.subgroupOf C) = Nat.card K
  rw [hNsub, ← hker]
  exact hcard

end CFSG.Quasithin.Chapter15.Section01
