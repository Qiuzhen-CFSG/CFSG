module

public import Theory.GroupAction.FullyMovedIrreducibleCentralizer
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Fully moved sections in groups with self-centralizing two-core

A full Sylow normalizing both B and its chosen elementary section E makes
O₂(G) normalize them. The commutator [O₂(G),B] lies in O₂(B), so if O₂(B)
fixes E, the commuting fixed-point argument makes O₂(G) fix E as well.
When the ambient core is self-centralizing, E therefore lies in its center.
This bounds the original chosen section without identifying it with a block.

The native consumer is the first J₄ involution centralizer in the inspection
of Aschbacher–Smith 10.2.9, printed pp.750–751; the fixed-point argument is
A.1.41 and C.1.11, printed pp.31,124.
-/

public section
open Subgroup
namespace Theory.GroupAction
variable {G : Type*} [Group G] [Finite G]

/-- A normalized chosen section is bounded by the center of the ambient two-core. -/
theorem fully_moved_irreducible_card_le_core_center
    (S : Sylow 2 G) (B E : Subgroup G) (hB : IsPPerfect 2 B)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hSE : (S : Subgroup G) ≤ normalizer (E : Set G))
    (hE : IsElementaryAbelian 2 E) (hEB : E ≤ B)
    (hcore : B.pCoreIn 2 ≤ centralizer (E : Set G)) (hmove : ⁅E,B⁆ = E)
    (hirr : ∀ N : Subgroup G, E ⊓ centralizer (B : Set G) ≤ N → N ≤ E →
      B ≤ normalizer (N : Set G) → N = E ⊓ centralizer (B : Set G) ∨ N = E)
    (hC : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    Nat.card E ≤ Nat.card (center (pCore 2 G)) := by
  let Q := pCore 2 G
  have hQS : Q ≤ S := pCore_isPGroup.le_sylow_of_normal S
  have hBQ : B ≤ normalizer (Q : Set G) := le_normalizer_of_normal
  have hcomm : ⁅Q,B⁆ ≤ B.pCoreIn 2 :=
    le_pCoreIn_of_normalizes
      (pCore_isPGroup.to_le (le_normalizer_iff_commutator_le_left.mp hBQ))
      (le_normalizer_iff_commutator_le_right.mp (hQS.trans hSB))
      (normalizer_commutator_ge_right Q B)
  have hCE : Q ≤ centralizer (E : Set G) :=
    centralizes_fully_moved_irreducible_section B Q E hB pCore_isPGroup hE hEB
      hBQ (hQS.trans hSE) (hcomm.trans hcore) hmove hirr
  have hEC : E ≤ centralizer (Q : Set G) := le_centralizer_iff.mp hCE
  have hEQ : E ≤ Q := hEC.trans hC
  have hz : E ≤ (center Q).map Q.subtype := by
    intro x hx
    refine ⟨⟨x,hEQ hx⟩,?_,rfl⟩
    exact mem_center_iff.mpr (fun q => Subtype.ext (hEC hx q q.property))
  have hh := card_le_of_le hz
  simpa only [card_map_of_injective Q.subtype_injective] using hh

end Theory.GroupAction
