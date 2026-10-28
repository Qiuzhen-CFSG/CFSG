module

public import CFSG.Quasithin.Chapter16.Section01To02.CoverAndSylowElimination.Basic
public import Theory.GroupAction.AutomorphismOddOuter

/-!
# The precise Suzuki cover inputs and remaining local constructions

The model is the actual matrix group `SuzukiMatrixGroup 1 = Sz(8)`.
The input records the two clauses of I.2.2(4), the elementary center from
16.1.2, and the involution geometry and automorphism facts of that model.
The eight-element subgroup is a subgroup of the actual central quotient,
and is exactly the set of elements squaring to one in its Sylow image.
No rank bound on an arbitrary ambient subgroup is an input.

`CoverStructure` and `CoverPlacement` specify intermediate conclusions.
`CoverStructure.lean` constructs the former from this precise intrinsic input
and the local component setup. `CoverPlacement.lean` constructs the latter
from the external involution and Sylow conjugacy.

Source: Aschbacher–Smith, I.2.2(4), p.409, and proof of 16.2.11, p.1176.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CoverAndSylowElimination

open Subgroup ChapterI.Section06To08

variable {G : Type*} [Group G]

/-- Precise intrinsic cover and quotient facts. Each field is a model
obligation for the section owner; neither the starred action conclusion nor
the elementary structure of `sylowOmega T L` is assumed. -/
structure SuzukiCoverInput (T : Sylow 2 G) (L : Subgroup G) : Prop where
  quotient_model : Nonempty ((L ⧸ center L) ≃*
    BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)
  center_elementary : IsElementaryAbelian 2 (center L)
  center_sylow : (center (componentSylow T L)).map (componentSylow T L).subtype =
    componentCenter L
  involutions_lift : ∀ x : L, (QuotientGroup.mk' (center L) x) ^ 2 = 1 →
    ∃ y : L, y ^ 2 = 1 ∧
      QuotientGroup.mk' (center L) y = QuotientGroup.mk' (center L) x
  quotient_involutions : ∃ B : Subgroup (L ⧸ center L),
    IsElementaryAbelian 2 B ∧ Nat.card B = 8 ∧
      ∀ q : L ⧸ center L, q ∈ B ↔
        q ∈ ((T : Subgroup G).subgroupOf L).map (QuotientGroup.mk' (center L)) ∧ q ^ 2 = 1
  odd_outer : Odd (MulAut.conj : L →* MulAut L).range.index
  automorphism_rank : primeRank 2 (MulAut L) = 3

/-- The elementary structure and the starred assertion in 16.2.11, including
its product containment and its conjugates. This is constructed in `CoverStructure.lean`. -/
structure CoverStructure (T : Sylow 2 G) (L : Subgroup G) : Prop where
  elementary : IsElementaryAbelian 2 (sylowOmega T L)
  center_le : componentCenter L ≤ sylowOmega T L
  center_index : (componentCenter L).relIndex (sylowOmega T L) = 8
  elementary_normalizer_action : ∀ (g : G) (A : Subgroup G),
    IsElementaryAbelian 2 A →
    A ≤ conjSubgroup ((T : Subgroup G) ⊓ normalizer (L : Set G)) g →
    A ≤ conjSubgroup (sylowOmega T L ⊔ commutingSylow T L) g ∧
      A ≤ centralizer (conjSubgroup (sylowOmega T L) g : Set G)

/-- The explicit placement needed just before the rank comparison in
16.2.11. In particular `X` is the relative normalizer, not an arbitrary
subgroup satisfying the desired conclusions. `CoverStructure.placement`
constructs this witness from the actual earlier local conclusions. -/
def CoverPlacement (T : Sylow 2 G) (z u : G) (L : Subgroup G) : Prop :=
  ∃ g ∉ localComponentNormalizer z L,
    let Z := sylowOmega T L
    let X := Z ⊓ normalizer (conjSubgroup L g : Set G)
    let V := conjSubgroup Z g
    Z ≤ conjSubgroup (T : Subgroup G) g ∧
    X ≤ centralizer (V : Set G) ∧
    ¬ X ≤ componentCenter L ∧ X.relIndex Z ≤ 2 ∧
    V ≤ localComponentNormalizer z L ⊓ normalizer (L : Set G) ⊓
      normalizer (conjSubgroup L u : Set G)

end CFSG.Quasithin.Chapter16.CoverAndSylowElimination
