module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.EdgeCentralizer
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# The literal local subgroup in the J₂ uniqueness construction

An edge frame consists of an adjacent vertex Y and a dihedral subgroup
B of order ten in the actual pointwise edge fixer. The local group is
C_G(B), exactly as in Aschbacher, *Sporadic Groups* (1994), 47.10, p.266.

Perfectness of the A₅ edge fixer puts X and Y inside this centralizer.
Its vertex overlap is the image of the intrinsic normalizer of X in K,
retaining the exact subgroup maps needed to apply finite A₅ geometry.
Existence of a frame and the A₅ identification of K remain upstream work.
-/

@[expose] public section

open Subgroup Theory.GroupTheory.GraphUniquenessSystem
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
variable {G : Type*} [Group G] [Finite G]

structure EdgeFrame (D : Seed G) where
  y : D.Vertex
  adjacent : D.graph.Adj D.base y
  B : Subgroup G
  B_le : B ≤ edgeFixer G D.base y
  dihedral : Nonempty (B ≃* DihedralGroup 5)

namespace EdgeFrame
variable {D : Seed G} (F : EdgeFrame D)

def K : Subgroup G := centralizer (F.B : Set G)

theorem card_B : Nat.card F.B = 10 := by
  rw [Nat.card_congr F.dihedral.some.toEquiv, Nat.card_eq_fintype_card,
    DihedralGroup.card]

theorem endpoints_le (he : Nonempty (edgeFixer G D.base F.y ≃* alternatingGroup (Fin 5))) :
    D.X ⊔ F.y.val ≤ F.K :=
  join_le_centralizer_of_le_edgeFixer D D.base F.y he F.B F.B_le

theorem vertex_overlap (he : Nonempty (edgeFixer G D.base F.y ≃* alternatingGroup (Fin 5))) :
    F.K ⊓ normalizer (D.X : Set G) =
      (normalizer ((D.X.subgroupOf F.K : Subgroup F.K) : Set F.K)).map F.K.subtype := by
  rw [← subgroupOf_normalizer_eq (le_sup_left.trans (F.endpoints_le he)), subgroupOf_map_subtype]
  exact inf_comm _ _

end EdgeFrame
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
