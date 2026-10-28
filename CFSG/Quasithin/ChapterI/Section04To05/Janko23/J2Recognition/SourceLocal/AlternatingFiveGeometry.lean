module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.AlternatingFiveGeometry.Vertices
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.AlternatingFiveGeometry.Normalizer
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.AlternatingFiveGeometry.Edges

/-!
# Finite A₅ geometry for the J₂ local subgroup

The local cubic vertices and ordered A₄ edges are single K-orbits, with actual
conjugating elements. Restriction identifies the vertex overlap with the
intrinsic S₃ normalizer and proves its maximality and noncentral action.
The pointwise edge overlap is trivial; the setwise overlap is an embedded C₂
with a specified reversing generator. Two local triangles have joins equal
to the selected A₄ and to K respectively, and cannot be fused by the ambient
setwise edge stabilizer.

Sylow conjugacy and small checked permutation identities establish these
facts in the actual alternating group, then the restriction equivalences
retain their embeddings in G. The dihedral marking inside an A₅ edge fixer
constructs an `EdgeFrame`. Its applications use the literal `K = C_G(B)`;
the theorem below discharges all three finite A₅ premises of
`SourceLocal.localDataOfCalculations`. The edge and triangle theorems also
apply directly to `LocalData.toSystem.localEdge`.

The A₅ identifications of the ambient edge fixer and K remain explicit
prime-local inputs to the final source assembly. These finite calculations
do not assert the ambient two-orbit theorem of 47.6 or J₂ uniqueness itself.

Source: Aschbacher, *Sporadic Groups* (1994), 47.6 and 47.10,
pp.264, 266–267.
-/

public section

open Subgroup Theory.GroupTheory.GraphUniquenessSystem

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeFrame

variable {G : Type*} [Group G] [Finite G] {D : Seed G} (F : EdgeFrame D)

/-- The finite A₅ inputs `hinverts`, `hmax`, and `hswap` for
`SourceLocal.localDataOfCalculations`, proved for the literal edge frame. -/
theorem local_calculations
    (he : Nonempty (edgeFixer G D.base F.y ≃* alternatingGroup (Fin 5)))
    (eK : F.K ≃* alternatingGroup (Fin 5)) :
    (¬ F.K ⊓ normalizer (D.X : Set G) ≤ centralizer (D.X : Set G)) ∧
      F.K ⊓ normalizer (D.X : Set G) ⋖ F.K ∧
      ∃ t : F.K, (t : G) • D.base = F.y ∧ (t : G) • F.y = D.base := by
  obtain ⟨t, _, hx, hy⟩ := F.exists_edge_reversal he eK
  exact ⟨F.vertex_overlap_not_le_centralizer he eK,
    F.vertex_overlap_maximal he eK, t, hx, hy⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeFrame
