module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.Normalizer
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceColumn

/-!
# Orienting the Mathieu marking and separating its two rectangular groups

The checked inverse-transpose marking interchanges all four root subgroups.
The 21/45 alternative therefore chooses an orientation of the original marking,
with no new local isomorphism choice. Ambient conjugation preserves the number
of conjugates of the distinguished involution in a subgroup; the unequal counts
then exclude conjugacy of the two rectangles.

Source: Aschbacher, *Sporadic Groups* (1994), 39.1(4), 39.6(1), and 40.5(2),
printed pp.213–219. Weak closure and the ambient normalizer classifications are
separate obligations; they are not part of the orientation definition.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear
variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

/-- The marking may only be retained or interchanged by the checked graph automorphism. -/
structure OrientedMarking where
  marking : MarkedCentralizer z
  marking_eq : marking = F ∨ marking = oppositeMarking F
  counts : MathieuFusionOrientation marking

/-- Orient the original marking so that the literal plane has 21 fused points
and the literal three-space has 45. -/
def orient (h : F.MathieuFusion) : OrientedMarking F := by
  classical
  by_cases hfirst : MathieuFusionOrientation F
  · exact ⟨F, Or.inl rfl, hfirst⟩
  · refine ⟨oppositeMarking F, Or.inr rfl, ?_⟩
    have hsecond := h.resolve_left hfirst
    simpa only [MathieuFusionOrientation, MarkedCentralizer.fusion,
      oppositeMarking_plane, oppositeMarking_threeSpace] using hsecond.symm

/-- Orientation changes all four literal marked subgroups together. -/
theorem oriented_subgroups (D : OrientedMarking F) :
    (D.marking.row = F.row ∧ D.marking.column = F.column ∧
      D.marking.plane = F.plane ∧ D.marking.threeSpace = F.threeSpace) ∨
    (D.marking.row = F.column ∧ D.marking.column = F.row ∧
      D.marking.plane = F.threeSpace ∧ D.marking.threeSpace = F.plane) := by
  rcases D.marking_eq with h | h
  · left; simp only [h, and_self]
  · right
    simp only [h, oppositeMarking_row, oppositeMarking_column,
      oppositeMarking_plane, oppositeMarking_threeSpace, and_self]

/-- Ambient conjugation carries the literal fusion subset to the fusion subset
of the conjugate subgroup. The distinguished point is not changed. -/
theorem fusion_map_conj (A : Subgroup G) (g : G) :
    F.fusion (A.map (MulAut.conj g).toMonoidHom) = MulAut.conj g '' F.fusion A := by
  ext x
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hconj⟩
    exact ⟨a, ⟨ha, hconj.trans (isConj_iff.mpr ⟨g, rfl⟩).symm⟩, rfl⟩
  · rintro ⟨a, ⟨ha, hconj⟩, rfl⟩
    exact ⟨mem_map_of_mem _ ha, hconj.trans (isConj_iff.mpr ⟨g, rfl⟩)⟩

/-- The ambient fusion count is invariant under conjugacy of the actual subgroup. -/
theorem fusion_ncard_map_conj (A : Subgroup G) (g : G) :
    (F.fusion (A.map (MulAut.conj g).toMonoidHom)).ncard = (F.fusion A).ncard := by
  rw [fusion_map_conj]
  exact Set.ncard_image_of_injective _ (MulAut.conj g).injective

/-- Source 39.6(1) in the Mathieu branch: the unequal ambient fusion counts
separate the actual rectangular groups, without a weak-closure assumption. -/
theorem planes_not_conjugate (h : F.MathieuFusion) (g : G) :
    F.plane.map (MulAut.conj g).toMonoidHom ≠ F.threeSpace := by
  intro he
  have hc := fusion_ncard_map_conj F F.plane g
  rw [he] at hc
  rcases h with h | h <;> rw [h.1, h.2] at hc <;> omega

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
