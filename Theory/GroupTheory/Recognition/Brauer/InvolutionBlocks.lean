module
public import Theory.GroupTheory.Recognition.Brauer.PlaneData
public import Theory.GroupTheory.ConjugateCosetBlocks

/-!
# Unique point and line containing an involution

Brauer, *On finite Desarguesian planes I*, (2A)–(2B), pp. 118–119,
shows that every involution belongs to exactly one point and exactly one
line. Here points and lines are the actual conjugate subsets of `jM` and
`jMstar` from `BrauerPlaneSeed`, and belonging to their underlying sets is
distinct from the incidence relation between points and lines.

Global involution fusion conjugates `j` to the given involution, yielding
existence of both containing subsets. The coset block theorem shows that
two conjugates of either base coset are equal or disjoint, yielding
uniqueness. The same argument handles the point and line families, without
requiring the later projective-plane postulates.
-/

open scoped Pointwise

namespace Theory.GroupTheory

private theorem existsUnique_orbit_block {K X : Type*} [Group K] [MulAction K X]
    (B : Set X) (hB : MulAction.IsBlock K B) {a x : X}
    (ha : a ∈ B) (hx : x ∈ MulAction.orbit K a) :
    ∃! p : ↥(MulAction.orbit K B), x ∈ (p : Set X) := by
  obtain ⟨g, rfl⟩ := hx
  have hg : g • a ∈ g • B := Set.smul_mem_smul_set ha
  refine ⟨⟨g • B, ⟨g, rfl⟩⟩, hg, ?_⟩
  intro p hp
  obtain ⟨h, hh⟩ := p.property
  apply Subtype.ext
  change (p : Set X) = g • B
  rw [← hh]
  exact hB.smul_eq_smul_of_nonempty ⟨g • a, by simpa only [hh] using hp, hg⟩

namespace BrauerPlaneSeed

/-- Brauer I, after (2B): an involution belongs to a unique point and a
unique line of the original conjugate-coset geometry. -/
public theorem existsUnique_blocks_of_involution {G : Type*} [Group G] [Finite G]
    (S : BrauerPlaneSeed G) {x : G} (hx : orderOf x = 2) :
    (∃! p : S.Point, x ∈ (p : Set G)) ∧ (∃! l : S.Line, x ∈ (l : Set G)) := by
  have horbit : x ∈ MulAction.orbit (ConjAct G) S.j := by
    obtain ⟨g, hg⟩ := isConj_iff.mp (S.involutions_isConj S.j_order hx)
    exact ⟨ConjAct.toConjAct g, hg⟩
  have hM : S.j ∈ S.basePoint := by
    exact Set.mem_smul_set.mpr ⟨1, S.M.one_mem, mul_one S.j⟩
  have hMstar : S.j ∈ S.baseLine := by
    exact Set.mem_smul_set.mpr ⟨1, S.Mstar.one_mem, mul_one S.j⟩
  exact ⟨existsUnique_orbit_block S.basePoint
      (isBlock_conjugate_coset_of_centralizer_normalizes S.M S.j
        S.centralizer_le_normalizer_M S.disjoint_M_centralizer) hM horbit,
    existsUnique_orbit_block S.baseLine
      (isBlock_conjugate_coset_of_centralizer_normalizes S.Mstar S.j
        S.centralizer_le_normalizer_Mstar S.disjoint_Mstar_centralizer) hMstar horbit⟩

end BrauerPlaneSeed
end Theory.GroupTheory
