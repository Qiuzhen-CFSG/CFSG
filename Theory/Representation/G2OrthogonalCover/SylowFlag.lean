module

public import Theory.Representation.G2OrthogonalCover.SylowFlag.Conjugation

/-!
# Every derived-Sylow flag in the G₂′ orthogonal cover

The marked calculation and conjugation transport establish the actual source
geometry for every Sylow subgroup of the derived split G₂ group. Both the
existence and uniqueness of the selected one- and two-spaces are proved. The
first preimage is the fixed two-space with a unique singular point, and the
central long-root displacement plane complements the scalar radical in the
second preimage, always using the original projection mk.

Source: Aschbacher–Smith, I.2.3(1)(a),(c), printed p.413 / PDF p.424.
Universal-cover and original ambient-group assembly are separate consumers.
-/

@[expose] public section
noncomputable section

open Atlas.SplitOctonion Representation Representation.OneCohomology
namespace Atlas.G2.Natural.OrthogonalCover.SylowFlag
variable (F : Type*) [Field F] [CharP F 2]

/-- The source-selected flag for every actual derived Sylow, together with
I.2.3(1)(a),(c) on the literal trace-zero cover. The witnesses are transported
by one derived-group element, so neither a Sylow alignment nor an extra
model-geometry hypothesis is required. -/
theorem selected_flag_geometry [Finite F] (Q : Sylow 2 (D F))
    (V1 V2 : Submodule F (Space F))
    (h1 : ∀ t : (Q : Subgroup (D F)), V1 ≤ V1.comap (derivedAction F t.val))
    (d1 : Module.finrank F V1 = 1)
    (h2 : ∀ t : (Q : Subgroup (D F)), V2 ≤ V2.comap (derivedAction F t.val))
    (d2 : Module.finrank F V2 = 2) :
    ∃ g : D F,
      (Q : Subgroup (D F)) = movedSylow F g ∧
      V1 = movedLine F g ∧ V2 = movedPlane F g ∧
      movedRoot F g ≤ (Subgroup.center (Q : Subgroup (D F))).map (Q : Subgroup (D F)).subtype ∧
      V1.comap (mk F) = fixed ((OrthogonalCover.action F).comp (Q : Subgroup (D F)).subtype) ∧
      V1.comap (mk F) = movedPoint F g ⊔ scalarLine F ∧
      Disjoint (movedPoint F g) (scalarLine F) ∧
      Module.finrank F (movedPoint F g) = 1 ∧
      (∀ x ∈ movedPoint F g, form F x = 0) ∧
      (∀ R : Submodule F (TraceZero F), R ≤ V1.comap (mk F) →
        Module.finrank F R = 1 → (∀ x ∈ R, form F x = 0) → R = movedPoint F g) ∧
      Module.finrank F (Coinvariants.ker ((OrthogonalCover.action F).comp (movedRoot F g).subtype)) = 2 ∧
      (∀ x ∈ Coinvariants.ker ((OrthogonalCover.action F).comp (movedRoot F g).subtype), form F x = 0) ∧
      Disjoint (Coinvariants.ker ((OrthogonalCover.action F).comp (movedRoot F g).subtype)) (scalarLine F) ∧
      V2.comap (mk F) =
        Coinvariants.ker ((OrthogonalCover.action F).comp (movedRoot F g).subtype) ⊔ scalarLine F := by
  obtain ⟨g,hg⟩ := exists_marking F Q
  have e1 : V1 = movedLine F g := movedLine_unique F g V1 (hg ▸ h1) d1
  have e2 : V2 = movedPlane F g := movedPlane_unique F g V2 (hg ▸ h2) d2
  refine ⟨g,hg,e1,e2,?_,?_,?_,movedPoint_disjoint F g,movedPoint_finrank F g,
    movedPoint_singular F g,?_,?_⟩
  · rw [hg]
    exact movedRoot_central F g
  · rw [hg,e1]
    exact (moved_cover_fixed F g).symm
  · rw [e1]
    exact movedLine_preimage F g
  · rw [e1]
    exact moved_singular_unique F g
  · rw [e2]
    exact movedRoot_geometry F g

/-- Existence as well as uniqueness of the invariant line and plane for every
Sylow subgroup; both are the marked spaces under the same actual conjugation. -/
theorem exists_unique_flag [Finite F] (Q : Sylow 2 (D F)) :
    ∃ g : D F, (Q : Subgroup (D F)) = movedSylow F g ∧
      Module.finrank F (movedLine F g) = 1 ∧ Module.finrank F (movedPlane F g) = 2 ∧
      (∀ t : (Q : Subgroup (D F)), movedLine F g ≤
        (movedLine F g).comap (derivedAction F t.val)) ∧
      (∀ t : (Q : Subgroup (D F)), movedPlane F g ≤
        (movedPlane F g).comap (derivedAction F t.val)) ∧
      (∀ W : Submodule F (Space F),
        (∀ t : (Q : Subgroup (D F)), W ≤ W.comap (derivedAction F t.val)) →
        Module.finrank F W = 1 → W = movedLine F g) ∧
      (∀ W : Submodule F (Space F),
        (∀ t : (Q : Subgroup (D F)), W ≤ W.comap (derivedAction F t.val)) →
        Module.finrank F W = 2 → W = movedPlane F g) := by
  obtain ⟨g,hg⟩ := exists_marking F Q
  refine ⟨g,hg,movedLine_finrank F g,movedPlane_finrank F g,?_,?_,?_,?_⟩
  all_goals rw [hg]
  · exact movedLine_invariant F g
  · exact movedPlane_invariant F g
  · exact movedLine_unique F g
  · exact movedPlane_unique F g

end Atlas.G2.Natural.OrthogonalCover.SylowFlag
