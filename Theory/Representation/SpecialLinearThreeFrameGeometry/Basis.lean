module

public import Theory.Representation.SpecialLinearThreeFrameGeometry
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Bases adapted to an ordered SL₃ frame

One spanning vector from each of the three frame lines gives a basis: the
vectors span a space of dimension three. Root generation and projective
transitivity use the two orientations of this same coordinate identity.

Source: Aschbacher–Smith, G.1.1, printed p.327 / PDF p.338.
-/

@[expose] public section
noncomputable section
namespace Matrix.SpecialLinearGroup.FrameGeometry
open Module
variable {F : Type*} [Field F]

/-- A frame admits a basis whose three vectors span its marked lines. -/
theorem Frame.exists_basis (b : Frame F) :
    ∃ v : Basis (Fin 3) F (Fin 3 → F),
      ∀ i, Submodule.span F {v i} = b.point i := by
  have hex (i : Fin 3) : ∃ x : Fin 3 → F, Submodule.span F {x} = b.point i := by
    obtain ⟨x, _, hx⟩ := finrank_eq_one_iff'.mp (b.dimension i)
    refine ⟨x.val, le_antisymm ((Submodule.span_singleton_le_iff_mem _ _).mpr x.property) ?_⟩
    intro y hy
    obtain ⟨c, hc⟩ := hx ⟨y, hy⟩
    exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩
  choose x hx using hex
  have hspan : ⊤ ≤ Submodule.span F (Set.range x) := by
    rw [← b.span]
    have hi (i : Fin 3) : b.point i ≤ Submodule.span F (Set.range x) := by
      rw [← hx i]
      exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨i, rfl⟩)
    exact sup_le (sup_le (hi 0) (hi 1)) (hi 2)
  refine ⟨basisOfTopLeSpanOfCardEqFinrank x hspan (by simp), ?_⟩
  simpa using hx

/-- The adapted basis identity with the frame line on the left. -/
theorem Frame.exists_basis_lines (b : Frame F) :
    ∃ v : Basis (Fin 3) F (Fin 3 → F),
      ∀ i, b.point i = Submodule.span F {v i} := by
  obtain ⟨v, hv⟩ := b.exists_basis
  exact ⟨v, fun i => (hv i).symm⟩

end Matrix.SpecialLinearGroup.FrameGeometry
