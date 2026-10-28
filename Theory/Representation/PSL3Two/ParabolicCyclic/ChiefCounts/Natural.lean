module

public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Actor

/-!
# One noncentral chief factor on the natural three-space

The invariant plane v₂ = 0 is simple under the residual: the marked cubic
spans it from every nonzero vector. The remaining one-dimensional quotient
is central. Both assertions refer to the literal embedded residual action.

Source: Aschbacher–Smith 14.7.22(2), in the point/line marking of H.6.5.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Matrix Representation
namespace BinaryLinearThree.ParabolicCyclic.ChiefCounts

private theorem last_entry (g : Group) (hg : g ∈ Matrix.PSL3Two.lineParabolicSL) :
    g.val 2 2 = 1 := by
  obtain ⟨h20, h21⟩ := (Matrix.PSL3Two.mem_lineParabolicSL_iff g).mp hg
  have hn : g.val 2 2 ≠ 0 := by
    intro h0
    have hd := g.property
    change g.val.det = 1 at hd
    rw [Matrix.det_fin_three, h20, h21, h0] at hd
    norm_num at hd
  exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hn

def naturalPlane : Subrepresentation (W.comp actor.subtype) where
  toSubmodule := (LinearMap.proj (R := ZMod 2) (ι := Fin 3) 2).ker
  apply_mem_toSubmodule g v hv := by
    obtain ⟨h20, h21⟩ := (Matrix.PSL3Two.mem_lineParabolicSL_iff g.val).mp
      (actor_le_lineParabolic g.property)
    change v 2 = 0 at hv
    change (g.val.val *ᵥ v) 2 = 0
    simp [mulVec, dotProduct, Fin.sum_univ_three, h20, h21, hv]

set_option synthInstance.maxSize 256 in
private theorem plane_cyclic : ∀ x y : Vector, x 2 = 0 → x ≠ 0 → y 2 = 0 →
    ∃ a b : ZMod 2, y = a • x + b • W lineCycle x := by decide +kernel

theorem naturalPlane_chief_bot : (⊥ : Subrepresentation (W.comp actor.subtype)) ⋖ naturalPlane := by
  apply covBy_of_eq_or_eq
  · apply lt_of_le_not_ge bot_le
    intro h
    have hh := h (show (![1, 0, 0] : Vector) ∈ naturalPlane from rfl)
    have he : (![1, 0, 0] : Vector) = 0 := hh
    have := congrFun he 0
    norm_num at this
  · intro U _ hU
    by_cases he : U ≤ ⊥
    · exact Or.inl (le_antisymm he bot_le)
    · right
      apply le_antisymm hU
      obtain ⟨x, hx, hxn⟩ := SetLike.not_le_iff_exists.mp he
      intro y hy
      obtain ⟨a, b, rfl⟩ := plane_cyclic x y (hU hx) hxn hy
      have hc := U.apply_mem_toSubmodule ⟨lineCycle, lineCycle_mem_actor⟩ hx
      exact U.toSubmodule.add_mem (U.toSubmodule.smul_mem a hx)
        (U.toSubmodule.smul_mem b hc)

theorem naturalPlane_chief_top : naturalPlane ⋖ (⊤ : Subrepresentation (W.comp actor.subtype)) := by
  apply covBy_of_eq_or_eq
  · apply lt_of_le_not_ge le_top
    intro h
    have hh : (![0, 0, 1] : Vector) ∈ naturalPlane := h Submodule.mem_top
    change (1 : ZMod 2) = 0 at hh
    exact one_ne_zero hh
  · intro U hU _
    by_cases he : U ≤ naturalPlane
    · exact Or.inl (le_antisymm he hU)
    · right
      apply top_unique
      obtain ⟨x, hx, hxn⟩ := SetLike.not_le_iff_exists.mp he
      have hx2 : x 2 = 1 :=
        (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hxn
      intro y _
      have hy : y - y 2 • x ∈ naturalPlane := by
        change y 2 - y 2 * x 2 = 0
        simp [hx2]
      have hh := U.toSubmodule.add_mem (hU hy) (U.toSubmodule.smul_mem (y 2) hx)
      rw [sub_add_cancel] at hh
      exact hh

theorem naturalPlane_noncentral : ¬ Central (⊥ : Subrepresentation (W.comp actor.subtype)) naturalPlane := by
  intro h
  have hh := h ⟨lineCycle, lineCycle_mem_actor⟩ (![1, 0, 0] : Vector) rfl
  have he : W lineCycle (![1, 0, 0] : Vector) - ![1, 0, 0] = 0 := hh
  have hn : W lineCycle (![1, 0, 0] : Vector) - ![1, 0, 0] ≠ 0 := by decide
  exact hn he

theorem naturalPlane_central_top : Central naturalPlane (⊤ : Subrepresentation (W.comp actor.subtype)) := by
  intro g v _
  have hg := actor_le_lineParabolic g.property
  obtain ⟨h20, h21⟩ := (Matrix.PSL3Two.mem_lineParabolicSL_iff g.val).mp hg
  have h22 := last_entry g.val hg
  change (g.val.val *ᵥ v) 2 - v 2 = 0
  simp [mulVec, dotProduct, Fin.sum_univ_three, h20, h21, h22]

/-- The full flag has a noncentral plane and a central one-dimensional quotient. -/
def naturalSeries : Series (W.comp actor.subtype) where
  length := 2
  toFun := ![⊥, naturalPlane, ⊤]
  step i := by
    fin_cases i
    · exact naturalPlane_chief_bot
    · exact naturalPlane_chief_top

theorem natural_count : HasCount (W.comp actor.subtype) 1 := by
  refine ⟨naturalSeries, rfl, rfl, ?_⟩
  have h : naturalSeries.count = ({0} : Finset (Fin 2)).card := by
    apply Series.count_eq_card
    intro i
    fin_cases i
    · change (0 : Fin 2) ∈ ({0} : Finset (Fin 2)) ↔ ¬ Central ⊥ naturalPlane
      exact iff_of_true (by decide) naturalPlane_noncentral
    · change (1 : Fin 2) ∈ ({0} : Finset (Fin 2)) ↔ ¬ Central naturalPlane ⊤
      exact iff_of_false (by decide) (not_not_intro naturalPlane_central_top)
  exact h.trans (by decide)

end BinaryLinearThree.ParabolicCyclic.ChiefCounts
