module

public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.AutomizerConjugacy.FullStructure.Shifts

/-!
# Automorphisms fixing the two root coordinates

Every automorphism fixing x and y also fixes the center pointwise: each central
element is a commutator of an x-root and a y-root element. Its remaining central
displacement is additive on F₄². Thus it is exactly one of the central shifts.
This identifies the kernel needed to pass from a classification on the two root
coordinates to full automorphism normal forms.

Source motivation: Aschbacher, *Sporadic Groups* (1994), 8.15 and 46.14.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace Matrix.PSL3Four.RootNormalizerModel.AutomizerConjugacy.FullStructure
noncomputable section

theorem commutator_coordinates (q r : Root) :
    ⁅q, r⁆ = ⟨0, 0, q.x * r.y - r.x * q.y⟩ := by
  change MulAut.conj q r * r⁻¹ = _
  rw [conj_coordinates]
  apply SylowModel.U.ext
  · change r.x + -r.x = 0
    ring
  · change r.y + -r.y = 0
    ring
  · change (r.c + (q.x * r.y - r.x * q.y)) + (r.x * r.y - r.c) +
      r.x * -r.y = q.x * r.y - r.x * q.y
    ring

theorem exists_shift_of_fix_coordinates (a : MulAut Root)
    (hx : ∀ q : Root, (a q).x = q.x) (hy : ∀ q : Root, (a q).y = q.y) :
    ∃ l : Shift, a = shift l := by
  have hc (c : F) : a ⟨0, 0, c⟩ = ⟨0, 0, c⟩ := by
    have h := map_commutatorElement a (⟨c, 0, 0⟩ : Root) (⟨0, 1, 0⟩ : Root)
    simpa only [commutator_coordinates, hx, hy, mul_one, zero_mul, sub_zero] using h
  let lval : F × F → F := fun p => (a ⟨p.1, p.2, 0⟩).c
  have hform (q : Root) : (a q).c = q.c + lval (q.x, q.y) := by
    have hq : q = (⟨q.x, q.y, 0⟩ : Root) * ⟨0, 0, q.c⟩ := by
      apply SylowModel.U.ext <;> simp
    have h := congrArg SylowModel.U.c (map_mul a (⟨q.x, q.y, 0⟩ : Root) ⟨0, 0, q.c⟩)
    rw [← hq, hc] at h
    simpa only [SylowModel.mul_c, mul_zero, add_zero, zero_add, add_comm] using h
  let l : Shift :=
    { toFun := lval
      map_zero' := by
        change (a 1).c = 0
        rw [map_one]
        rfl
      map_add' := by
        rintro ⟨x, y⟩ ⟨z, w⟩
        have h := congrArg SylowModel.U.c (map_mul a (⟨x, y, 0⟩ : Root) ⟨z, w, 0⟩)
        rw [hform] at h
        simp only [SylowModel.mul_x, SylowModel.mul_y, SylowModel.mul_c, hx, hy,
          zero_add] at h
        change lval (x + z, y + w) = lval (x, y) + lval (z, w)
        change x * w + lval (x + z, y + w) = lval (x, y) + lval (z, w) + x * w at h
        linear_combination h }
  refine ⟨l, ?_⟩
  apply MulEquiv.ext
  intro q
  exact SylowModel.U.ext (hx q) (hy q) (hform q)

end
end Matrix.PSL3Four.RootNormalizerModel.AutomizerConjugacy.FullStructure
