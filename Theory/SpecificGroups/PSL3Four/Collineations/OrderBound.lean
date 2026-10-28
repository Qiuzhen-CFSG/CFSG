module

public import Theory.SpecificGroups.PSL3Four.Collineations.FrameRigidity

/-!
# Bounding the incidence collineation group of PG(2,4)

Every collineation is a product of a projective matrix collineation and a
pointwise frame fixer. The former have at most 60,480 possibilities and
the latter at most two. Thus the full incidence group has order at most
120,960, without identifying it with a semilinear group.

This is the model-side counting step used for Aschbacher–Smith F.4.8(2),
printed p.278. Its consumer uses the bound to remove the outer action from
a perfect completion.
-/

namespace Configuration.PlaneFour
open Matrix.PSL3Four
noncomputable section
local instance : DecidableEq F := Classical.decEq _

public theorem card_fullCollineation_le : Nat.card FullCollineation ≤ 120960 := by
  let f : PGL × FrameFixer → FullCollineation := fun a => pglCollineation a.1 * a.2.val
  have hf : Function.Surjective f := by
    intro c
    obtain ⟨a,ha⟩ := exists_projectiveLinear_frame c
    let s := (pglCollineation a)⁻¹ * c
    have hs : ∀ i : Fin 4, Collineation.pointHom PG PG s (frame i) = frame i := by
      intro i
      simp only [s, map_mul, map_inv, Equiv.Perm.mul_apply]
      rw [← ha i]
      exact (Collineation.pointHom PG PG (pglCollineation a)).symm_apply_apply _
    exact ⟨(a,⟨s,hs⟩), by dsimp [f,s]; simp⟩
  have hb := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_prod, card_PGL] at hb
  have hc := card_frameFixer_le_two
  omega
end
end Configuration.PlaneFour
