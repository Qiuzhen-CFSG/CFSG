module
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.ElementarySubgroups
/-!
# Exchanging the two root planes through a central point

Every graph–field coset actor exchanges the two root planes. Multiplying
by a suitable diagonal scalar makes it fix any specified central point.
These are actual elements of the marked split normalizer, supplying the
local incidence step in the normalizer fusion argument.

Source: Aschbacher, *Sporadic Groups* (1994), 46.14(2–4), pp.257–258.
-/

public noncomputable section
open Subgroup
namespace Matrix.PSL3Four.RootNormalizerModel
open Cubic Theory.GroupTheory.HyperbolicRecognition

theorem graph_coset_exchanges (a : Fˣ × Fˣ) :
    rootPlane₁.map (diagonalHom a * graphField).toMonoidHom = rootPlane₂ ∧
    rootPlane₂.map (diagonalHom a * graphField).toMonoidHom = rootPlane₁ := by
  constructor
  · apply eq_of_le_of_card_ge
    · rintro q ⟨r,hr,rfl⟩
      apply (mem_rootPlane₂ _).mpr
      change (a.1 : F) * fieldFrobenius r.y = 0
      rw [(mem_rootPlane₁ r).mp hr,map_zero,mul_zero]
    · rw [card_map_of_injective (diagonalHom a * graphField).injective,
        card_rootPlane₁,card_rootPlane₂]
  · apply eq_of_le_of_card_ge
    · rintro q ⟨r,hr,rfl⟩
      apply (mem_rootPlane₁ _).mpr
      change (a.2 : F) * fieldFrobenius r.x = 0
      rw [(mem_rootPlane₂ r).mp hr,map_zero,mul_zero]
    · rw [card_map_of_injective (diagonalHom a * graphField).injective,
        card_rootPlane₁,card_rootPlane₂]

/-- A member of the actual actor exchanges both planes and fixes a specified central point. -/
theorem exists_exchange_fixing_center (z : Root) (hz : z ∈ center Root) :
    ∃ s : actor, (s : MulAut Root) z = z ∧
      rootPlane₁.map (s : MulAut Root).toMonoidHom = rootPlane₂ ∧
      rootPlane₂.map (s : MulAut Root).toMonoidHom = rootPlane₁ := by
  have hzxy := (SylowModel.mem_center_U z).mp hz
  have step (a : Fˣ × Fˣ) (hc : (a.1 : F) * a.2 * fieldFrobenius z.c = z.c) :
      ∃ s : actor, (s : MulAut Root) z = z ∧
        rootPlane₁.map (s : MulAut Root).toMonoidHom = rootPlane₂ ∧
        rootPlane₂.map (s : MulAut Root).toMonoidHom = rootPlane₁ := by
    let s : actor := ⟨diagonalHom a * graphField,
      actor.mul_mem (mem_sup_left ⟨a,rfl⟩) (mem_sup_right (mem_zpowers _))⟩
    refine ⟨s,?_,graph_coset_exchanges a⟩
    apply SylowModel.U.ext
    · change (a.1 : F) * fieldFrobenius z.y = z.x
      simp [hzxy.1,hzxy.2]
    · change (a.2 : F) * fieldFrobenius z.x = z.y
      simp [hzxy.1,hzxy.2]
    · change ((a.1 : F) * a.2) * fieldFrobenius (z.x*z.y-z.c) = z.c
      simpa [hzxy.1,hzxy.2,CharTwo.neg_eq] using hc
  by_cases hc : z.c = 0
  · apply step (1,1)
    simp [hc]
  · apply step ((Units.mk0 z.c hc)⁻¹,1)
    simp only [Units.val_inv_eq_inv_val,Units.val_mk0,Units.val_one,mul_one,
      fieldFrobenius_apply,pow_two]
    rw [←mul_assoc,inv_mul_cancel₀ hc,one_mul]
end Matrix.PSL3Four.RootNormalizerModel
