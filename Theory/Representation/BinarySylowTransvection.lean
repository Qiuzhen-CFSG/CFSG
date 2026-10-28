module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Transvections

/-!
# Displacement of Sylow-central elements in binary natural modules

Every nonidentity element centralizing a binary linear Sylow two-subgroup
is a transvection. Its displacement image is exactly its axis, so has
dimension one. The special linear version uses the actual matrix action
equivalence and transports the given Sylow subgroup.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.21, printed p.924, eliminating the natural SL₄(2) and SL₅(2) rows.
-/

@[expose] public section
open Subgroup BinaryLinear
namespace BinaryLinear.OuterCyclic

theorem IsTransvection.displacement_rank
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {t : BinaryLinear.GL V} (ht : IsTransvection t) :
    Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 1 := by
  obtain ⟨w, f, hw, hf, hfw, rfl⟩ := ht
  have hr : LinearMap.range ((transvection w f hfw).toLinearMap - LinearMap.id) =
      Submodule.span (ZMod 2) {w} := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      change x + f x • w - x ∈ _
      rw [add_sub_cancel_left]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
    · apply Submodule.span_le.mpr
      intro y hy
      have hyw : y = w := Set.mem_singleton_iff.mp hy
      subst y
      have hex : ∃ x, f x ≠ 0 := by
        by_contra! hz
        exact hf (LinearMap.ext hz)
      obtain ⟨x, hx⟩ := hex
      have hx1 : f x = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hx
      refine ⟨x, ?_⟩
      change x + f x • w - x = w
      rw [hx1, one_smul, add_sub_cancel_left]
  rw [hr, finrank_span_singleton hw]

/-- The actual natural action, with the original Sylow transported through
SLₙ(2) ≃ GL(F₂ⁿ). Membership of the element in the Sylow is unnecessary. -/
theorem specialLinear_isTransvection_of_central_sylow {n : ℕ} (hn : 1 < n)
    (T : Sylow 2 (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)))
    (v : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) (hv : v ≠ 1)
    (hc : ∀ x, x ∈ T → x * v = v * x) :
    IsTransvection (slEquivLinear n v) := by
  let e := slEquivLinear n
  let P := T.mapSurjective (f := e.toMonoidHom) e.surjective
  refine isTransvection_of_central_sylow ?_ ?_ P ?_ ?_
  · change 2 ∣ Nat.card (Fin n → ZMod 2)
    simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    exact dvd_pow_self 2 (by omega : n ≠ 0)
  · simpa only [Space, Module.finrank_fin_fun] using hn
  · exact fun h => hv (e.injective (h.trans e.map_one.symm))
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    change e y * e v = e v * e y
    simpa only [map_mul] using congrArg e (hc y hy)

end BinaryLinear.OuterCyclic
