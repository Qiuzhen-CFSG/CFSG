module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Data.Set.Card

/-!
# A fixed point complementary to an orbit of length three

In an invariant four-element set, the complement of a three-element orbit
is a singleton and hence fixed. If a subgroup has at most two fixed points
in that set, one of which lies in the orbit, the other is fixed by the whole
group. This is the permutation argument used on the four cubic residuals
in Aschbacher–Smith 12.4.6, printed p.814.
-/

public section
namespace MulAction
variable {H α : Type*} [Group H] [MulAction H α]

/-- The second possible subgroup-fixed point is fixed by the whole group. -/
theorem fixed_of_four_point_orbit (S : Subgroup H) (Y : Set α)
    (hY : Y.ncard = 4) (hinv : ∀ g : H, ∀ x ∈ Y, g • x ∈ Y)
    (a b : α) (ha : a ∈ Y) (horbit : (orbit H a).ncard = 3)
    (hfixed : ∀ x ∈ Y, (∀ s : S, (s : H) • x = x) → x = a ∨ x = b) :
    ∀ g : H, g • b = b := by
  have hfin : Y.Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hsub : orbit H a ⊆ Y := by
    rintro x ⟨g, rfl⟩
    exact hinv g a ha
  have hdiff : (Y \ orbit H a).ncard = 1 := by
    rw [Set.ncard_sdiff' hsub hfin, hY, horbit]
  obtain ⟨c, hc⟩ := Set.ncard_eq_one.mp hdiff
  have hcmem : c ∈ Y \ orbit H a := hc.symm ▸ Set.mem_singleton c
  have hfix : ∀ g : H, g • c = c := by
    intro g
    have hgc : g • c ∈ Y \ orbit H a := by
      refine ⟨hinv g c hcmem.1, ?_⟩
      rintro ⟨k, hk⟩
      apply hcmem.2
      refine ⟨g⁻¹ * k, ?_⟩
      change k • a = g • c at hk
      change (g⁻¹ * k) • a = c
      rw [mul_smul, hk, inv_smul_smul]
    simpa only [hc, Set.mem_singleton_iff] using hgc
  have hcb : c = b := (hfixed c hcmem.1 (fun s => hfix s)).resolve_left (by
    intro he
    subst c
    exact hcmem.2 (mem_orbit_self a))
  simpa only [← hcb] using hfix

end MulAction
