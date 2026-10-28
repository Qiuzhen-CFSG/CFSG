module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic
public import Theory.SpecificGroups.AlternatingFiveCore
public import Theory.GroupTheory.PCoreSurjective

/-!
# Recognizing the first intrinsic cores from the concrete five-point actions

A surjection onto A₅ or S₅ with a two-group kernel identifies that kernel
with the two-core. A₅ has trivial two-core by simplicity. For S₅, a normal
two-subgroup has a fixed point on the five letters; conjugation transports
that fixed point to every letter, so the subgroup is trivial.

The fixed radical's order 32 and the two explicit action maps therefore
suffice for both core identifications and quotient equivalences. These are
conditional reductions: the radical order and action maps remain inputs.
Source: the local quotients of Aschbacher--Smith F.1.12(I)(10)--(11), p.263.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
open Theory.GroupTheory Seed

private theorem perm_five_twoCore_eq_bot : pCore 2 (Equiv.Perm (Fin 5)) = ⊥ := by
  let P := pCore 2 (Equiv.Perm (Fin 5))
  have hp : IsPGroup 2 P := pCore_isPGroup
  obtain ⟨x, hx⟩ := hp.nonempty_fixed_point_of_prime_not_dvd_card (Fin 5) (by simp)
  apply (pCore 2 (Equiv.Perm (Fin 5))).eq_bot_iff_forall.mpr
  intro g hg
  apply Equiv.ext
  intro y
  let t : Equiv.Perm (Fin 5) := Equiv.swap x y
  have hm := (inferInstance : P.Normal).conj_mem g hg t⁻¹
  have hf := hx ⟨_, hm⟩
  change (t⁻¹ * g * (t⁻¹)⁻¹) x = x at hf
  have he := congrArg t hf
  simpa [Equiv.Perm.mul_apply, t] using he

theorem l₁_core_eq_of_radical_action
    (hcard : Nat.card radical = 32)
    (f : l₁ →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (hk : f.ker = radical.subgroupOf l₁) :
    pCore 2 l₁ = radical.subgroupOf l₁ := by
  have hp : IsPGroup 2 f.ker := by
    rw [hk]
    exact (IsPGroup.of_card (p := 2) (n := 5) hcard).of_equiv
      (Subgroup.subgroupOfEquivOfLe radical_le_l₁).symm
  have h := f.comap_pCore_of_ker_isPGroup hf hp
  rw [alternatingGroup.five_twoCore_eq_bot] at h
  change f.ker = pCore 2 l₁ at h
  exact h.symm.trans hk

theorem l₁_quotient_of_radical_action
    (hcard : Nat.card radical = 32)
    (f : l₁ →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (hk : f.ker = radical.subgroupOf l₁) :
    Nonempty ((l₁ ⧸ pCore 2 l₁) ≃* alternatingGroup (Fin 5)) := by
  have heq : pCore 2 l₁ = f.ker := (l₁_core_eq_of_radical_action hcard f hf hk).trans hk.symm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq heq).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

theorem l₁s_core_eq_of_radical_action
    (hcard : Nat.card radical = 32)
    (f : l₁s →* Equiv.Perm (Fin 5)) (hf : Function.Surjective f)
    (hk : f.ker = outerRadical.subgroupOf l₁s) :
    pCore 2 l₁s = outerRadical.subgroupOf l₁s := by
  have hc : Nat.card outerRadical = 32 := by
    rw [outerRadical, Subgroup.card_map_of_injective SecondParabolic.intoExtension_injective, hcard]
  have hp : IsPGroup 2 f.ker := by
    rw [hk]
    exact (IsPGroup.of_card (p := 2) (n := 5) hc).of_equiv
      (Subgroup.subgroupOfEquivOfLe outerRadical_le_l₁s).symm
  have h := f.comap_pCore_of_ker_isPGroup hf hp
  rw [perm_five_twoCore_eq_bot] at h
  change f.ker = pCore 2 l₁s at h
  exact h.symm.trans hk

theorem l₁s_quotient_of_radical_action
    (hcard : Nat.card radical = 32)
    (f : l₁s →* Equiv.Perm (Fin 5)) (hf : Function.Surjective f)
    (hk : f.ker = outerRadical.subgroupOf l₁s) :
    Nonempty ((l₁s ⧸ pCore 2 l₁s) ≃* Equiv.Perm (Fin 5)) := by
  have heq : pCore 2 l₁s = f.ker := (l₁s_core_eq_of_radical_action hcard f hf hk).trans hk.symm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq heq).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

/-- The raw candidate becomes the intrinsic core after the action calculation. -/
noncomputable def radicalCoreEquiv_of_action
    (hcard : Nat.card radical = 32)
    (f : l₁ →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (hk : f.ker = radical.subgroupOf l₁) : radical ≃* pCore 2 l₁ :=
  (Subgroup.subgroupOfEquivOfLe radical_le_l₁).symm.trans
    (MulEquiv.subgroupCongr (l₁_core_eq_of_radical_action hcard f hf hk).symm)

end Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
