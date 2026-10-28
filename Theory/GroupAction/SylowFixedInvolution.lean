module

public import Theory.GroupAction.PerfectCentralQuotient
public import Mathlib.GroupTheory.Sylow

/-!
# Faithful actions with a Sylow-fixing involution

The acting group contains every inner automorphism of the group being acted
on. Its specified subgroup has order two and fixes a Sylow two-subgroup
pointwise. These are action hypotheses only; no centralizer conclusion is
part of the structure.

Isomorphisms and the central quotient of a perfect group preserve all four
conditions. For the quotient, faithfulness uses perfectness and the Sylow
subgroup is the image under the actual quotient map. The acting group and
its order-two subgroup are unchanged, so their centralizer is unchanged.

This is the elementary transport used in Aschbacher–Smith, combined
manuscript (1 March 2004), E.6.19, printed p.252 (PDF p.263).
-/

public section

open Subgroup
namespace Theory.GroupAction
variable {X Y H : Type*} [Group X] [Group Y] [Group H]

/-- A faithful action containing the inner group, with an order-two subgroup
fixing an actual Sylow subgroup pointwise. -/
structure SylowFixedInvolution (φ : H →* MulAut X) (E : Subgroup H) : Prop where
  faithful : Function.Injective φ
  inner : (MulAut.conj : X →* MulAut X).range ≤ φ.range
  card : Nat.card E = 2
  fixes : ∃ S : Sylow 2 X, ∀ a ∈ E, ∀ x ∈ (S : Subgroup X), φ a x = x

/-- Transport an action along a group isomorphism, keeping the actors fixed. -/
theorem SylowFixedInvolution.equiv [Finite X] {φ : H →* MulAut X} {E : Subgroup H}
    (d : SylowFixedInvolution φ E) (e : X ≃* Y) :
    SylowFixedInvolution ((MulAut.congr e).toMonoidHom.comp φ) E := by
  refine ⟨(MulAut.congr e).injective.comp d.faithful, ?_, d.card, ?_⟩
  · rintro _ ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := d.inner ⟨e.symm y, rfl⟩
    refine ⟨a, ?_⟩
    change MulAut.congr e (φ a) = MulAut.conj y
    rw [ha]
    ext z
    simp [MulAut.congr_apply, MulAut.conj_apply]
  · obtain ⟨S, hS⟩ := d.fixes
    refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
    intro a ha y hy
    obtain ⟨x, hx, rfl⟩ := hy
    change e (φ a (e.symm (e x))) = e x
    rw [e.symm_apply_apply, hS a ha x hx]

/-- Pass to a specified perfect central quotient without changing the actors. -/
theorem SylowFixedInvolution.centralQuotient [Finite X] [Group.IsPerfect X]
    {φ : H →* MulAut X} {E : Subgroup H} (d : SylowFixedInvolution φ E)
    (e : X ⧸ center X ≃* Y) :
    SylowFixedInvolution ((MulAut.centralQuotientAction e).comp φ) E := by
  refine ⟨(MulAut.centralQuotientAction_injective e).comp d.faithful, ?_, d.card, ?_⟩
  · rintro _ ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center X) z
    obtain ⟨a, ha⟩ := d.inner ⟨x, rfl⟩
    refine ⟨a, ?_⟩
    change MulAut.centralQuotientAction e (φ a) = _
    rw [ha, MulAut.centralQuotientAction_conj]
  · obtain ⟨S, hS⟩ := d.fixes
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center X))
    refine ⟨S.mapSurjective (f := q) (e.surjective.comp
      (QuotientGroup.mk'_surjective (center X))), ?_⟩
    intro a ha y hy
    obtain ⟨x, hx, rfl⟩ := hy
    change MulAut.centralQuotientAction e (φ a)
      (e (QuotientGroup.mk' (center X) x)) = e (QuotientGroup.mk' (center X) x)
    rw [MulAut.centralQuotientAction_apply, hS a ha x hx]

end Theory.GroupAction
