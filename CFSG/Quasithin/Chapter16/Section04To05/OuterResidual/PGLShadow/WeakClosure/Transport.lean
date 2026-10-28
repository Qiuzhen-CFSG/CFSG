module
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.WeakClosure.Configuration

/-!
# Transporting weak closure with the marked involution

Conjugation maps the actual embedded center onto the center of the
conjugate subgroup. Applying the inverse conjugation to a purported
fusion transfers elementwise weak closure. The premise remains explicit;
the failure-of-closure argument must establish it before this lemma can
be used in the symmetric configuration.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 16.4.6, printed p.1185, weak closure in Z(T^g).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.WeakClosure
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]

theorem embeddedCenter_conjBy (T : Subgroup G) (g : G) :
    (embeddedCenter T).conjBy g = embeddedCenter (T.conjBy g) := by
  change (T ⊓ centralizer (T : Set G)).map (MulAut.conj g).toMonoidHom = _
  rw [map_inf _ _ _ (MulAut.conj g).injective, map_centralizer_equiv]
  rfl

/-- Weak closure transports with its actual marked element and subgroup. -/
theorem WeaklyClosedInCenter.conjBy {T : Subgroup G} {z : G}
    (h : WeaklyClosedInCenter T z) (g : G) :
    WeaklyClosedInCenter (T.conjBy g) (MulAut.conj g z) := by
  constructor
  · rw [← embeddedCenter_conjBy]
    exact ⟨z, h.1, rfl⟩
  · intro x hx hc
    rw [← embeddedCenter_conjBy] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hzy : IsConj z y := by
      have hh := (MulAut.conj g).symm.toMonoidHom.map_isConj hc
      change IsConj ((MulAut.conj g).symm (MulAut.conj g z))
        ((MulAut.conj g).symm (MulAut.conj g y)) at hh
      simpa only [MulEquiv.symm_apply_apply] using hh
    exact congrArg (MulAut.conj g) (h.2 y hy hzy)

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.WeakClosure
