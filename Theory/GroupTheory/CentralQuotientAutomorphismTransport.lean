module
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
/-!
# Faithful central quotient actions under group isomorphisms

An isomorphism carries the center onto the center and conjugates the induced
automorphism actions on the corresponding quotients. Faithfulness of an action
on the central quotient therefore survives transport to a concrete group model.
This preserves the literal source actor while using a Sylow model for its target.
-/

public section
open Subgroup
namespace MulEquiv
variable {G H A : Type*} [Group G] [Group H] [Group A]
private theorem map_center_for_quotient (e : G≃*H) : (center G).map e.toMonoidHom=center H := by
  ext h
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact (centerCongr e ⟨g,hg⟩).property
  · intro hh
    exact ⟨e.symm h,(centerCongr e.symm ⟨h,hh⟩).property,e.apply_symm_apply h⟩

theorem injective_centerQuotientAction_congr (e : G≃*H)
    (α : A→*MulAut G)
    (hfaithful : Function.Injective ((quotientAut (center G)).comp α)) :
    Function.Injective ((quotientAut (center H)).comp
      ((MulAut.congr e).toMonoidHom.comp α)) := by
  let q : (G⧸center G)≃*(H⧸center H) :=
    QuotientGroup.congr _ _ e (map_center_for_quotient e)
  have heq : (quotientAut (center H)).comp ((MulAut.congr e).toMonoidHom.comp α) =
      (MulAut.congr q).toMonoidHom.comp ((quotientAut (center G)).comp α) := by
    ext a x
    obtain ⟨x,rfl⟩ := q.surjective x
    induction x using Quotient.inductionOn with
    | h x =>
      change quotientAut (center H) (MulAut.congr e (α a))
          (q (QuotientGroup.mk' (center G) x)) =
        q ((quotientAut (center G) (α a)) (q.symm (q (QuotientGroup.mk' (center G) x))))
      rw [q.symm_apply_apply,quotientAut_apply_mk]
      have hq (y:G) : q (QuotientGroup.mk' (center G) y) =
          QuotientGroup.mk' (center H) (e y) := QuotientGroup.congr_mk' _ _ _ _ y
      rw [hq,quotientAut_apply_mk,hq]
      change QuotientGroup.mk' (center H) (e (α a (e.symm (e x)))) = _
      rw [e.symm_apply_apply]
  rw [heq]
  exact (MulAut.congr q).injective.comp hfaithful
end MulEquiv
