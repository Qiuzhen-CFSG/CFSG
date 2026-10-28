module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Transport of central derived subgroups through embeddings

An injective homomorphism identifies a subgroup with its image. Under that
identification both its derived subgroup and its center are preserved, so the
ambient image of their intersection is preserved as well. This records the
actual subgroup equality needed when a centralizer inside a Sylow subgroup is
viewed in the full group.
-/

namespace Subgroup

/-- The central derived subgroup of an embedded subgroup is the image of its
intrinsic central derived subgroup. -/
public theorem map_derived_inf_center_of_injective
    {T G : Type*} [Group T] [Group G]
    (C : Subgroup T) (f : T →* G) (hf : Function.Injective f) :
    let Q := C.map f
    (_root_.commutator Q ⊓ center Q).map Q.subtype =
      ((_root_.commutator C ⊓ center C).map C.subtype).map f := by
  let Q := C.map f
  let e : C ≃* Q := C.equivMapOfInjective f hf
  have hcenter : (center C).map e.toMonoidHom = center Q := by
    ext q
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact (centerCongr e ⟨c, hc⟩).property
    · intro hq
      exact ⟨e.symm q, (centerCongr e.symm ⟨q, hq⟩).property, e.apply_symm_apply q⟩
  have hderived : (_root_.commutator C).map e.toMonoidHom = _root_.commutator Q := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  have hboth : (_root_.commutator C ⊓ center C).map e.toMonoidHom =
      _root_.commutator Q ⊓ center Q := by
    rw [map_inf _ _ _ e.injective, hderived, hcenter]
  change (_root_.commutator Q ⊓ center Q).map Q.subtype = _
  rw [← hboth, map_map, map_map]
  rfl

/-- A characteristic derived-center line retains its named generator under
an injective embedding. -/
public theorem derived_center_line_map_of_injective
    {T G : Type*} [Group T] [Group G]
    (C : Subgroup T) (f : T →* G) (hf : Function.Injective f) (z : T)
    (hline : (_root_.commutator C ⊓ center C).map C.subtype = zpowers z) :
    let Q := C.map f
    (_root_.commutator Q ⊓ center Q).map Q.subtype = zpowers (f z) := by
  dsimp only
  rw [map_derived_inf_center_of_injective C f hf, hline, MonoidHom.map_zpowers]

end Subgroup
