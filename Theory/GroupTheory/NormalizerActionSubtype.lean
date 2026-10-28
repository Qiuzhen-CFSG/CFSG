module
public import Mathlib.GroupTheory.Subgroup.Centralizer
/-!
A subgroup inclusion transports a surjective normalizer action to the literal ambient normalizer action.
Source application: Aschbacher--Smith 2.5.15, printed pp.558--559.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

theorem normalizer_action_map_subtype_surjective
    (K : Subgroup G) (C R : Subgroup K)
    (hCN : C ≤ normalizer (R : Set K))
    (hMC : C.map K.subtype ≤ normalizer (R.map K.subtype : Set G))
    (hsurj : Function.Surjective (R.normalizerMonoidHom.comp (inclusion hCN))) :
    Function.Surjective ((R.map K.subtype).normalizerMonoidHom.comp (inclusion hMC)) := by
  let eR := R.equivMapOfInjective K.subtype K.subtype_injective
  let eC := C.equivMapOfInjective K.subtype K.subtype_injective
  intro a
  obtain ⟨c,hc⟩ := hsurj (MulAut.congr eR.symm a)
  refine ⟨eC c,?_⟩
  apply MulEquiv.ext
  intro r
  obtain ⟨s,rfl⟩ := eR.surjective r
  have hh := congrArg (fun b : MulAut R => eR (b s)) hc
  have hs : eR ((R.normalizerMonoidHom (inclusion hCN c)) s) = a (eR s) := by
    simpa only [MonoidHom.comp_apply,MulAut.congr_apply,MulEquiv.trans_apply,
      MulEquiv.symm_symm,eR.apply_symm_apply] using hh
  apply Subtype.ext
  exact congrArg Subtype.val hs
end Subgroup
