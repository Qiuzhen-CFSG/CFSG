module

public import Theory.GroupTheory.CoprimeComplementLift

/-!
# Lifting a subgroup through a coprime kernel

A subgroup of order coprime to a surjection's kernel has a section over its
original subtype map. Apply Schur–Zassenhaus inside its inverse image and
invert the resulting isomorphism. The pointwise projection identity lets a
marked linear action lift without changing that action.

The source torus in Aschbacher–Smith, original 4.3.10–11, printed p.617,
uses this to lift the scalar torus through the original two-core.
-/

open Subgroup
namespace MonoidHom
variable {A B : Type*} [Group A] [Group B]

/-- A subgroup of order coprime to a surjection's kernel admits a lift whose
composition with the original surjection is exactly its subtype map. -/
public theorem exists_subgroup_section_of_coprime_kernel
    (f : A →* B) (hf : Function.Surjective f) (T : Subgroup B)
    (hcop : Nat.Coprime (Nat.card f.ker) (Nat.card T)) :
    ∃ s : T →* A, f.comp s = T.subtype := by
  let V := T.comap f
  let r : V →* T := (f.comp V.subtype).codRestrict T (fun x => x.property)
  have hr : Function.Surjective r := by
    intro t
    obtain ⟨a,ha⟩ := hf t
    exact ⟨⟨a,show f a ∈ T from ha.symm ▸ t.property⟩,Subtype.ext ha⟩
  let k : r.ker ≃* f.ker := {
    toFun := fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
    invFun := fun x => ⟨⟨x,by change f x ∈ T; rw [x.property]; exact T.one_mem⟩,
      Subtype.ext x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  obtain ⟨E,_,e,he⟩ := r.exists_complement_lift_of_coprime_kernel hr ⊥ ⊤
    isComplement'_bot_top (by simpa only [Nat.card_congr k.toEquiv, card_top] using hcop)
  let t : T →* (⊤ : Subgroup T) := (topEquiv : (⊤ : Subgroup T) ≃* T).symm.toMonoidHom
  let s : T →* A := V.subtype.comp (E.subtype.comp (e.symm.toMonoidHom.comp t))
  refine ⟨s,?_⟩
  ext x
  have hx := he (e.symm (t x))
  have hx' : r (e.symm (t x)) = x := by
    calc r (e.symm (t x)) = (t x : T) := by
           simpa only [e.apply_symm_apply] using hx.symm
         _ = x := rfl
  exact congrArg Subtype.val hx'
end MonoidHom

