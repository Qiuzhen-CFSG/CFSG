module

public import Theory.GroupTheory.NormalSupplementGluing
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Transport and normal-supplement consequences of A₅ subgroup rigidity

The two explicit model obligations say that an embedding of an order-twelve
subgroup of A₅ extends to an automorphism, and that restriction to such a
subgroup is faithful. Transport carries these assertions to genuine A₅
models. For two normal A₅ subgroups, uniqueness on the common local
subgroup forces conjugation compatibility, so normal-supplement gluing
constructs the extension and retains the entire prescribed local map.

This module does not assert the two model obligations. Their producer is
separate. Source application: Aschbacher, “A 2-local characterization of
M12”, Proposition 3.3, printed p.38.
-/

@[expose] public section
open Subgroup
namespace AlternatingFiveSubgroupExtension
abbrev A5 := alternatingGroup (Fin 5)
/-- Every marking of an order-twelve subgroup extends to A₅. -/
def MarkingExtension : Prop := ∀ (S : Subgroup A5), Nat.card S = 12 →
  ∀ (f : S →* A5), Function.Injective f → ∃ e : MulAut A5, ∀ s : S, e s = f s

/-- An automorphism of A₅ is determined on an order-twelve subgroup. -/
def RestrictionFaithful : Prop := ∀ (S : Subgroup A5), Nat.card S = 12 →
  ∀ α β : MulAut A5, (∀ s : S, α s = β s) → α = β

variable {A B : Type*} [Group A] [Group B]

/-- Transport marking extension along actual A₅ equivalences. -/
theorem exists_equiv_extending (h : MarkingExtension)
    (eA : A ≃* A5) (eB : B ≃* A5) (S : Subgroup A) (hcard : Nat.card S = 12)
    (f : S →* B) (hf : Function.Injective f) :
    ∃ e : A ≃* B, ∀ s : S, e s = f s := by
  let T := S.map eA.toMonoidHom
  let eS : S ≃* T := S.equivMapOfInjective eA.toMonoidHom eA.injective
  let g : T →* A5 := eB.toMonoidHom.comp (f.comp eS.symm.toMonoidHom)
  have hT : Nat.card T = 12 := (Nat.card_congr eS.toEquiv).symm.trans hcard
  obtain ⟨α, hα⟩ := h T hT g (eB.injective.comp (hf.comp eS.symm.injective))
  refine ⟨eA.trans (α.trans eB.symm), ?_⟩
  intro s
  apply eB.injective
  change eB (eB.symm (α (eA s))) = eB (f s)
  rw [eB.apply_symm_apply]
  have hs := hα (eS s)
  have heS : (eS s : A5) = eA s := rfl
  rw [heS] at hs
  simpa only [g, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, eS.symm_apply_apply] using hs

/-- Transport faithfulness of restriction along an actual A₅ equivalence. -/
theorem aut_eq_of_agree (h : RestrictionFaithful) (eA : A ≃* A5)
    (S : Subgroup A) (hcard : Nat.card S = 12) (α β : MulAut A)
    (hagree : ∀ s : S, α s = β s) : α = β := by
  let T := S.map eA.toMonoidHom
  let eS : S ≃* T := S.equivMapOfInjective eA.toMonoidHom eA.injective
  have hT : Nat.card T = 12 := (Nat.card_congr eS.toEquiv).symm.trans hcard
  apply (MulAut.congr eA).injective
  apply h T hT
  intro t
  obtain ⟨s, rfl⟩ := eS.surjective t
  change eA (α (eA.symm (eA s))) = eA (β (eA.symm (eA s)))
  rw [eA.symm_apply_apply, hagree s]
/-- Local marking and rigidity determine the whole normal-supplement extension. -/
theorem exists_equiv_normal_supplement (hm : MarkingExtension) (hr : RestrictionFaithful)
    (N M : Subgroup A) [N.Normal] (R : Subgroup B) [R.Normal]
    (eN : N ≃* A5) (eR : R ≃* A5) (v : M →* B) (hv : Function.Injective v)
    (hgen : N ⊔ M = ⊤) (hgen' : R ⊔ v.range = ⊤)
    (hinter : ∀ m : M, v m ∈ R ↔ (m : A) ∈ N)
    (hcard : Nat.card (M.subgroupOf N) = 12) :
    ∃ E : A ≃* B, ∀ m : M, E m = v m := by
  let S := M.subgroupOf N
  let f : S →* R :=
    { toFun := fun s => ⟨v ⟨s.val.val, s.property⟩,
        (hinter ⟨s.val.val, s.property⟩).mpr s.val.property⟩
      map_one' := Subtype.ext (map_one v)
      map_mul' := by
        intro s t
        apply Subtype.ext
        change v ((⟨s.val.val, s.property⟩ : M) * ⟨t.val.val, t.property⟩) = _
        rw [map_mul]
        rfl }
  have hf : Function.Injective f := by
    intro s t h
    have he := hv (congrArg Subtype.val h)
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : M => (x : A)) he
  obtain ⟨e, he⟩ := exists_equiv_extending hm eN eR S hcard f hf
  have hagree (m : M) (hn : (m : A) ∈ N) : (e ⟨m, hn⟩ : B) = v m := by
    exact congrArg Subtype.val (he ⟨⟨m, hn⟩, m.property⟩)
  have hconj (m : M) (n : N) :
      (e (MulAut.conjNormal (m : A) n) : B) = v m * e n * (v m)⁻¹ := by
    let α : MulAut N := MulAut.conjNormal (m : A)
    let β : MulAut N := (MulAut.congr e).symm (MulAut.conjNormal (v m))
    have hαβ : α = β := aut_eq_of_agree hr eN S hcard α β (by
      intro s
      apply e.injective
      apply Subtype.ext
      have hsM : (m : A) * s.val.val * (m : A)⁻¹ ∈ M :=
        M.mul_mem (M.mul_mem m.property s.property) (M.inv_mem m.property)
      have hc := hagree ⟨(m : A) * s.val.val * (m : A)⁻¹, hsM⟩
        ((inferInstance : N.Normal).conj_mem _ s.val.property m)
      have hs := hagree ⟨s.val.val, s.property⟩ s.val.property
      change (e (α s) : B) = (e (e.symm (MulAut.conjNormal (v m) (e s))) : B)
      rw [e.apply_symm_apply]
      change (e (α s) : B) = v m * (e s : B) * (v m)⁻¹
      rw [hs]
      refine hc.trans ?_
      change v (m * (⟨s.val.val, s.property⟩ : M) * m⁻¹) = _
      rw [map_mul, map_mul, map_inv])
    have heq := congrArg (fun a : MulAut N => e (a n)) hαβ
    change e (MulAut.conjNormal (m : A) n) =
      e (e.symm (MulAut.conjNormal (v m) (e n))) at heq
    rw [e.apply_symm_apply] at heq
    exact congrArg Subtype.val heq
  obtain ⟨E, _, hE⟩ := NormalSupplementGluing.exists_equiv N M R e v hgen hgen'
    hinter hagree hconj
  exact ⟨E, hE⟩
end AlternatingFiveSubgroupExtension
end
