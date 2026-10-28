module
public import Theory.Representation.BinarySingerNormalizer
public import Theory.ElementaryAbelian.VectorSpace

/-!
# Cyclic 2-subgroups of a regular cyclic automorphism normalizer

A cyclic group acting regularly on the nonidentity elements of an elementary
abelian 2-group is a binary Singer group. Its normalizing 2-subgroups are cyclic,
by the linear Singer-normalizer theorem. This supplies the action argument in
Aschbacher–Smith, Volume I, 2.4.17(2).
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]

private def elementaryAutLinear : MulAut E ≃* LinearMap.GeneralLinearGroup (ZMod 2) (Additive E) :=
  (show MulAut E ≃* (Additive E ≃ₗ[ZMod 2] Additive E) from
    { toFun := fun a => { a.toAdditive with map_smul' := ZMod.map_smul a.toAdditive }
      invFun := fun a => a.toAddEquiv.toMultiplicative
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive E)).symm

theorem regular_cyclic_automorphism_normalizer_two_subgroup
    (C P : Subgroup (MulAut E)) [IsCyclic C]
    (hreg : ∀ v w : E, v ≠ 1 → w ≠ 1 → ∃! c : C, c.val v = w)
    (hp : IsPGroup 2 P) (hn : P ≤ normalizer (C : Set (MulAut E))) : IsCyclic P := by
  let e := elementaryAutLinear (E := E)
  let D := C.map e.toMonoidHom
  let Q := P.map e.toMonoidHom
  let : IsCyclic D := isCyclic_of_surjective (e.toMonoidHom.subgroupMap C)
    (e.toMonoidHom.subgroupMap_surjective C)
  have hreg' : ∀ v w : Additive E, v ≠ 0 → w ≠ 0 →
      ∃! c : D, (c.val : Module.End (ZMod 2) (Additive E)) v = w := by
    intro v w hv hw
    obtain ⟨c,hc,hu⟩ := hreg v.toMul w.toMul hv hw
    refine ⟨⟨e c, mem_map_of_mem _ c.property⟩,hc,?_⟩
    intro a ha
    obtain ⟨b,hb,he⟩ := a.property
    have hb' : (⟨b,hb⟩ : C) = c := hu ⟨b,hb⟩ (by
      have hh := ha
      change (a.val : Module.End (ZMod 2) (Additive E)) v = w at hh
      rw [←he] at hh
      exact hh)
    apply Subtype.ext
    exact he.symm.trans (congrArg e (congrArg Subtype.val hb'))
  have hn' : Q ≤ normalizer (D : Set _) :=
    (map_mono hn).trans (C.le_normalizer_map e.toMonoidHom)
  let : IsCyclic Q := Representation.BinarySingerNormalizer.isCyclic_of_isPGroup_le_normalizer
    D hreg' Q (hp.map e.toMonoidHom) hn'
  exact (P.equivMapOfInjective e.toMonoidHom e.injective).isCyclic.mpr
    (show IsCyclic Q from inferInstance)



private theorem elementary_involution_fixed_lower
    (t : MulAut E) (ht2 : t ^ 2 = 1) :
    Nat.card E ≤ Nat.card (t.toMonoidHom.eqLocus (MonoidHom.id E)) ^ 2 := by
  let δ : E →* E := t.toMonoidHom / MonoidHom.id E
  have ht (x : E) : t (t x) = x := by
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using
      congrArg (fun a : MulAut E => a x) ht2
  have hi (x : E) : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) x
  have hk : δ.ker = t.toMonoidHom.eqLocus (MonoidHom.id E) := by
    ext x
    change t x / x = 1 ↔ t x = x
    exact div_eq_one
  have hr : δ.range ≤ δ.ker := by
    rintro x ⟨y,rfl⟩
    change t (t y / y) / (t y / y) = 1
    rw [div_eq_one,map_div,ht]
    simp only [div_eq_mul_inv,hi,mul_comm]
  have hc := δ.ker.card_mul_index
  rw [index_ker] at hc
  rw [←hk,←hc,pow_two]
  exact Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective (inclusion hr) (inclusion_injective hr))

theorem regular_cyclic_automorphism_normalizer_involution_fixed_card
    (C : Subgroup (MulAut E)) [IsCyclic C]
    (hreg : ∀ v w : E, v ≠ 1 → w ≠ 1 → ∃! c : C, c.val v = w)
    (t : MulAut E) (ht : t ≠ 1) (ht2 : t ^ 2 = 1)
    (hn : t ∈ normalizer (C : Set (MulAut E))) :
    Nat.card (t.toMonoidHom.eqLocus (MonoidHom.id E)) ^ 2 = Nat.card E := by
  let e := elementaryAutLinear (E := E)
  let D := C.map e.toMonoidHom
  let : IsCyclic D := isCyclic_of_surjective (e.toMonoidHom.subgroupMap C)
    (e.toMonoidHom.subgroupMap_surjective C)
  have hreg' : ∀ v w : Additive E, v ≠ 0 → w ≠ 0 →
      ∃! c : D, (c.val : Module.End (ZMod 2) (Additive E)) v = w := by
    intro v w hv hw
    obtain ⟨c,hc,hu⟩ := hreg v.toMul w.toMul hv hw
    refine ⟨⟨e c, mem_map_of_mem _ c.property⟩,hc,?_⟩
    intro a ha
    obtain ⟨b,hb,he⟩ := a.property
    have hb' : (⟨b,hb⟩ : C) = c := hu ⟨b,hb⟩ (by
      have hh := ha
      change (a.val : Module.End (ZMod 2) (Additive E)) v = w at hh
      rw [←he] at hh
      exact hh)
    apply Subtype.ext
    exact he.symm.trans (congrArg e (congrArg Subtype.val hb'))
  have hn' : e t ∈ normalizer (D : Set _) :=
    C.le_normalizer_map e.toMonoidHom (mem_map_of_mem _ hn)
  have ht' : e t ≠ 1 := by
    intro he
    apply ht
    exact e.injective (he.trans (map_one e).symm)
  have ht2' : (e t)^2 = 1 := by rw [←map_pow,ht2,map_one]
  have hb := Representation.BinarySingerNormalizer.fixedSpace_card_sq_le D hreg'
    (e t) ht' ht2' hn'
  let F := Representation.BinaryOffender.fixedSpace
    (Units.coeHom (Module.End (ZMod 2) (Additive E))) (zpowers (e t))
  have hm (v : E) : Additive.ofMul v ∈ F ↔ t v = v := by
    constructor
    · intro h
      exact h ⟨e t,mem_zpowers (e t)⟩
    · intro h a
      exact smul_eq_self_of_mem_zpowers a.property h
  have hc : Nat.card F = Nat.card (t.toMonoidHom.eqLocus (MonoidHom.id E)) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (show Additive E ≃ E from Equiv.refl _) (fun v => hm v.toMul)
  rw [hc] at hb
  exact le_antisymm hb (elementary_involution_fixed_lower t ht2)
end Theory.GroupTheory
