module
public import Theory.Representation.FullLinearOuterAction
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic

/-!
# No outer degree-four automorphism fixes a full center

The transvections with a fixed nonzero center form a point radical. An
automorphism fixing them preserves that point radical, hence all point
radicals by conjugacy. The proved point-rigidity theorem makes it inner.
Coordinates transport this argument to the original binary four-space.
This supplies the representation obstruction in the degree-four repair of
Aschbacher--Smith G.10.15(3), printed p.363.
-/

public noncomputable section
open Subgroup Module
namespace Representation.BinaryOffender
open BinaryLinear BinaryLinear.OuterCyclic

private theorem inner_of_fixed_full_center
    (a : MulAut (LinearGroup 4)) (i : Space 4) (hi : i ≠ 0)
    (hfull : ∀ (f : Module.Dual (ZMod 2) (Space 4)) (hf : f i = 0),
      a (transvection i f hf) = transvection i f hf) :
    a ∈ MulAut.innerSubgroup (LinearGroup 4) := by
  have hfix (t : LinearGroup 4) (ht : t ∈ pointRadical 4 i) : a t = t := by
    let d : Space 4 →ₗ[ZMod 2] Space 4 := t.toLinearMap - LinearMap.id
    let c := d.codRestrict (Submodule.span (ZMod 2) {i}) ht.2
    let f := (LinearEquiv.coord (ZMod 2) (Space 4) i hi).toLinearMap.comp c
    have hfd (u : Space 4) : f u • i = t u - u :=
      LinearEquiv.coord_apply_smul (ZMod 2) (Space 4) i hi (c u)
    have hfi : f i = 0 := by
      have hh := hfd i
      rw [ht.1 i (Submodule.mem_span_singleton_self i),sub_self] at hh
      exact (smul_eq_zero.mp hh).resolve_right hi
    have he : t = transvection i f hfi := by
      apply LinearEquiv.ext
      intro u
      change t u = u + f u • i
      rw [hfd]
      abel
    rw [he]
    exact hfull f hfi
  have hmap : (pointRadical 4 i).map a.toMonoidHom = pointRadical 4 i := by
    apply le_antisymm
    · rintro _ ⟨t,ht,rfl⟩
      change a t ∈ pointRadical 4 i
      rw [hfix t ht]
      exact ht
    · intro t ht
      exact ⟨t,ht,hfix t ht⟩
  obtain ⟨b,hb⟩ := eq_conj_of_preservesPointRadicals (Or.inl rfl) a
    (preservesPointRadicals_of_one a hi hi hmap)
  exact ⟨b,hb.symm⟩

/-- On any binary four-space, no outer automorphism fixes every transvection
with a given nonzero center. The automorphism and transvections use the actual
full linear group, without a model tag or an assumed classification. -/
theorem fullCenterOuterObstruction_four {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (hd : finrank (ZMod 2) V = 4) : FullCenterOuterObstruction V := by
  intro a ha i hi hfull
  let c : V ≃ₗ[ZMod 2] Space 4 := LinearEquiv.ofFinrankEq _ _ (by simpa [Space] using hd)
  let E : LinearMap.GeneralLinearGroup (ZMod 2) V ≃* LinearGroup 4 :=
    (LinearMap.GeneralLinearGroup.congrLinearEquiv c).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Space 4))
  let b := MulAut.congr E a
  have hb : b ∈ MulAut.innerSubgroup (LinearGroup 4) := by
    apply inner_of_fixed_full_center b (c i) (by simpa using hi)
    intro f hf
    let f' := f.comp c.toLinearMap
    have hf' : f' i = 0 := hf
    let t := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm
      (transvection i f' hf')
    have hE : E t = transvection (c i) f hf := by
      apply LinearEquiv.ext
      intro u
      change c (c.symm u + f (c (c.symm u)) • i) = u + f u • c i
      simp only [map_add,map_smul,c.apply_symm_apply]
    have he : b (E t) = E (a t) := by
      change E (a (E.symm (E t))) = E (a t)
      rw [E.symm_apply_apply]
    rw [← hE,he]
    exact congrArg E (hfull f' hf')
  rw [← MulAut.map_innerSubgroup_congr E] at hb
  obtain ⟨a',ha',he⟩ := hb
  exact ha ((MulAut.congr E).injective he ▸ ha')

end Representation.BinaryOffender
