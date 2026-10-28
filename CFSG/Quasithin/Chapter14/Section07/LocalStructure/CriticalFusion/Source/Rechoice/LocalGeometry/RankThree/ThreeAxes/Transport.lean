module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.MovedPlane

/-!
# Transport of full axis actions

An ambient automorphism preserving the original carrier transports every
pointwise axis realization. Applying this to conjugation by the actual Sylow
element supplies the third axis in the moved-plane argument.

Source: Aschbacher–Smith, proof of 14.7.70, printed pp.1073–1074.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.ThreeAxes
noncomputable section
variable {G : Type*} [Group G]

theorem realizesAxis_mono {A P Q C : Subgroup G} (h : RealizesAxis A P Q) (hQC : Q ≤ C) :
    RealizesAxis A P C := by
  intro f hd hf
  obtain ⟨q,hq,hn,he⟩ := h f hd hf
  exact ⟨q,hQC hq,hn,he⟩

theorem realizesAxis_map (A P Q : Subgroup G) (a : MulAut G)
    (ha : A.map a.toMonoidHom = A) (h : RealizesAxis A P Q) :
    RealizesAxis A (P.map a.toMonoidHom) (Q.map a.toMonoidHom) := by
  let ea : A ≃* A := (A.equivMapOfInjective a.toMonoidHom a.injective).trans
    (MulEquiv.subgroupCongr ha)
  have ea_val (x : A) : (ea x : G) = a x := rfl
  have ea_symm_val (x : A) : (ea.symm x : G) = a.symm x := by
    apply a.injective
    change (ea (ea.symm x) : G) = a (a.symm (x : G))
    rw [ea.apply_symm_apply,a.apply_symm_apply]
  intro f hd hf
  let f0 : MulAut A := ea.trans (f.trans ea.symm)
  have hf0 (x : A) : (f0 x : G) = a.symm (f (ea x)) := ea_symm_val (f (ea x))
  have hd0 : ∀ x : A, (f0 x : G) * (x : G)⁻¹ ∈ P := by
    intro x
    have hh := hd (ea x)
    rw [mem_map_equiv] at hh
    simpa only [hf0,map_mul,map_inv,ea_val,a.symm_apply_apply] using hh
  have hfix0 : ∀ x : A, (x : G) ∈ P → f0 x = x := by
    intro x hx
    have hm : (ea x : G) ∈ P.map a.toMonoidHom := mem_map_of_mem a.toMonoidHom hx
    change ea.symm (f (ea x)) = x
    rw [hf (ea x) hm,ea.symm_apply_apply]
  obtain ⟨q,hq,hn,he⟩ := h f0 hd0 hfix0
  have formula (x : A) : a q * (x : G) * (a q)⁻¹ = (f x : G) := by
    have hh := congrArg a (he (ea.symm x))
    rw [map_mul,map_mul,map_inv,ea_symm_val,a.apply_symm_apply] at hh
    rw [hf0,a.apply_symm_apply,ea.apply_symm_apply] at hh
    exact hh
  refine ⟨a q,mem_map_of_mem a.toMonoidHom hq,?_,formula⟩
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [formula ⟨y,hy⟩]
    exact (f ⟨y,hy⟩).property
  · intro hy
    let z : A := ⟨a q * y * (a q)⁻¹,hy⟩
    obtain ⟨x,hx⟩ := f.surjective z
    have hh : a q * (x : G) * (a q)⁻¹ = a q * y * (a q)⁻¹ := by
      simpa only [hx] using formula x
    have heq : (x : G) = y := by
      have := congrArg (fun w => (a q)⁻¹ * w * a q) hh
      simpa [mul_assoc] using this
    exact heq ▸ x.property

end
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.ThreeAxes
