module

public import Theory.Representation.G2BinaryIsotropicThree.Basic
public import Theory.Representation.G2NaturalOffenders


/-!
# A single displacement fills an offender's fixed three-space

For the actual binary A–B–C offender, C(1) has displacement range equal to
its fixed three-space. The proved natural offender classification transports
this equality to every offender. This is the precise native input needed to
identify [V,Vᵍ], C_V(Vᵍ), and V∩Vᵍ in the original unitary source argument.

Source: Aschbacher–Smith B.4.6(13) and 13.3.12(4), printed pp.90 and890.
-/

public section

open Subgroup Module Submodule Representation Representation.BinaryOffender
namespace Atlas.G2.Natural.BinaryIsotropicThree
open BinaryNondegeneratePlane Atlas.G2.Restricted.NaturalCoordinates

theorem fixed_elementary_eq_target : fixedSpace rho (EvenTwoRank.elementary K)=target false := by
  exact NaturalOffenders.fixedSpace_elementary

theorem rootC_displacement_range : LinearMap.range (rho (rootC (1:K))-1)=target false := by
  apply le_antisymm
  · rintro _ ⟨v,rfl⟩
    change (rho (rootC (1:K)) v-v) 3=0 ∧
      (rho (rootC (1:K)) v-v) 4=0 ∧ (rho (rootC (1:K)) v-v) 5=0
    simp [action_rootC]
  · intro v hv
    refine ⟨![0,0,0,v 1,v 2,v 0],?_⟩
    change v 3=0 ∧ v 4=0 ∧ v 5=0 at hv
    ext i
    fin_cases i <;> simp [action_rootC,hv.1,hv.2.1,hv.2.2]

private theorem conjugate_displacement (g t : Model K) :
    LinearMap.range (rho (g*t*g⁻¹)-1)=(LinearMap.range (rho t-1)).map (rho g) := by
  have he : rho (g*t*g⁻¹)-1=(rho g).comp ((rho t-1).comp (rho g⁻¹)) := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.sub_apply,LinearMap.comp_apply,Module.End.one_apply,map_sub,
      map_mul,Module.End.mul_apply,rho.self_inv_apply]
  rw [he,LinearMap.range_comp,LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (rho.apply_bijective g⁻¹).surjective,Submodule.map_top]

private theorem fixed_conjugate (g : Model K) (A : Subgroup (Model K)) :
    fixedSpace rho (A.map (MulAut.conj g).toMonoidHom)=(fixedSpace rho A).map (rho g) := by
  let E := LinearEquiv.ofBijective (rho g) (rho.apply_bijective g)
  symm
  apply fixedSpace_map_equivariant rho rho (MulAut.conj g).toMonoidHom E
  intro a v
  change rho g (rho a v)=rho (g*a*g⁻¹) (rho g v)
  simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]

theorem offender_fixed_is_single_displacement (A : Subgroup (Model K))
    (hA : IsOffender rho A) :
    ∃t∈A,fixedSpace rho A=LinearMap.range (rho t-1) := by
  obtain ⟨g,hg⟩ := NaturalOffenders.offender_conjugate_elementary
    (F:=K) (n:=1) (by norm_num) (by decide) A hA
  refine ⟨g*rootC 1*g⁻¹,?_,?_⟩
  · rw [hg]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (NaturalOffenders.rootC_mem_elementary 1)
  · rw [hg,fixed_conjugate,fixed_elementary_eq_target,conjugate_displacement,rootC_displacement_range]
end Atlas.G2.Natural.BinaryIsotropicThree
