module

public import Theory.Representation.BinaryOffender.CommonCenterBound


/-!
# Equality in the common-center codimension bound

The displacement map identifies the common fixed codimension with its
image dimension. Equality with actor rank therefore makes it injective,
so the action is faithful. Saturation of the doubled bound on an invariant
subspace forces equality of its codimension with the actor rank and
faithfulness on that subspace. Every nonidentity common-center operator
is then given by an explicit nonzero transvection form and center vector.

Source: Aschbacher–Smith, F.9.16(2), equality case, printed pp.323–324.
-/

public section

open Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.BinaryOffender.CommonCenter
variable {A V:Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem actor_dim : Module.finrank (ZMod 2) (Additive A) = Nat.log 2 (Nat.card A) := by
  have hc:=Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive A)
  rw [Nat.card_zmod] at hc
  change _=Nat.log 2 (Nat.card (Additive A))
  rw [hc,Nat.log_pow Nat.one_lt_two]

theorem injective_of_fixedCodim_eq_rank (ρ:Representation (ZMod 2) A V)
    (Z:Submodule (ZMod 2) V) (e:Z≃ₗ[ZMod 2]ZMod 2)
    (hd:∀a v,ρ a v-v∈Z) (hz:∀a z,z∈Z→ρ a z=z)
    (he:fixedCodim ρ ⊤=Nat.log 2 (Nat.card A)) : Function.Injective ρ := by
  let f:=displacementMap ρ Z e hd hz
  have hn:=Subspace.finrank_add_finrank_dualCoannihilator_eq (LinearMap.range f)
  have hf:fixedSpace ρ ⊤=(LinearMap.range f).dualCoannihilator :=
    fixedSpace_eq_annihilator ρ Z e hd hz
  rw [←hf] at hn
  have hc:=fixedCodim_add_finrank ρ ⊤
  have hk:=LinearMap.finrank_range_add_finrank_ker f
  have ha:=actor_dim (A:=A)
  have hker : Module.finrank (ZMod 2) (LinearMap.ker f)=0 := by omega
  have hinj:Function.Injective f:=LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)
  intro a b hab
  apply Additive.ofMul.injective
  apply hinj
  apply LinearMap.ext
  intro v
  change e ⟨ρ a v-v,hd a v⟩=e ⟨ρ b v-v,hd b v⟩
  apply congrArg e
  apply Subtype.ext
  change ρ a v-v=ρ b v-v
  rw [hab]

theorem injective_of_fixedCodim_eq_rank_of_center_dim_le_one
    (ρ:Representation (ZMod 2) A V) (Z:Submodule (ZMod 2) V)
    (hZ:Module.finrank (ZMod 2) Z≤1)
    (hd:∀a v,ρ a v-v∈Z) (hz:∀a z,z∈Z→ρ a z=z)
    (he:fixedCodim ρ ⊤=Nat.log 2 (Nat.card A)) : Function.Injective ρ := by
  by_cases hn:Z=⊥
  · have hf:fixedSpace ρ ⊤=⊤ := by
      apply top_unique
      intro v _ a
      have hh:=hd a v
      rw [hn,Submodule.mem_bot] at hh
      exact sub_eq_zero.mp hh
    have hc:=fixedCodim_add_finrank ρ ⊤
    rw [hf,finrank_top] at hc
    have ha:=actor_dim (A:=A)
    have hdim:Module.finrank (ZMod 2) (Additive A)=0 := by omega
    let : Subsingleton (Additive A):=Module.finrank_zero_iff.mp hdim
    exact fun a b _=>Additive.ofMul.injective (Subsingleton.elim _ _)
  · have hdim:Module.finrank (ZMod 2) Z=1 := by
      have hp:0<Module.finrank (ZMod 2) Z := by
        by_contra hnot
        exact hn (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_not_pos hnot))
      omega
    let e:Z≃ₗ[ZMod 2]ZMod 2:=LinearEquiv.ofFinrankEq _ _ (by simpa using hdim)
    exact injective_of_fixedCodim_eq_rank ρ Z e hd hz he

theorem equality_of_doubled_bound (ρ:Representation (ZMod 2) A V)
    (W:Subrepresentation ρ) (Z:Submodule (ZMod 2) V)
    (hZ:Module.finrank (ZMod 2) Z≤1)
    (hd:∀a v,v∈W.toSubmodule→ρ a v-v∈Z)
    (hz:∀a z,z∈Z→ρ a z=z)
    (hcmp:Module.finrank (ZMod 2) (V ⧸ W.toSubmodule)≤Nat.log 2 (Nat.card A))
    (he:fixedCodim ρ ⊤=2*Nat.log 2 (Nat.card A)) :
    Module.finrank (ZMod 2) (V ⧸ W.toSubmodule)=Nat.log 2 (Nat.card A) ∧
      Function.Injective W.toRepresentation := by
  let Z':Submodule (ZMod 2) W.toSubmodule:=Z.comap W.toSubmodule.subtype
  have hZ':Module.finrank (ZMod 2) Z'≤1 := by
    have he':Module.finrank (ZMod 2) Z'=Module.finrank (ZMod 2) (W.toSubmodule⊓Z : Submodule (ZMod 2) V) := by
      rw [←Submodule.finrank_map_subtype_eq,Submodule.map_comap_subtype]
    exact he'.le.trans ((Submodule.finrank_mono inf_le_right).trans hZ)
  have hd':∀a v,W.toRepresentation a v-v∈Z' := fun a v=>hd a v v.property
  have hz':∀a z,z∈Z'→W.toRepresentation a z=z := fun a z hz'=>Subtype.ext (hz a z hz')
  have hc:=fixedCodim_top_le_of_center_dim_le_one W.toRepresentation Z' hZ' hd' hz'
  have hb:=fixedCodim_le_subrepresentation_add_codim ρ W ⊤
  have hw:fixedCodim W.toRepresentation ⊤=Nat.log 2 (Nat.card A) := by omega
  exact ⟨by omega,injective_of_fixedCodim_eq_rank_of_center_dim_le_one
    W.toRepresentation Z' hZ' hd' hz' hw⟩

omit [Finite A] in
theorem common_center_form_of_ne_one (ρ:Representation (ZMod 2) A V)
    (Z:Submodule (ZMod 2) V) (hZ:Module.finrank (ZMod 2) Z≤1)
    (hd:∀a v,ρ a v-v∈Z) (hz:∀a z,z∈Z→ρ a z=z)
    (hf:Function.Injective ρ) (a:A) (ha:a≠1) :
    ∃ (f:Module.Dual (ZMod 2) V) (z:V),
      f≠0 ∧ z≠0 ∧ z∈Z ∧ f z=0 ∧ ∀v,ρ a v=v+f v • z := by
  have hn:Z≠⊥ := by
    intro he
    apply ha
    apply hf
    apply LinearMap.ext
    intro v
    have hv:=hd a v
    rw [he,Submodule.mem_bot] at hv
    simpa only [map_one,Module.End.one_apply] using sub_eq_zero.mp hv
  have hdim:Module.finrank (ZMod 2) Z=1 := by
    have hp:0<Module.finrank (ZMod 2) Z := by
      by_contra hnot
      exact hn (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_not_pos hnot))
    omega
  let e:Z≃ₗ[ZMod 2]ZMod 2:=LinearEquiv.ofFinrankEq _ _ (by simpa using hdim)
  let z:V := e.symm 1
  let f:=displacement ρ Z e hd a
  have hf0:f≠0 := by
    intro he
    apply ha
    apply hf
    apply LinearMap.ext
    intro v
    have hv:displacement ρ Z e hd a v=0 := by rw [show displacement ρ Z e hd a=f from rfl,he];rfl
    simpa only [map_one,Module.End.one_apply] using (displacement_eq_zero_iff ρ Z e hd a v).mp hv
  have hz0:z≠0 := by
    intro he
    have hh:e.symm (1:ZMod 2)=0 := Subtype.ext he
    have hh':(1:ZMod 2)=0 := e.symm.injective (hh.trans e.symm.map_zero.symm)
    exact one_ne_zero hh'
  have hzZ:z∈Z := (e.symm 1).property
  refine ⟨f,z,hf0,hz0,hzZ,(displacement_eq_zero_iff ρ Z e hd a z).mpr (hz a z hzZ),?_⟩
  intro v
  have hdisp:ρ a v-v=f v • z := by
    have hh : (⟨ρ a v-v,hd a v⟩:Z)=f v • e.symm 1 := by
      apply e.injective
      rw [map_smul,e.apply_symm_apply,smul_eq_mul,mul_one]
      rfl
    exact congrArg Subtype.val hh
  rw [←hdisp]
  abel

end Representation.BinaryOffender.CommonCenter

end
