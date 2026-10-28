module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveSaturation
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveModules
public import CFSG.Quasithin.ChapterB.Section02.BaumannCenter
public import Theory.Representation.BinaryPermutation.FivePairTransvection
public import Theory.GroupTheory.ElementaryThompsonRelative
/-!
# Displacement on the original paired-five Thompson fixed subgroup

The same original quotient and paired marking identify the Thompson image.
Each original Sylow intersection with a residual factor normalizes its marked
transposition four-group. The fixed-plane calculation and the canonical
class-sum sections put every commutator in one marked line, whose center lies
in the original residual-factor commutator subgroup. No coordinate assumption
or trivial action-kernel hypothesis is added.

Source: Aschbacher–Smith E.2.3(3) and 10.2.1, printed pp.216–217 and743.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction BinaryPermutation FivePairFixedSpaces
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
private theorem D_eq_pairClosure : Offenders.D 5 = pairClosure := by
  apply congrArg Subgroup.closure
  ext a
  constructor
  · rintro ⟨i,_,rfl⟩
    fin_cases i <;> simp [Offenders.pairSwap,first,second]
  · intro ha
    rcases ha with rfl | ha
    · exact ⟨0,by decide,rfl⟩
    · exact ⟨1,by decide,ha⟩

private theorem normalizer_product_fst {A B : Subgroup Perm} {g : Perm × Perm}
    (hg : g ∈ normalizer (A.prod B : Set (Perm × Perm))) :
    g.1 ∈ normalizer (A : Set Perm) := by
  rw [mem_normalizer_iff] at hg ⊢
  intro x
  have hh := hg (x,1)
  change (x∈A ∧ 1∈B) ↔ (g.1*x*g.1⁻¹∈A ∧ g.2*1*g.2⁻¹∈B) at hh
  simpa only [mul_one,mul_inv_cancel,one_mem,and_true] using hh

private theorem normalizer_product_snd {A B : Subgroup Perm} {g : Perm × Perm}
    (hg : g ∈ normalizer (A.prod B : Set (Perm × Perm))) :
    g.2 ∈ normalizer (B : Set Perm) := by
  rw [mem_normalizer_iff] at hg ⊢
  intro x
  have hh := hg (1,x)
  change (1∈A ∧ x∈B) ↔ (g.1*1*g.1⁻¹∈A ∧ g.2*x*g.2⁻¹∈B) at hh
  simpa only [mul_one,mul_inv_cancel,one_mem,true_and] using hh

private theorem normalizer_of_mapped {X Y : Type*} [Group X] [Group Y]
    (j : X →* Y) (hj : Function.Injective j) (A : Subgroup X) (g : X)
    (hg : j g ∈ normalizer (A.map j : Set Y)) : g ∈ normalizer (A : Set X) := by
  have h := (A.map j).le_normalizer_comap j hg
  rwa [comap_map_eq_self_of_injective hj] at h

theorem paired_symmetric_fixed_displacement
    (T : Sylow 2 G)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
    ∃ v₁ v₂ : G,
      v₁ ∈ ⁅U,factorResidual q Y d.first⁆ ∧ v₁ ≠ 1 ∧
      v₂ ∈ ⁅U,factorResidual q Y d.second⁆ ∧ v₂ ≠ 1 ∧
      (∀ g ∈ (T : Subgroup G) ⊓ factorResidual q Y d.first,
        ∀ x ∈ U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G),
          ⁅g,x⁆=1 ∨ ⁅g,x⁆=v₁) ∧
      (∀ g ∈ (T : Subgroup G) ⊓ factorResidual q Y d.second,
        ∀ x ∈ U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G),
          ⁅g,x⁆=1 ∨ ⁅g,x⁆=v₂) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let j := Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom
  let σ := α.comp j
  have hj : Function.Injective j := Y.subtype_injective.comp c.action.groupEquiv.symm.injective
  obtain ⟨a,b,hab⟩ := paired_thompson_of_symmetric_model T U hU hJ q hq hker d c hexchange
  rw [D_eq_pairClosure] at hab
  let A := pairClosure.map (MulAut.conj a).toMonoidHom
  let B := pairClosure.map (MulAut.conj b).toMonoidHom
  have hk (v : Additive U) (hv : c.symmetricCoreMap v=0) (g : Perm × Perm) : σ g v=v := by
    have hfix : v ∈ Representation.invariants (α.comp Y.subtype) := c.symmetricCoreMap_ker ▸ hv
    exact hfix (c.action.groupEquiv.symm g)
  obtain ⟨s₁,s₂,h₁,h₂,he₁,he₂,hr₁,hr₂⟩ := paired_symmetric_residual_module_sections U q hq hker d c
  have hs₁ (g : Perm × Perm) (v : core (Fin 5)) :
      s₁ (coreRepresentation (Fin 5) g.1 v)=σ g (s₁ v) := by
    simpa only [σ,j,α,Y,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply,Subgroup.subtype_apply] using he₁ (c.action.groupEquiv.symm g) v
  have hs₂ (g : Perm × Perm) (v : core (Fin 5)) :
      s₂ (coreRepresentation (Fin 5) g.2 v)=σ g (s₂ v) := by
    simpa only [σ,j,α,Y,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply,Subgroup.subtype_apply] using he₂ (c.action.groupEquiv.symm g) v
  let w₁ := s₁ (coreRepresentation (Fin 5) a centerVector)
  let w₂ := s₂ (coreRepresentation (Fin 5) b centerVector)
  have hn₁ : w₁ ≠ 0 := by
    intro hz
    have hh := congrArg (fun v => (c.symmetricCoreMap v).1) hz
    simp only [w₁,h₁,map_zero,Prod.fst_zero] at hh
    have hh' := congrArg (coreRepresentation (Fin 5) a⁻¹) hh
    rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply,map_zero] at hh'
    exact centerVector_ne_zero hh'
  have hn₂ : w₂ ≠ 0 := by
    intro hz
    have hh := congrArg (fun v => (c.symmetricCoreMap v).2) hz
    simp only [w₂,h₂,map_zero,Prod.snd_zero] at hh
    have hh' := congrArg (coreRepresentation (Fin 5) b⁻¹) hh
    rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply,map_zero] at hh'
    exact centerVector_ne_zero hh'
  have hn (g : G) (hg : g ∈ T) (z : Perm × Perm) (hz : j z=q g) :
      z ∈ normalizer (A.prod B : Set (Perm × Perm)) := by
    apply normalizer_of_mapped j hj
    rw [hz,←hab]
    exact (elementaryAbelianMaxJ (T : Subgroup G)).le_normalizer_map q
      (mem_map_of_mem q ((normalizer_le_normalizer_elementaryAbelianMaxJ _)
        ((T : Subgroup G).le_normalizer hg)))
  have hf (v : Additive U) (hv : (v.toMul : G) ∈ centralizer
      (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) (z : Perm × Perm)
      (hz : z ∈ A.prod B) : FivePair.action z (c.symmetricCoreMap v)=c.symmetricCoreMap v := by
    have hfix := (NormalElementaryQuotient.mem_fixedSpace_image U q hq hker _ v).mpr hv
    have hfix' : σ z v=v := hfix ⟨j z,hab ▸ mem_map_of_mem j hz⟩
    have hcoord := c.symmetricCoreMap_action (c.action.groupEquiv.symm z) v
    have hh : c.symmetricCoreMap (σ z v)=FivePair.action z (c.symmetricCoreMap v) := by
      simpa only [σ,j,α,Y,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply,Subgroup.subtype_apply] using hcoord
    exact hh.symm.trans (congrArg c.symmetricCoreMap hfix')
  refine ⟨w₁.toMul,w₂.toMul,?_,?_,?_,?_,?_,?_⟩
  · change w₁ ∈ NormalElementaryQuotient.commutatorSpace U _
    rw [←hr₁]
    exact ⟨_,rfl⟩
  · intro he
    apply hn₁
    exact Additive.toMul.injective (Subtype.ext he)
  · change w₂ ∈ NormalElementaryQuotient.commutatorSpace U _
    rw [←hr₂]
    exact ⟨_,rfl⟩
  · intro he
    apply hn₂
    exact Additive.toMul.injective (Subtype.ext he)
  · intro g hg x hx
    have hgq := mem_map_of_mem q hg.2
    rw [paired_symmetric_first_residual_image α q hq d c] at hgq
    obtain ⟨z,hz,hzg⟩ := hgq
    have hz2 : z.2=1 := hz.2
    have hnz := normalizer_product_fst (hn g hg.1 z hzg)
    have hnza : z.1 ∈ (normalizer (pairClosure : Set Perm)).map (MulAut.conj a).toMonoidHom := by
      rwa [map_normalizer_eq_of_bijective pairClosure (MulAut.conj a).bijective]
    let v : Additive U := Additive.ofMul ⟨x,hx.1⟩
    have hf1 := congrArg Prod.fst (hf v hx.2 ((MulAut.conj a) first,1)
      ⟨mem_map_of_mem _ (subset_closure (by simp)),one_mem _⟩)
    have hf2 := congrArg Prod.fst (hf v hx.2 ((MulAut.conj a) second,1)
      ⟨mem_map_of_mem _ (subset_closure (by simp)),one_mem _⟩)
    have hdisp := FivePair.displacement_eq σ c.symmetricCoreMap hk s₁ s₂ h₁ h₂ hs₁ hs₂ z v
    rw [hz2,map_one,Module.End.one_apply,sub_self,map_zero,add_zero] at hdisp
    have hcases := conjugate_normalizer_displacement a z.1 hnza (c.symmetricCoreMap v).1 hf1 hf2
    have hconv : (((σ z v-v).toMul : U) : G)=⁅g,x⁆ := by
      simp only [toMul_sub, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      change ((α (j z) v).toMul : G) * x⁻¹=⁅g,x⁆
      rw [hzg,NormalElementaryQuotient.representation_apply]
      rfl
    rcases hcases with h | h
    · left
      rw [h,map_zero] at hdisp
      have hh := congrArg (fun v : Additive U => (v.toMul : G)) hdisp
      rwa [hconv] at hh
    · right
      rw [h] at hdisp
      have hh := congrArg (fun v : Additive U => (v.toMul : G)) hdisp
      rwa [hconv] at hh
  · intro g hg x hx
    have hgq := mem_map_of_mem q hg.2
    rw [paired_symmetric_second_residual_image α q hq d c] at hgq
    obtain ⟨z,hz,hzg⟩ := hgq
    have hz1 : z.1=1 := hz.1
    have hnz := normalizer_product_snd (hn g hg.1 z hzg)
    have hnzb : z.2 ∈ (normalizer (pairClosure : Set Perm)).map (MulAut.conj b).toMonoidHom := by
      rwa [map_normalizer_eq_of_bijective pairClosure (MulAut.conj b).bijective]
    let v : Additive U := Additive.ofMul ⟨x,hx.1⟩
    have hf1 := congrArg Prod.snd (hf v hx.2 (1,(MulAut.conj b) first)
      ⟨one_mem _,mem_map_of_mem _ (subset_closure (by simp))⟩)
    have hf2 := congrArg Prod.snd (hf v hx.2 (1,(MulAut.conj b) second)
      ⟨one_mem _,mem_map_of_mem _ (subset_closure (by simp))⟩)
    have hdisp := FivePair.displacement_eq σ c.symmetricCoreMap hk s₁ s₂ h₁ h₂ hs₁ hs₂ z v
    rw [hz1,map_one,Module.End.one_apply,sub_self,map_zero,zero_add] at hdisp
    have hcases := conjugate_normalizer_displacement b z.2 hnzb (c.symmetricCoreMap v).2 hf1 hf2
    have hconv : (((σ z v-v).toMul : U) : G)=⁅g,x⁆ := by
      simp only [toMul_sub, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      change ((α (j z) v).toMul : G) * x⁻¹=⁅g,x⁆
      rw [hzg,NormalElementaryQuotient.representation_apply]
      rfl
    rcases hcases with h | h
    · left
      rw [h,map_zero] at hdisp
      have hh := congrArg (fun v : Additive U => (v.toMul : G)) hdisp
      rwa [hconv] at hh
    · right
      rw [h] at hdisp
      have hh := congrArg (fun v : Additive U => (v.toMul : G)) hdisp
      rwa [hconv] at hh
end CFSG.Quasithin.ChapterE.ThompsonAction
