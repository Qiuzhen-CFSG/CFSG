module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveModules
public import Theory.GroupTheory.MarkedProductAxis
public import Theory.Representation.BinaryAlternatingFiveExtension.NaturalMovedKernel

/-!
# Sections of actual symmetric-five factor extensions

Project the literal subgroup image onto its marked full symmetric axis.
The kernel is the restricted original quotient kernel. When that kernel
is exactly the corresponding moved subgroup, the actual equivariant
natural section supplies its faithful kernel coordinates, and the existing
natural-kernel splitting theorem gives a group section.

Both orientations retain the original quotient and product marking.
Source: Aschbacher–Smith10.2.1, pp.742–743, using E.2.3.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB.SourceInduction BinaryPermutation BinaryPermutation.AlternatingFiveExtension
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
set_option backward.isDefEq.respectTransparency false

omit [Finite H] in
private theorem section_on_axis
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (Y : Subgroup H) (em : Y ≃* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5))
    (P B : Subgroup G)
    (hP : P.map q = ((⊤ : Subgroup (Equiv.Perm (Fin 5))).prod ⊥).map
      (Y.subtype.comp em.symm.toMonoidHom))
    (hK : q.ker ⊓ P = ⁅U,B⁆)
    (s : core (Fin 5) →ₗ[ZMod 2] Additive U) (hs : Function.Injective s)
    (hr : s.range = NormalElementaryQuotient.commutatorSpace U B)
    (he : ∀ g : Y, ∀ v,
      s (coreRepresentation (Fin 5) (em g).1 v) =
        NormalElementaryQuotient.representation U q hq hker (g:H) (s v)) :
    ∃ f : P →* Equiv.Perm (Fin 5), Function.Surjective f ∧
      f.ker = q.ker.subgroupOf P ∧
      (∀ g : P, ∀ hg : q (g:G) ∈ Y, f g = (em ⟨q (g:G),hg⟩).1) ∧
      ∃ σ : Equiv.Perm (Fin 5) →* P, f.comp σ = MonoidHom.id _ := by
  obtain ⟨f,hf,hfk,hfc⟩ := markedAxisProjection_surjective_ker q Y em P hP
  have hfcoord (g : P) (hg : q (g:G) ∈ Y) : f g = (em ⟨q (g:G),hg⟩).1 := hfc g
  have hk : f.ker.map P.subtype = ⁅U,B⁆ := by
    rw [hfk,subgroupOf_map_subtype,hK]
  have hact (g : P) (v : core (Fin 5)) :
      ((s (coreRepresentation (Fin 5) (f g) v)).toMul:G) =
        (g:G) * ((s v).toMul:G) * (g:G)⁻¹ := by
    have hgy : q (g:G) ∈ Y := by
      have hh := mem_map_of_mem q g.property
      rw [hP] at hh
      obtain ⟨z,_,hz⟩ := hh
      exact hz ▸ (em.symm z).property
    rw [hfcoord g hgy]
    have hh := congrArg (fun z : Additive U => (z.toMul:G)) (he ⟨q (g:G),hgy⟩ v)
    rw [NormalElementaryQuotient.representation_apply] at hh
    exact hh
  exact ⟨f,hf,hfk,hfcoord,exists_section_of_natural_commutator_range U B P f hf s hs hr hk hact⟩

theorem paired_first_axis_section
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    (P : Subgroup G)
    (hP : P.map q = d.first.map (offenderSubgroup
      (NormalElementaryQuotient.representation U q hq hker)).subtype)
    (hK : q.ker ⊓ P = ⁅U,factorResidual q (offenderSubgroup
      (NormalElementaryQuotient.representation U q hq hker)) d.first⁆) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
    ∃ f : P →* Equiv.Perm (Fin 5), Function.Surjective f ∧
      f.ker = q.ker.subgroupOf P ∧
      (∀ g : P, ∀ hg : q (g:G) ∈ Y, f g = (c.action.groupEquiv ⟨q (g:G),hg⟩).1) ∧
      ∃ σ : Equiv.Perm (Fin 5) →* P, f.comp σ = MonoidHom.id _ := by
  obtain ⟨s₁,s₂,h₁,_,he₁,_,hr₁,_⟩ := paired_symmetric_residual_module_sections U q hq hker d c
  have hs : Function.Injective s₁ := by
    intro x y h
    have hh := congrArg c.symmetricCoreMap h
    rw [h₁,h₁] at hh
    exact congrArg Prod.fst hh
  apply section_on_axis U q hq hker _ c.action.groupEquiv P _ _ hK s₁ hs hr₁ he₁
  rw [hP,←c.first_eq,map_map]
theorem paired_second_axis_section
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    (P : Subgroup G)
    (hP : P.map q = d.second.map (offenderSubgroup
      (NormalElementaryQuotient.representation U q hq hker)).subtype)
    (hK : q.ker ⊓ P = ⁅U,factorResidual q (offenderSubgroup
      (NormalElementaryQuotient.representation U q hq hker)) d.second⁆) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
    ∃ f : P →* Equiv.Perm (Fin 5), Function.Surjective f ∧
      f.ker = q.ker.subgroupOf P ∧
      (∀ g : P, ∀ hg : q (g:G) ∈ Y, f g = (c.action.groupEquiv ⟨q (g:G),hg⟩).2) ∧
      ∃ σ : Equiv.Perm (Fin 5) →* P, f.comp σ = MonoidHom.id _ := by
  obtain ⟨s₁,s₂,_,h₂,_,he₂,_,hr₂⟩ := paired_symmetric_residual_module_sections U q hq hker d c
  have hs : Function.Injective s₂ := by
    intro x y h
    have hh := congrArg c.symmetricCoreMap h
    rw [h₂,h₂] at hh
    exact congrArg Prod.snd hh
  apply section_on_axis U q hq hker _
    (c.action.groupEquiv.trans MulEquiv.prodComm) P _ _ hK s₂ hs hr₂ he₂
  rw [hP,←c.second_eq,map_map]
  ext x
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact ⟨(v.2,v.1),⟨hv.2,hv.1⟩,rfl⟩
  · rintro ⟨v,hv,rfl⟩
    exact ⟨(v.2,v.1),⟨hv.2,hv.1⟩,rfl⟩

end CFSG.Quasithin.ChapterE.ThompsonAction
