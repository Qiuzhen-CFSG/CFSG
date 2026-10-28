module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveSections

/-!
# Natural kernels on the same original paired symmetric-five quotient

Retain the original quotient, marked product, actual subgroup, and chosen
symmetric-factor epimorphism. The marked moved-space section identifies
its literal kernel with the natural augmentation module and intertwines
the actual conjugation action. Both factor orientations are treated.
The combined consumers retain the already proved quotient sections and
expose these kernel coordinates for the Baumann-factor recognition.

Source: Aschbacher–Smith E.2.3 and 10.2.1, pp.216–217 and742–743.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB.SourceInduction BinaryPermutation BinaryPermutation.AlternatingFiveExtension
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
set_option backward.isDefEq.respectTransparency false
local notation "S5" => Equiv.Perm (Fin 5)

omit [Finite G] [Finite H] in
private theorem natural_kernel_on_axis
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (Y : Subgroup H) (em : Y ≃* S5 × S5)
    (P B : Subgroup G) (hPY : P.map q ≤ Y)
    (f : P →* S5) (hfk : f.ker = q.ker.subgroupOf P)
    (hcoord : ∀ g : P, ∀ hg : q (g:G) ∈ Y, f g = (em ⟨q (g:G),hg⟩).1)
    (hK : q.ker ⊓ P = ⁅U,B⁆)
    (s : core (Fin 5) →ₗ[ZMod 2] Additive U) (hs : Function.Injective s)
    (hr : s.range = NormalElementaryQuotient.commutatorSpace U B)
    (he : ∀ g : Y, ∀ v, s (coreRepresentation (Fin 5) (em g).1 v) =
      NormalElementaryQuotient.representation U q hq hk (g:H) (s v)) :
    ∃ e : f.ker ≃* V, ∀ (g : P) (v : f.ker),
      e (MulAut.conjNormal g v) = coreAction (f g) (e v) := by
  have hkernel : f.ker.map P.subtype = (ambientNaturalMap U s).range := by
    rw [hfk,subgroupOf_map_subtype,hK,ambientNaturalMap_range_eq_commutator U B s hr]
  have hact (g : P) (v : core (Fin 5)) :
      ((s (coreRepresentation (Fin 5) (f g) v)).toMul:G) =
        (g:G) * ((s v).toMul:G) * (g:G)⁻¹ := by
    have hgy : q (g:G) ∈ Y := hPY (mem_map_of_mem q g.property)
    rw [hcoord g hgy]
    have hh := congrArg (fun z : Additive U => (z.toMul:G)) (he ⟨q (g:G),hgy⟩ v)
    rw [NormalElementaryQuotient.representation_apply] at hh
    exact hh
  obtain ⟨e,_,heq⟩ := exists_kernel_equiv_of_natural_range U P f s hs hkernel hact
  exact ⟨e,heq⟩

theorem paired_first_axis_natural_kernel
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    (P : Subgroup G)
    (hPY : P.map q ≤ offenderSubgroup (NormalElementaryQuotient.representation U q hq hk))
    (f : P →* S5) (hfk : f.ker = q.ker.subgroupOf P)
    (hcoord : ∀ g : P, ∀ hg : q (g:G) ∈
      offenderSubgroup (NormalElementaryQuotient.representation U q hq hk),
      f g = (c.action.groupEquiv ⟨q (g:G),hg⟩).1)
    (hK : q.ker ⊓ P = ⁅U,factorResidual q
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)) d.first⁆) :
    ∃ e : f.ker ≃* V, ∀ (g : P) (v : f.ker),
      e (MulAut.conjNormal g v) = coreAction (f g) (e v) := by
  obtain ⟨s₁,s₂,h₁,_,he₁,_,hr₁,_⟩ := paired_symmetric_residual_module_sections U q hq hk d c
  have hs : Function.Injective s₁ := by
    intro x y h
    have hh := congrArg c.symmetricCoreMap h
    rw [h₁,h₁] at hh
    exact congrArg Prod.fst hh
  exact natural_kernel_on_axis U q hq hk _ c.action.groupEquiv P _ hPY
    f hfk hcoord hK s₁ hs hr₁ he₁

theorem paired_second_axis_natural_kernel
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    (P : Subgroup G)
    (hPY : P.map q ≤ offenderSubgroup (NormalElementaryQuotient.representation U q hq hk))
    (f : P →* S5) (hfk : f.ker = q.ker.subgroupOf P)
    (hcoord : ∀ g : P, ∀ hg : q (g:G) ∈
      offenderSubgroup (NormalElementaryQuotient.representation U q hq hk),
      f g = (c.action.groupEquiv ⟨q (g:G),hg⟩).2)
    (hK : q.ker ⊓ P = ⁅U,factorResidual q
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)) d.second⁆) :
    ∃ e : f.ker ≃* V, ∀ (g : P) (v : f.ker),
      e (MulAut.conjNormal g v) = coreAction (f g) (e v) := by
  obtain ⟨s₁,s₂,_,h₂,_,he₂,_,hr₂⟩ := paired_symmetric_residual_module_sections U q hq hk d c
  have hs : Function.Injective s₂ := by
    intro x y h
    have hh := congrArg c.symmetricCoreMap h
    rw [h₂,h₂] at hh
    exact congrArg Prod.snd hh
  exact natural_kernel_on_axis U q hq hk _ (c.action.groupEquiv.trans MulEquiv.prodComm)
    P _ hPY f hfk hcoord hK s₂ hs hr₂ he₂

theorem paired_first_axis_natural_quotient
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    (P : Subgroup G)
    (hP : P.map q = d.first.map
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype)
    (hK : q.ker ⊓ P = ⁅U,factorResidual q
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)) d.first⁆) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)
    ∃ f : P →* S5, Function.Surjective f ∧ f.ker = q.ker.subgroupOf P ∧
      (∀ g : P, ∀ hg : q (g:G) ∈ Y, f g = (c.action.groupEquiv ⟨q (g:G),hg⟩).1) ∧
      ∃ e : f.ker ≃* V,
        (∀ (g : P) (v : f.ker), e (MulAut.conjNormal g v) = coreAction (f g) (e v)) ∧
        ∃ σ : S5 →* P, f.comp σ = MonoidHom.id _ := by
  obtain ⟨f,hf,hfk,hcoord,σ,hσ⟩ := paired_first_axis_section U q hq hk d c P hP hK
  have hPY : P.map q ≤ offenderSubgroup (NormalElementaryQuotient.representation U q hq hk) :=
    hP ▸ map_subtype_le d.first
  obtain ⟨e,he⟩ := paired_first_axis_natural_kernel U q hq hk d c P hPY f hfk hcoord hK
  exact ⟨f,hf,hfk,hcoord,e,he,σ,hσ⟩

theorem paired_second_axis_natural_quotient
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    (P : Subgroup G)
    (hP : P.map q = d.second.map
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype)
    (hK : q.ker ⊓ P = ⁅U,factorResidual q
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)) d.second⁆) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)
    ∃ f : P →* S5, Function.Surjective f ∧ f.ker = q.ker.subgroupOf P ∧
      (∀ g : P, ∀ hg : q (g:G) ∈ Y, f g = (c.action.groupEquiv ⟨q (g:G),hg⟩).2) ∧
      ∃ e : f.ker ≃* V,
        (∀ (g : P) (v : f.ker), e (MulAut.conjNormal g v) = coreAction (f g) (e v)) ∧
        ∃ σ : S5 →* P, f.comp σ = MonoidHom.id _ := by
  obtain ⟨f,hf,hfk,hcoord,σ,hσ⟩ := paired_second_axis_section U q hq hk d c P hP hK
  have hPY : P.map q ≤ offenderSubgroup (NormalElementaryQuotient.representation U q hq hk) :=
    hP ▸ map_subtype_le d.second
  obtain ⟨e,he⟩ := paired_second_axis_natural_kernel U q hq hk d c P hPY f hfk hcoord hK
  exact ⟨f,hf,hfk,hcoord,e,he,σ,hσ⟩

end CFSG.Quasithin.ChapterE.ThompsonAction
