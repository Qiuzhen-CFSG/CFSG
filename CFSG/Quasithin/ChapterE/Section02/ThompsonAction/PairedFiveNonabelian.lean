module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveMovingActor
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveModules

/-!
# A nonabelian Sylow action on a moved submodule of the paired Baumann center

The two original residual commutator modules are disjoint, as their actual
class-sum sections map to opposite coordinates. A prescribed Sylow element
exchanges the residual factors. If the Sylow action on W were abelian,
a factor actor and its exchanged conjugate would induce the same action.
Their displacements lie in the two disjoint modules and hence vanish.
Since the factor Sylow intersections generate the residual Sylow, this
contradicts its nontrivial action on W.

Source: Aschbacher–Smith E.2.3 and the transvection comparison in 10.2.1,
printed pp.216–217 and 743. All factors, sections and the exchanger are
obtained on the original marked quotient.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction BinaryPermutation
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

/-- The two literal residual commutator modules have trivial intersection. -/
theorem paired_symmetric_residual_modules_disjoint
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5))) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
    (⁅U,factorResidual q Y d.first⁆ : Subgroup G) ⊓
      ⁅U,factorResidual q Y d.second⁆ = ⊥ := by
  let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
  obtain ⟨s₁,s₂,h₁,h₂,_,_,hr₁,hr₂⟩ := paired_symmetric_residual_module_sections U q hq hker d c
  apply bot_unique
  intro x hx
  let v : Additive U := Additive.ofMul ⟨x,(commutator_le_left U _) hx.1⟩
  have hv₁ : v ∈ s₁.range := hr₁.symm ▸ hx.1
  have hv₂ : v ∈ s₂.range := hr₂.symm ▸ hx.2
  obtain ⟨a,ha⟩ := hv₁
  obtain ⟨b,hb⟩ := hv₂
  have he := congrArg c.symmetricCoreMap (ha.trans hb.symm)
  rw [h₁,h₂] at he
  have ha0 : a = 0 := congrArg Prod.fst he
  have hv0 : v = 0 := by rw [←ha,ha0,map_zero]
  exact congrArg (fun z : Additive U => (z.toMul : G)) hv0

omit [Finite G] [Finite H] in
private theorem conjugate_same_displacement_of_derived_centralizes
    (T W : Subgroup G) (hn : T ≤ normalizer (W : Set G))
    (hc : ⁅T,T⁆ ≤ centralizer (W : Set G))
    {t g x : G} (ht : t ∈ T) (hg : g ∈ T) (hx : x ∈ W) :
    ⁅(MulAut.conj t) g,x⁆ = ⁅g,x⁆ := by
  have hz := hc (commutator_mem_commutator ht hg)
  have hy : g*x*g⁻¹ ∈ W := (mem_normalizer_iff.mp (hn hg) x).mp hx
  have he := hz (g*x*g⁻¹) hy
  change (t*g*t⁻¹)*x*(t*g*t⁻¹)⁻¹*x⁻¹ = g*x*g⁻¹*x⁻¹
  calc
    _ = ⁅t,g⁆ * (g*x*g⁻¹) * ⁅t,g⁆⁻¹ * x⁻¹ := by
      simp only [commutatorElement_def]; group
    _ = g*x*g⁻¹*x⁻¹ := by rw [←he,mul_inv_cancel_right]

omit [Finite G] [Finite H] in
private theorem paired_displacement_centralizes_of_derived_centralizes
    (T W A B V₁ V₂ : Subgroup G) (t : G) (ht : t ∈ T)
    (he : A.map (MulAut.conj t).toMonoidHom = B)
    (hn : T ≤ normalizer (W : Set G))
    (hc : ⁅T,T⁆ ≤ centralizer (W : Set G))
    (hd : V₁ ⊓ V₂ = ⊥)
    (h₁ : ∀ g ∈ T ⊓ A, ∀ x ∈ W, ⁅g,x⁆ ∈ V₁)
    (h₂ : ∀ g ∈ T ⊓ B, ∀ x ∈ W, ⁅g,x⁆ ∈ V₂) :
    T ⊓ A ≤ centralizer (W : Set G) := by
  intro g hg x hx
  have hgt : (MulAut.conj t) g ∈ T := T.mul_mem (T.mul_mem ht hg.1) (T.inv_mem ht)
  have hgb : (MulAut.conj t) g ∈ B := he ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom hg.2
  have heq := conjugate_same_displacement_of_derived_centralizes T W hn hc ht hg.1 hx
  have hv₂ : ⁅g,x⁆ ∈ V₂ := heq ▸ h₂ _ ⟨hgt,hgb⟩ x hx
  have hz : ⁅g,x⁆ = 1 := mem_bot.mp (hd ▸ (show ⁅g,x⁆ ∈ V₁ ⊓ V₂ from ⟨h₁ g hg x hx,hv₂⟩))
  exact (commutatorElement_eq_one_iff_mul_comm.mp hz).symm

/-- Any invariant submodule of the original Baumann center moved by the
residual Sylow has nonabelian Sylow action. -/
theorem paired_baumann_derived_not_centralizes
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
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
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first)
    (W : Subgroup G) (hW : W ≤ omegaOneCenterAmbient (baumann (T : Subgroup G)))
    (hn : (T : Subgroup G) ≤ normalizer (W : Set G))
    (hm : ¬ (T : Subgroup G) ⊓ pResidual 2 G ≤ centralizer (W : Set G)) :
    ¬ ⁅(T : Subgroup G),(T : Subgroup G)⁆ ≤ centralizer (W : Set G) := by
  let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
  let A := factorResidual q Y d.first
  let B := factorResidual q Y d.second
  let V₁ := ⁅U,A⁆
  let V₂ := ⁅U,B⁆
  have hd : V₁ ⊓ V₂ = ⊥ := paired_symmetric_residual_modules_disjoint U q hq hker d c
  obtain ⟨t,ht,hAB,hBA⟩ := paired_residual_factors_exchange T U q hq hker d hexchange
  obtain ⟨v₁,v₂,hv₁,_,hv₂,_,h₁,h₂⟩ :=
    paired_symmetric_baumann_center_displacement T hP U hU hJ q hq hker d c hexchange
  have hD₁ : ∀ g ∈ (T : Subgroup G) ⊓ A, ∀ x ∈ W, ⁅g,x⁆ ∈ V₁ := by
    intro g hg x hx
    rcases h₁ g hg x (hW hx) with he|he
    · exact he ▸ V₁.one_mem
    · exact he ▸ hv₁
  have hD₂ : ∀ g ∈ (T : Subgroup G) ⊓ B, ∀ x ∈ W, ⁅g,x⁆ ∈ V₂ := by
    intro g hg x hx
    rcases h₂ g hg x (hW hx) with he|he
    · exact he ▸ V₂.one_mem
    · exact he ▸ hv₂
  intro hc
  apply hm
  rw [paired_residual_sylow_factors_generate T hP U hU hJ q hq hker d]
  exact sup_le
    (paired_displacement_centralizes_of_derived_centralizes _ W A B V₁ V₂ t ht hAB hn hc hd hD₁ hD₂)
    (paired_displacement_centralizes_of_derived_centralizes _ W B A V₂ V₁ t ht hBA hn hc
      (inf_comm _ _ |>.trans hd) hD₂ hD₁)

end CFSG.Quasithin.ChapterE.ThompsonAction
