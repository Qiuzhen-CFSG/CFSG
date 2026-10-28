module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveModules

/-!
# Cross-centralizers of the two symmetric-five module supports

The full second factor acts trivially on the first natural support, and
conversely. Equivariance of the literal moved-module sections transports
this coordinate fact back to commuting elements in the original group.
Source: Aschbacher–Smith E.2.3, applied in10.2.1, pp.216–217 and743.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB.SourceInduction BinaryPermutation
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
set_option backward.isDefEq.respectTransparency false in
theorem paired_cross_module_centralizers
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5))) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
    factorPreimage q Y d.second ≤ centralizer ((⁅U,factorResidual q Y d.first⁆ : Subgroup G) : Set G) ∧
      factorPreimage q Y d.first ≤ centralizer ((⁅U,factorResidual q Y d.second⁆ : Subgroup G) : Set G) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  obtain ⟨s₁,s₂,_,_,he₁,he₂,hr₁,hr₂⟩ := paired_symmetric_residual_module_sections U q hq hker d c
  constructor
  · intro g hg x hx
    obtain ⟨y,hy,hyg⟩ := hg
    have hcoord : (c.action.groupEquiv y).1 = 1 := by
      rw [←c.second_eq] at hy
      obtain ⟨z,hz,rfl⟩ := hy
      simpa using hz.1
    let v : Additive U := Additive.ofMul ⟨x,(commutator_le_left U _) hx⟩
    have hv : v ∈ s₁.range := by rw [hr₁]; exact hx
    obtain ⟨w,hw⟩ := hv
    have hf := he₁ y w
    rw [hcoord,map_one,Module.End.one_apply,hw] at hf
    change (y:H) = q g at hyg
    have hf' : α (q g) v = v := by simpa only [hyg] using hf.symm
    have hh := congrArg (fun z : Additive U => (z.toMul:G)) hf'
    change ((NormalElementaryQuotient.representation U q hq hker (q g) v).toMul : G) = _ at hh
    rw [NormalElementaryQuotient.representation_apply] at hh
    change g*x*g⁻¹=x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro g hg x hx
    obtain ⟨y,hy,hyg⟩ := hg
    have hcoord : (c.action.groupEquiv y).2 = 1 := by
      rw [←c.first_eq] at hy
      obtain ⟨z,hz,rfl⟩ := hy
      simpa using hz.2
    let v : Additive U := Additive.ofMul ⟨x,(commutator_le_left U _) hx⟩
    have hv : v ∈ s₂.range := by rw [hr₂]; exact hx
    obtain ⟨w,hw⟩ := hv
    have hf := he₂ y w
    rw [hcoord,map_one,Module.End.one_apply,hw] at hf
    change (y:H) = q g at hyg
    have hf' : α (q g) v = v := by simpa only [hyg] using hf.symm
    have hh := congrArg (fun z : Additive U => (z.toMul:G)) hf'
    change ((NormalElementaryQuotient.representation U q hq hker (q g) v).toMul : G) = _ at hh
    rw [NormalElementaryQuotient.representation_apply] at hh
    change g*x*g⁻¹=x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
end CFSG.Quasithin.ChapterE.ThompsonAction
