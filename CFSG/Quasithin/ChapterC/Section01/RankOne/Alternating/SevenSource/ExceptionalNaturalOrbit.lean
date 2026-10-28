module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.ExceptionalSpan
public import Theory.SpecificGroups.SL2.Affine.Action
public import Theory.ElementaryAbelian.VectorSpace

/-!
# The natural subgroup lies in the original alpha orbit

A nonzero normal elementary subgroup of a finite two-group meets its center.
For a natural SL₂-module, the ambient group is transitive on its nonzero
vectors. A single vector in the Sylow omega center therefore generates the
whole natural subgroup inside the normal closure of the Thompson alpha.
This removes the orbit-containment premise in the selected local-span proof.

Source: Aschbacher–Smith C.1.21(4), applied in C.1.24, pp.128–131.
-/

public section
open Subgroup Stellmacher Representation
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
open ChapterB
variable {G : Type*} [Group G] [Finite G]
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

/-- Actual natural coordinates put the complete moving subgroup in the
alpha closure, independently of extra central factors. -/
theorem natural_le_alpha_closure (T : Sylow 2 G)
    (W : Subgroup G) [W.Normal] [IsElementaryAbelian 2 W]
    (q : G →* SL(2,F)) (hq : Function.Surjective q)
    (p : Additive W ≃ₗ[ZMod 2] (Fin 2 → F))
    (he : ∀ (g : G) (v : Additive W),
      p (Additive.ofMul (MulAut.conjNormal g v.toMul)) = specialLinearNatural 2 (q g) (p v)) :
    W ≤ normalClosure (thompsonAlpha (T : Subgroup G) : Set G) := by
  let : Nontrivial (Additive W) := p.toEquiv.nontrivial
  let : Nontrivial W := by
    obtain ⟨a,b,hab⟩ := exists_pair_ne (Additive W)
    exact ⟨a.toMul,b.toMul,fun h => hab (Additive.toMul.injective h)⟩
  have hWne : W ≠ ⊥ := (nontrivial_iff_ne_bot W).mp inferInstance
  have hWT : W ≤ T := (IsElementaryAbelian.isPGroup 2 W).le_sylow_of_normal T
  let E := W.subgroupOf (T : Subgroup G)
  let : E.Normal := inferInstance
  have hEne : E ≠ ⊥ := by
    intro hz
    have hh := congrArg (map (T : Subgroup G).subtype) hz
    rw [map_subgroupOf_eq_of_le hWT,Subgroup.map_bot] at hh
    exact hWne hh
  have hZne := center_inf_ne_bot_of_normal T.isPGroup' E hEne
  obtain ⟨z,hz,hzne⟩ := (center (T : Subgroup G) ⊓ E).bot_or_exists_ne_one.resolve_left hZne
  let w : W := ⟨z,hz.2⟩
  have hwne : w ≠ 1 := by
    intro heq
    apply hzne
    apply Subtype.ext
    exact congrArg (fun w : W => (w : G)) heq
  have hwZ : (w : G) ∈ omegaOneCenterAmbient (T : Subgroup G) :=
    (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨z.property,elemPow_eq_one_of_isElementaryAbelian _ w.property,
        fun t ht => congrArg Subtype.val ((mem_center_iff.mp hz.1) ⟨t,ht⟩)⟩
  let D := normalClosure (thompsonAlpha (T : Subgroup G) : Set G)
  have hwD : (w : G) ∈ D := subset_normalClosure
    ((omegaCenter_le_omegaCenter_maxJ (T : Subgroup G)) hwZ)
  intro x hx
  by_cases hx1 : x = 1
  · exact hx1 ▸ D.one_mem
  let v : W := ⟨x,hx⟩
  have hw0 : p (Additive.ofMul w) ≠ 0 := by
    intro h
    exact hwne (p.injective (h.trans p.map_zero.symm))
  have hv0 : p (Additive.ofMul v) ≠ 0 := by
    intro h
    have hv : v = 1 := p.injective (h.trans p.map_zero.symm)
    exact hx1 (congrArg Subtype.val hv)
  obtain ⟨a,ha⟩ := Matrix.SL2.exists_mulVec_eq F
    (p (Additive.ofMul w)) (p (Additive.ofMul v)) hw0 hv0
  obtain ⟨g,rfl⟩ := hq a
  have hgw : MulAut.conjNormal g w = v := by
    apply Additive.ofMul.injective
    apply p.injective
    exact (he g (Additive.ofMul w)).trans ha
  have hh := (inferInstance : D.Normal).conj_mem _ hwD g
  have hval := congrArg (fun u : W => (u : G)) hgw
  change g * (w : G) * g⁻¹ = x at hval
  rwa [hval] at hh

end CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
