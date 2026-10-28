module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.Irreducible
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.CentralFactorWholeAction
/-!
# Invariant subgroups of the marked central product

The full orthogonal square action on the four-dimensional quotient is
irreducible. Therefore an invariant subgroup is either central or together
with the center generates the whole central product. The proof transports
the literal action through the quaternion coordinates; it does not assume
the quaternion factor is preserved by each automorphism.

Source: Aschbacher--Smith 2.4.29, printed p.545.
-/
public section
open Subgroup
namespace Subgroup.QuaternionCentralProductData
variable {P D E F : Type*} [Group P] [Finite P] [Group D] [IsElementaryAbelian 2 D]
  [Group E] [Group F] (d : QuaternionCentralProductData P) (e : E ≃* P×D)

theorem centralFactor_squareCoordinates_apply (a : MulAut E) (x : E) :
    d.squareCoordinates (Additive.ofMul (centralFactorProjection e (a x))) =
      (BinaryFourPlus.wreathToIsometry (d.centralFactorWreathAction e a)).val
        (d.squareCoordinates (Additive.ofMul (centralFactorProjection e x))) := by
  have hh (i : BinaryFourPlus.C2) := d.centralFactorWreathAction_apply e a
    (QuotientGroup.mk' (center E) x) i
  simp only [quotientAut_apply_mk,centralFactorQuotientEquiv_mk] at hh
  have hcoord (i : BinaryFourPlus.C2) :
      BinaryFourPlus.coordinate (d.squareCoordinates (Additive.ofMul (centralFactorProjection e (a x)))) i =
      BinaryFourPlus.coordinate
        ((BinaryFourPlus.wreathToIsometry (d.centralFactorWreathAction e a)).val
          (d.squareCoordinates (Additive.ofMul (centralFactorProjection e x)))) i := by
    rw [BinaryFourPlus.wreathToIsometry_coordinate]
    exact hh i
  apply Prod.ext
  · simpa [BinaryFourPlus.coordinate] using hcoord 1
  · simpa only [BinaryFourPlus.coordinate,if_neg BinaryFourPlus.swapIndex_ne_one] using
      hcoord BinaryFourPlus.swapIndex

theorem centralFactor_invariant_subgroup (f : F →* MulAut E)
    (hf : Function.Surjective ((d.centralFactorWreathAction e).comp f))
    (A : Subgroup E) (hA : ∀ t : F,∀x∈A,f t x∈A) :
    A≤center E ∨ A⊔center E=⊤ := by
  let c : E →* Multiplicative BinaryFourPlus.V :=
    d.squareCoordinates.toAddEquiv.toMultiplicativeRight.toMonoidHom.comp
      (centralFactorProjection e)
  have hker : c.ker=center E := by
    ext x
    change d.squareCoordinates.toAddEquiv.toMultiplicativeRight (centralFactorProjection e x)=1 ↔ _
    rw [map_eq_one_iff _ d.squareCoordinates.toAddEquiv.toMultiplicativeRight.injective,←centralFactorProjection_ker e]
    rfl
  let B : Submodule (ZMod 2) BinaryFourPlus.V := AddSubgroup.toZModSubmodule 2 (A.map c).toAddSubgroup
  have hB : ∀w : BinaryFourPlus.Wreath,∀v∈B,(BinaryFourPlus.wreathToIsometry w).val v∈B := by
    intro w v hv
    obtain ⟨t,ht⟩ := hf w
    change Multiplicative.ofAdd v∈A.map c at hv
    obtain ⟨x,hx,hcx⟩ := hv
    have hm := mem_map_of_mem c (hA t x hx)
    have he : c (f t x)=Multiplicative.ofAdd ((BinaryFourPlus.wreathToIsometry w).val v) := by
      apply Multiplicative.toAdd.injective
      have hh := d.centralFactor_squareCoordinates_apply e (f t) x
      change (c (f t x)).toAdd=
        (BinaryFourPlus.wreathToIsometry ((d.centralFactorWreathAction e).comp f t)).val (c x).toAdd at hh
      rwa [ht,hcx] at hh
    change Multiplicative.ofAdd ((BinaryFourPlus.wreathToIsometry w).val v)∈A.map c
    exact he ▸ hm
  rcases BinaryFourPlus.invariant_submodule_eq_bot_or_top B hB with hb | hb
  · left
    rw [←hker]
    intro x hx
    have hh : (c x).toAdd∈B := mem_map_of_mem c hx
    rw [hb] at hh
    exact hh
  · right
    have ha : A.map c=⊤ := by
      apply top_unique
      intro v _
      have hh : v.toAdd∈B := hb ▸ Submodule.mem_top
      exact hh
    have hh := congrArg (comap c) ha
    rwa [comap_map_eq,hker,comap_top] at hh
end Subgroup.QuaternionCentralProductData
