module

public import Theory.AlgebraicGroup.RootSystems.F4WeightAction.TwistedCoordinates
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses.Placement
/-!
# The exceptional map on the original coroot torus

Apply the literal exceptional root formula to the four positive coroots and
reorder them inside the actual split torus. Iteration gives the original
algebraic odd-power map on this same coroot product. A torus representative
of a genuine fixed point is conjugate to its transformed representative.
No torus invariance or class-count premise is supplied by the caller.

Source: Steinberg (1963), §12.2; exceptional root formula in GLS3, 1.15.4.
-/

public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open ReeF4.BinaryDegree.ExceptionalTensor
open ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses
open F4WeightAction
variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]

omit [CharP F 2] in
private lemma torus_commute {x y : PointGroup F}
    (hx : x ∈ F4Chevalley.splitTorus (k:=F))
    (hy : y ∈ F4Chevalley.splitTorus (k:=F)) : x*y=y*x := by
  let T := F4Chevalley.splitTorus (k:=F)
  let _ := T.carrierAlgebraicGroup
  let a := T.pointEquiv.symm ⟨x,hx⟩
  let b := T.pointEquiv.symm ⟨y,hy⟩
  have he := congrArg T.inclusion.onPoints
    (isMulCommutative_iff.mp F4Chevalley.splitTorus_isSubtorus.isMulCommutative a b)
  have ha : T.inclusion.onPoints a = x := congrArg Subtype.val (T.pointEquiv.apply_symm_apply _)
  have hb : T.inclusion.onPoints b = y := congrArg Subtype.val (T.pointEquiv.apply_symm_apply _)
  simpa only [map_mul,ha,hb] using he

omit [CharP F 2] in
lemma corootTorusElement_mem (t : Fin 4 → Fˣ) :
    corootTorusElement t ∈ F4Chevalley.splitTorus (k:=F) := by
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (algebraicCorootElement_mem_splitTorus 0 (t 0))
    (algebraicCorootElement_mem_splitTorus 1 (t 1)))
    (algebraicCorootElement_mem_splitTorus 2 (t 2)))
    (algebraicCorootElement_mem_splitTorus 3 (t 3))

omit [IsAlgClosed F] [CharP F 2] in
private lemma exceptionalParameter_simple (i : Fin 4) (t : Fˣ) :
    exceptionalParameter (typeF4SimpleRootIndex i) t =
      if i.val < 2 then t else t^2 := by
  by_cases h : i.val < 2
  · rw [if_pos h, exceptionalParameter_of_long]
    exact (typeF4SimpleRootIndex_mem_pair_iff i).mpr h
  · rw [if_neg h, exceptionalParameter_of_short]
    exact fun hh => h ((typeF4SimpleRootIndex_mem_pair_iff i).mp hh)

lemma exceptional_corootTorusElement (ψ : Monoid.End (PointGroup F))
    (hψ : HasExceptionalRootFormula ψ) (t : Fin 4 → Fˣ) :
    ψ (corootTorusElement t) = corootTorusElement (torusTwist t) := by
  simp only [corootTorusElement, map_mul, exceptional_simple_coroot ψ hψ,
    exceptionalParameter_simple]
  norm_num [torusTwist, Fin.revPerm, Fin.rev, Matrix.cons_val_two, Matrix.cons_val_three]
  let A := algebraicCorootElement (typeF4SimpleRootIndex 3) (t 0)
  let B := algebraicCorootElement (typeF4SimpleRootIndex 2) (t 1)
  let C := algebraicCorootElement (typeF4SimpleRootIndex 1) (t 2 ^ 2)
  let D := algebraicCorootElement (typeF4SimpleRootIndex 0) (t 3 ^ 2)
  change A*B*C*D=D*C*B*A
  have ha : A ∈ F4Chevalley.splitTorus (k:=F) := algebraicCorootElement_mem_splitTorus _ _
  have hb : B ∈ F4Chevalley.splitTorus (k:=F) := algebraicCorootElement_mem_splitTorus _ _
  have hc : C ∈ F4Chevalley.splitTorus (k:=F) := algebraicCorootElement_mem_splitTorus _ _
  have hd : D ∈ F4Chevalley.splitTorus (k:=F) := algebraicCorootElement_mem_splitTorus _ _
  calc
    A*B*C*D = (A*B)*(C*D) := mul_assoc _ _ _
    _ = (C*D)*(A*B) := torus_commute (Subgroup.mul_mem _ ha hb) (Subgroup.mul_mem _ hc hd)
    _ = (D*C)*(B*A) := by rw [torus_commute hc hd, torus_commute ha hb]
    _ = D*C*B*A := (mul_assoc _ _ _).symm
lemma exceptional_power_corootTorusElement (ψ : Monoid.End (PointGroup F))
    (hψ : HasExceptionalRootFormula ψ) (n : ℕ) (t : Fin 4 → Fˣ) :
    (ψ ^ n) (corootTorusElement t) = corootTorusElement ((torusTwist (F:=F))^[n] t) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ]
    change (ψ ^ n) (ψ (corootTorusElement t)) = _
    rw [exceptional_corootTorusElement ψ hψ, ih, Function.iterate_succ_apply]

lemma fixed_torus_twist_isConj (m : ℕ) (x : SourceFixedPoints.fixedGroup (F:=F) m)
    (c : PointGroup F) (t : Fin 4 → Fˣ)
    (hx : (x : PointGroup F) = c * corootTorusElement t * c⁻¹) :
    IsConj (corootTorusElement ((torusTwist (F:=F))^[2*m+1] t)) (corootTorusElement t) := by
  let ψ : Monoid.End (PointGroup F) := ExceptionalMorphism.morphism.onPoints
  have hfix : (ψ ^ (2*m+1)) (x : PointGroup F) = x := x.property
  rw [hx, map_mul, map_mul, map_inv,
    exceptional_power_corootTorusElement ψ ExceptionalMorphism.morphism_rootFormula] at hfix
  apply isConj_iff.mpr
  refine ⟨c⁻¹ * (ψ ^ (2*m+1)) c, ?_⟩
  calc
    _ = c⁻¹ * ((ψ ^ (2*m+1)) c *
      corootTorusElement ((torusTwist (F:=F))^[2*m+1] t) *
        ((ψ ^ (2*m+1)) c)⁻¹) * c := by group
    _ = c⁻¹ * (c * corootTorusElement t * c⁻¹) * c := by rw [hfix]
    _ = _ := by group

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses
