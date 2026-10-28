module

public import Theory.SpecificGroups.BinaryFour.SplitBlockPair.Identification.Orbit
public import Theory.Representation.AlternatingSevenConjugatePair.Model.InnerElements
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
import Mathlib.Algebra.Module.ZMod
import Mathlib.Tactic.FinCases

/-!
# The marked stabilizer of the binary A₇ pair

Assuming an actual equivalence between the joined group and A₇, the stabilizer
of the original vector `(0,1,0,0)` is identified with PSL₃(2). The map is induced
by the literal evaluation action on the quotient by that vector's line.
We realize this quotient with coordinates `(v₀,v₂,v₃)` and prove both its kernel
and compatibility with evaluation.

An element in the kernel of the quotient action has displacement in the marked
line. Since it fixes that line, its square is one. A nonidentity kernel element
would therefore be an involution of displacement rank at most one, whereas the
faithful four-dimensional binary A₇ representation theorem gives rank two.
Thus the quotient action is faithful; the previously proved stabilizer order
168 makes it onto GL₃(2). The canonical GL₃(2)–SL₃(2)–PSL₃(2) equivalences finish
the construction. No enumeration of the ambient linear group is required.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Lemma 14.4.4, printed p.1007 (PDF p.1024), the stabilizer of z in the generated A₇.
The separate joined-group identification remains an explicit premise here.
-/

open Representation.BinaryOffender
namespace BinaryFourSplitPair
noncomputable section

private def linearAction : Representation (ZMod 2) joined V where
  toFun g := (show V →+ V from
    { toFun := fun v => (g.val (Multiplicative.ofAdd v)).toAdd
      map_zero' := g.val.map_one
      map_add' := fun v w => g.val.map_mul _ _ }).toZModLinearMap 2
  map_one' := by ext v i; rfl
  map_mul' a b := by ext v i; rfl

private theorem linearAction_injective : Function.Injective linearAction := by
  intro g h he
  apply Subtype.ext
  apply MulEquiv.ext
  intro v
  exact LinearMap.congr_fun he v.toAdd

@[simp] private theorem linearAction_point (g : MulAction.stabilizer joined point) :
    linearAction g.val point.toAdd = point.toAdd :=
  g.property

/-- Coordinates on the quotient by the marked line: forget coordinate 1. -/
@[expose] public def pointQuotientProjection : V →ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun v := ![v 0, v 2, v 3]
  map_add' v w := by ext i; fin_cases i <;> simp
  map_smul' a v := by ext i; fin_cases i <;> simp

private def sectionMap : (Fin 3 → ZMod 2) →ₗ[ZMod 2] V where
  toFun w := ![w 0, 0, w 1, w 2]
  map_add' v w := by ext i; fin_cases i <;> simp
  map_smul' a v := by ext i; fin_cases i <;> simp

@[simp] private theorem project_section (w : Fin 3 → ZMod 2) :
    pointQuotientProjection (sectionMap w) = w := by
  ext i; fin_cases i <;> rfl

@[simp] private theorem project_point : pointQuotientProjection point.toAdd = 0 := by
  ext i; fin_cases i <;> rfl

private theorem decompose (v : V) : sectionMap (pointQuotientProjection v) + v 1 • point.toAdd = v := by
  ext i; fin_cases i <;> simp [sectionMap, pointQuotientProjection, point]

/-- The coordinate projection kills exactly the marked line. -/
public theorem pointQuotientProjection_ker : LinearMap.ker pointQuotientProjection =
    Submodule.span (ZMod 2) {point.toAdd} := by
  apply le_antisymm
  · intro v hv
    have hd := decompose v
    rw [LinearMap.mem_ker.mp hv, map_zero, zero_add] at hd
    rw [← hd]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    rw [hv]
    exact project_point

/-- Every quotient coordinate vector has a representative in the original space. -/
public theorem pointQuotientProjection_surjective :
    Function.Surjective pointQuotientProjection :=
  fun w => ⟨sectionMap w, project_section w⟩

private def quotientLinear (g : MulAction.stabilizer joined point) :
    (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
  pointQuotientProjection.comp ((linearAction g.val).comp sectionMap)

private theorem quotientLinear_project (g : MulAction.stabilizer joined point) (v : V) :
    quotientLinear g (pointQuotientProjection v) = pointQuotientProjection (linearAction g.val v) := by
  conv_rhs => rw [← decompose v]
  simp [quotientLinear, LinearMap.comp_apply, map_add, map_smul]

@[simp] private theorem quotientLinear_one (w : Fin 3 → ZMod 2) : quotientLinear 1 w = w := by
  change pointQuotientProjection (sectionMap w) = w
  exact project_section w

private theorem quotientLinear_mul (g h : MulAction.stabilizer joined point) (w : Fin 3 → ZMod 2) :
    quotientLinear (g * h) w = quotientLinear g (quotientLinear h w) := by
  change pointQuotientProjection (linearAction (g.val * h.val) (sectionMap w)) =
    quotientLinear g (pointQuotientProjection (linearAction h.val (sectionMap w)))
  rw [quotientLinear_project, map_mul]
  rfl

/-- The action induced by the literal evaluation action on the quotient by the marked line. -/
public def pointStabilizerQuotientAction : MulAction.stabilizer joined point →*
    ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) where
  toFun g :=
    { quotientLinear g with
      invFun := quotientLinear g⁻¹
      left_inv := by
        intro w
        change quotientLinear g⁻¹ (quotientLinear g w) = w
        rw [← quotientLinear_mul, inv_mul_cancel, quotientLinear_one]
      right_inv := by
        intro w
        change quotientLinear g (quotientLinear g⁻¹ w) = w
        rw [← quotientLinear_mul, mul_inv_cancel, quotientLinear_one] }
  map_one' := by apply LinearEquiv.ext; exact quotientLinear_one
  map_mul' g h := by apply LinearEquiv.ext; exact quotientLinear_mul g h

/-- The quotient action intertwines the literal evaluation action and the projection. -/
public theorem pointStabilizerQuotientAction_project
    (g : MulAction.stabilizer joined point) (v : E) :
    pointStabilizerQuotientAction g (pointQuotientProjection v.toAdd) =
      pointQuotientProjection (g.val.val v).toAdd :=
  quotientLinear_project g v.toAdd

private theorem kernel_displacement (g : MulAction.stabilizer joined point)
    (hg : pointStabilizerQuotientAction g = 1) (v : V) :
    linearAction g.val v - v = (linearAction g.val v - v) 1 • point.toAdd := by
  have hp : pointQuotientProjection (linearAction g.val v - v) = 0 := by
    rw [map_sub, ← quotientLinear_project]
    have h := LinearEquiv.congr_fun hg (pointQuotientProjection v)
    change quotientLinear g (pointQuotientProjection v) = pointQuotientProjection v at h
    rw [h, sub_self]
  have hd := decompose (linearAction g.val v - v)
  rw [hp, map_zero, zero_add] at hd
  exact hd.symm

private theorem kernel_square (g : MulAction.stabilizer joined point)
    (hg : pointStabilizerQuotientAction g = 1) : g.val ^ 2 = 1 := by
  apply linearAction_injective
  apply LinearMap.ext
  intro v
  change linearAction (g.val ^ 2) v = v
  rw [pow_two, map_mul]
  change linearAction g.val (linearAction g.val v) = v
  have hs := congrArg (linearAction g.val) (kernel_displacement g hg v)
  rw [map_sub, map_smul, linearAction_point, ← kernel_displacement g hg v] at hs
  calc
    _ = (linearAction g.val v - v) + linearAction g.val v := sub_eq_iff_eq_add.mp hs
    _ = (linearAction g.val v + linearAction g.val v) - v := by abel
    _ = v := by
      rw [ZModModule.add_self, zero_sub]
      exact neg_eq_iff_add_eq_zero.mpr (ZModModule.add_self v)

/-- A faithful binary four-dimensional A₇ action has faithful marked quotient action:
its involutions cannot have displacement contained in the marked line. -/
public theorem pointStabilizerQuotientAction_injective_of_alternating
    (e : joined ≃* alternatingGroup (Fin 7)) :
    Function.Injective pointStabilizerQuotientAction := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro g hg
  change pointStabilizerQuotientAction g = 1 at hg
  change g = 1
  by_contra hne
  have hne' : g.val ≠ 1 := fun h => hne (Subtype.ext h)
  let ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V :=
    linearAction.comp e.symm.toMonoidHom
  have hinj : Function.Injective ρ := linearAction_injective.comp e.symm.injective
  have ht : orderOf (e g.val) = 2 := orderOf_eq_prime
    (by rw [← map_pow, kernel_square g hg, map_one])
    (fun h => hne' (e.injective (h.trans e.map_one.symm)))
  have hrank := Representation.AlternatingSevenConjugatePair.Model.involution_fixedCodim
    ρ hinj (by simp [V]) (e g.val) ht
  rw [fixedCodim_zpowers_eq_displacement_rank] at hrank
  have haction : ρ (e g.val) = linearAction g.val := by
    change linearAction (e.symm (e g.val)) = _
    rw [e.symm_apply_apply]
  rw [haction] at hrank
  have hle : LinearMap.range (linearAction g.val - LinearMap.id) ≤
      Submodule.span (ZMod 2) {point.toAdd} := by
    rintro _ ⟨v, rfl⟩
    change linearAction g.val v - v ∈ _
    rw [kernel_displacement g hg v]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  have hdim := Submodule.finrank_mono hle
  rw [hrank, finrank_span_singleton (show point.toAdd ≠ 0 from point_ne_one)] at hdim
  omega

private def quotientLinearModel :
    ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃* Matrix.PSL3Two.PSL :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → ZMod 2)).symm.trans
    (Matrix.GeneralLinearGroup.toLin.symm.trans
      (Matrix.PSL3Two.equivGL.symm.trans Matrix.PSL3Two.equiv))

/-- The marked stabilizer is PSL₃(2), through its actual action on the quotient by the
marked line. The sole additional premise is the identification of the joined group with A₇. -/
public def pointStabilizerEquivOfAlternating (e : joined ≃* alternatingGroup (Fin 7)) :
    MulAction.stabilizer joined point ≃* Matrix.PSL3Two.PSL := by
  letI : Finite ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :=
    Finite.of_equiv Matrix.PSL3Two.PSL quotientLinearModel.toEquiv.symm
  exact (MulEquiv.ofBijective pointStabilizerQuotientAction
    ((pointStabilizerQuotientAction_injective_of_alternating e).bijective_of_nat_card_le (by
      rw [Nat.card_congr quotientLinearModel.toEquiv, Matrix.PSL3Two.card_PSL,
        pointStabilizer_card_of_alternating e]))).trans quotientLinearModel

end
end BinaryFourSplitPair
