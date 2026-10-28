module
public import Theory.Representation.BinaryTransvectionGroups.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Characters of a full binary transvection group

The displacement of a transvection along a fixed nonzero central vector
has a unique scalar coefficient. It vanishes on the center and therefore
descends to the literal quotient. Multiplication adds these characters,
and every quotient character comes from its rank-one transvection.

This supplies the full pairing used by the original fixed-coset argument
in Aschbacher--Smith 8.2.12, printed p.722.
-/

@[expose] public noncomputable section
namespace BinaryTransvectionGroups
open BinaryLinear
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (z : V) (hz : z ≠ 0)

/-- Scalar displacement along a prescribed nonzero fixed line. -/
def lineCoefficient (t : radical (centerLine z)) : V →ₗ[ZMod 2] ZMod 2 :=
  (LinearEquiv.coord (ZMod 2) V z hz).toLinearMap.comp
    ((t.val.toLinearMap - LinearMap.id).codRestrict (centerLine z) t.property.2)

theorem lineCoefficient_smul (t : radical (centerLine z)) (v : V) :
    lineCoefficient z hz t v • z = t.val v - v :=
  LinearEquiv.coord_apply_smul (ZMod 2) V z hz _

theorem lineCoefficient_vanishes (t : radical (centerLine z)) :
    centerLine z ≤ (lineCoefficient z hz t).ker := by
  intro v hv
  apply (smul_left_injective (ZMod 2) hz)
  dsimp only
  rw [zero_smul,lineCoefficient_smul,t.property.1 v hv,sub_self]

/-- A transvection acts by a linear character of the literal quotient by its center. -/
def lineCharacter (t : radical (centerLine z)) :
    Module.Dual (ZMod 2) (V ⧸ centerLine z) :=
  (centerLine z).liftQ (lineCoefficient z hz t) (lineCoefficient_vanishes z hz t)

@[simp] theorem lineCharacter_mk (t : radical (centerLine z)) (v : V) :
    lineCharacter z hz t ((centerLine z).mkQ v) = lineCoefficient z hz t v := rfl

theorem lineCharacter_smul (t : radical (centerLine z)) (v : V) :
    lineCharacter z hz t ((centerLine z).mkQ v) • z = t.val v - v :=
  lineCoefficient_smul z hz t v

/-- Multiplication of transvections adds their central displacement characters. -/
def lineCharacterHom : radical (centerLine z) →*
    Multiplicative (Module.Dual (ZMod 2) (V ⧸ centerLine z)) where
  toFun t := Multiplicative.ofAdd (lineCharacter z hz t)
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with | _ v =>
    apply (smul_left_injective (ZMod 2) hz)
    dsimp only
    change lineCharacter z hz 1 ((centerLine z).mkQ v) • z = (0 : ZMod 2) • z
    rw [lineCharacter_smul,zero_smul]
    exact sub_self v
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with | _ v =>
    change lineCharacter z hz (a*b) ((centerLine z).mkQ v) =
      lineCharacter z hz a ((centerLine z).mkQ v) + lineCharacter z hz b ((centerLine z).mkQ v)
    apply (smul_left_injective (ZMod 2) hz)
    dsimp only
    rw [add_smul,lineCharacter_smul,lineCharacter_smul,lineCharacter_smul]
    have hd := a.property.1 (b.val v - v) (b.property.2 v)
    rw [map_sub] at hd
    change a.val (b.val v) - v = (a.val v-v)+(b.val v-v)
    rw [← hd]
    abel

theorem lineCharacterHom_injective : Function.Injective (lineCharacterHom z hz) := by
  intro a b hab
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have he := congrArg (fun t => t.toAdd ((centerLine z).mkQ v)) hab
  have hs := congrArg (fun c : ZMod 2 => c • z) he
  change lineCharacter z hz a ((centerLine z).mkQ v) • z =
    lineCharacter z hz b ((centerLine z).mkQ v) • z at hs
  rw [lineCharacter_smul,lineCharacter_smul] at hs
  exact sub_left_inj.mp hs

theorem lineCharacterHom_surjective : Function.Surjective (lineCharacterHom z hz) := by
  intro a
  let f := a.toAdd.comp (centerLine z).mkQ
  have hf : centerLine z ≤ f.ker := by
    intro v hv
    change a.toAdd ((centerLine z).mkQ v) = 0
    have hzero : (centerLine z).mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hv
    rw [hzero, map_zero]
  let t : radical (centerLine z) :=
    ⟨transvection z f (hf (Submodule.mem_span_singleton_self z)),
      transvection_mem (Submodule.mem_span_singleton_self z) hf⟩
  refine ⟨t,?_⟩
  apply Multiplicative.toAdd.injective
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with | _ v =>
  apply (smul_left_injective (ZMod 2) hz)
  dsimp only
  change lineCharacter z hz t ((centerLine z).mkQ v) • z = _
  rw [lineCharacter_smul]
  change (v + f v • z) - v = f v • z
  abel

end BinaryTransvectionGroups
