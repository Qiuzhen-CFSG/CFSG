module

public import Theory.Representation.EndFieldRep
public import Theory.Representation.PGroupScalarWitness
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.LinearAlgebra.SpecialLinearGroup
import Mathlib.Tactic

/-!
# Four scalars for a binary representation with central subgroup of order three

A faithful irreducible binary representation has a finite Schur endomorphism
field. A central element of order three acts as a scalar in this field; its
minimal polynomial over F₂ is quadratic. The field it generates therefore has
four elements. In binary dimension six the original vector space has dimension
three over this field, and perfectness makes its determinant character trivial.

This constructs the scalar-field and special-linear embedding steps in
Aschbacher–Smith, *The Classification of Quasithin Groups*, G.7.3,
printed p.349 (PDF p.360, combined 1 March 2004 manuscript).
-/

public section

namespace CFSG.Quasithin.ChapterG.Section07.AlternatingSevenCover

open scoped MonoidAlgebra
open IntermediateField Polynomial

private theorem cubic_field_degree {E : Type*} [Field E] [Finite E] [Algebra (ZMod 2) E]
    (a : E) (ha : orderOf a = 3) :
    Module.finrank (ZMod 2) ((IntermediateField.adjoin (ZMod 2) {a})) = 2 := by
  let : Module.Finite (ZMod 2) E := Module.Finite.of_finite
  have ha1 : a ≠ 1 := by intro h; simp [h] at ha
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hap : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one _
  have hroot : a ^ 2 + a + 1 = 0 := by
    apply (mul_eq_zero.mp (show (a - 1) * (a ^ 2 + a + 1) = 0 from by
      calc _ = a ^ 3 - 1 := by ring
           _ = 0 := by rw [hap, sub_self])).resolve_left
    exact sub_ne_zero.mpr ha1
  have hd : Module.finrank (ZMod 2) (adjoin (ZMod 2) {a}) ≤ 2 := by
    rw [IntermediateField.adjoin.finrank (IsIntegral.of_finite (ZMod 2) a)]
    have hp : (X ^ 2 + X + 1 : (ZMod 2)[X]) ≠ 0 := by
      intro h
      have := congrArg (fun p : (ZMod 2)[X] => p.coeff 2) h
      norm_num [Polynomial.coeff_X, Polynomial.coeff_one] at this
    calc
      _ ≤ (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree :=
        natDegree_le_of_dvd (minpoly.dvd (ZMod 2) a (by simpa using hroot)) hp
      _ ≤ 2 := by compute_degree
  have hn : Module.finrank (ZMod 2) (adjoin (ZMod 2) {a}) ≠ 1 := by
    intro h
    obtain ⟨x, hx⟩ := (IntermediateField.mem_bot).mp
      (IntermediateField.finrank_adjoin_simple_eq_one_iff.mp h)
    fin_cases x
    · change (algebraMap (ZMod 2) E) 0 = a at hx
      exact ha0 (by simpa only [map_zero] using hx.symm)
    · change (algebraMap (ZMod 2) E) 1 = a at hx
      exact ha1 (by simpa only [map_one] using hx.symm)
  have hp := Module.finrank_pos (R := ZMod 2) (M := adjoin (ZMod 2) {a})
  omega


universe u v
variable {L : Type u} {V : Type v} [Group L] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A compatible field of four scalars on the original binary vector space,
with the same group action and scalar dimension three. -/
structure FourFieldRealization (rho : Representation (ZMod 2) L V) where
  Scalar : Type v
  [field : Field Scalar]
  [algebra : Algebra (ZMod 2) Scalar]
  [module : Module Scalar V]
  [scalarTower : IsScalarTower (ZMod 2) Scalar V]
  card : Nat.card Scalar = 4
  action : Representation Scalar L V
  agrees : ∀ (g : L) (v : V), action g v = rho g v
  dimension : Module.finrank Scalar V = 3

/-- A central element of order three generates a quadratic subfield of the
Schur endomorphism field. Restricting scalars to it realizes the same action
in dimension three over a field of order four. -/
theorem exists_four_field_realization (rho : Representation (ZMod 2) L V) [rho.IsIrreducible]
    (hfaith : Function.Injective rho) (hz : Nat.card (Subgroup.center L) = 3)
    (hdim : Module.finrank (ZMod 2) V = 6) : Nonempty (FourFieldRealization rho) := by
  let E := Module.End (ZMod 2)[L] rho.asModule
  let : Finite V := Module.finite_iff_finite.mp (inferInstance : Module.Finite (ZMod 2) V)
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial rho
  let : Finite rho.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) rho.asModule)
  let : Nontrivial rho.asModule := rho.asModuleEquiv.nontrivial
  let : Module.Finite E rho.asModule := Module.Finite.of_finite
  let : Representation.IsAbsolutelyIrreducible rho.endFieldRep :=
    Representation.endFieldRep_isAbsolutelyIrreducible rho
  have hendfaith : Function.Injective rho.endFieldRep := by
    intro x y hxy
    apply hfaith
    ext v
    exact congrArg (fun f => rho.asModuleEquiv (f (rho.asModuleEquiv.symm v))) hxy
  let : Finite (Subgroup.center L) := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨z, hzorder⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center L) 3 (by rw [hz])
  obtain ⟨a, ha⟩ := Representation.exists_scalar_of_mem_center_of_absolutelyIrreducible
    rho.endFieldRep (z : L) z.property
  have hscalar : (algebraMap E (Module.End E rho.asModule)) a = rho.endFieldRep z := ha.symm
  have haorder : orderOf a = 3 := by
    calc
      orderOf a = orderOf ((algebraMap E (Module.End E rho.asModule)) a) :=
        (orderOf_injective (algebraMap E (Module.End E rho.asModule)).toMonoidHom
          (algebraMap E (Module.End E rho.asModule)).injective a).symm
      _ = orderOf (rho.endFieldRep z) := by rw [hscalar]
      _ = orderOf (z : L) := orderOf_injective _ hendfaith _
      _ = orderOf z := orderOf_injective (Subgroup.center L).subtype Subtype.val_injective z
      _ = 3 := hzorder
  let K := adjoin (ZMod 2) {a}
  let : Module E V := Representation.endFieldModule rho
  let : Module K V := inferInstance
  let : IsScalarTower (ZMod 2) K V := inferInstance
  have hKdim : Module.finrank (ZMod 2) K = 2 := cubic_field_degree a haorder
  have hKcard : Nat.card K = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hKdim]
    norm_num
  let sigma : Representation K L V := {
    toFun g := (rho.endFieldRep g).restrictScalars K
    map_one' := by ext v; change rho.endFieldRep 1 v = v; rw [map_one]; rfl
    map_mul' g h := by ext v; exact congrArg (fun f => f v) (rho.endFieldRep.map_mul g h) }
  refine ⟨{ Scalar := K, card := hKcard, action := sigma, agrees := ?_, dimension := ?_ }⟩
  · intro g v
    rfl
  · have hmul := Module.finrank_mul_finrank (ZMod 2) K V
    rw [hKdim, hdim] at hmul
    omega

attribute [instance] FourFieldRealization.field FourFieldRealization.algebra
  FourFieldRealization.module FourFieldRealization.scalarTower

omit [FiniteDimensional (ZMod 2) V] in
/-- The action over four scalars preserves faithfulness. -/
theorem FourFieldRealization.faithful {rho : Representation (ZMod 2) L V}
    (S : FourFieldRealization rho) (hfaith : Function.Injective rho) :
    Function.Injective S.action := by
  intro x y hxy
  apply hfaith
  ext v
  rw [← S.agrees x v, ← S.agrees y v]
  exact congrArg (fun f => f v) hxy

/-- Perfectness kills the determinant character of the three-dimensional
action, producing an actual faithful special-linear representation. -/
theorem FourFieldRealization.embeds_sl3 {rho : Representation (ZMod 2) L V}
    [Group.IsPerfect L] (S : FourFieldRealization rho) (hfaith : Function.Injective rho) :
    ∃ j : L →* Matrix.SpecialLinearGroup (Fin 3) S.Scalar, Function.Injective j := by
  let : Finite V := Module.finite_iff_finite.mp (inferInstance : Module.Finite (ZMod 2) V)
  let : Module.Finite S.Scalar V := Module.Finite.of_finite
  let f : L →* (V ≃ₗ[S.Scalar] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv S.Scalar V).toMonoidHom.comp
      S.action.asGroupHom
  have hf : Function.Injective f := by
    intro x y hxy
    apply S.faithful hfaith
    ext v
    exact congrArg (fun t : V ≃ₗ[S.Scalar] V => t v) hxy
  have hdet (g : L) : (f g).det = 1 :=
    Abelianization.commutator_subset_ker (LinearEquiv.det.comp f)
      (Group.IsPerfect.mem_commutator (g := g))
  let fSL : L →* _root_.SpecialLinearGroup S.Scalar V := {
    toFun g := ⟨f g, hdet g⟩
    map_one' := Subtype.ext (f.map_one)
    map_mul' x y := Subtype.ext (f.map_mul x y) }
  have hfSL : Function.Injective fSL := fun x y h => hf (congrArg Subtype.val h)
  let b : Module.Basis (Fin 3) S.Scalar V := by
    simpa only [S.dimension] using Module.finBasis S.Scalar V
  exact ⟨(Matrix.SpecialLinearGroup.toLin_equiv b).symm.toMonoidHom.comp fSL,
    (Matrix.SpecialLinearGroup.toLin_equiv b).symm.injective.comp hfSL⟩

end CFSG.Quasithin.ChapterG.Section07.AlternatingSevenCover
