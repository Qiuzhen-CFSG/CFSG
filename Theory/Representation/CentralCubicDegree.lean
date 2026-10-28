module

public import Theory.Representation.EndFieldRep
public import Theory.Representation.FiveCycleDegreeThree
public import Theory.Representation.ExtendScalars
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.CharP.Algebra

/-!
# Binary degree bounds from a cubic center and a five-cycle automizer

For a faithful irreducible binary representation, Schur and Wedderburn give
an actual finite endomorphism field. A center of order three embeds in this
field, making its degree over F₂ at least two. Perfectness makes the
representation's determinant trivial, so the field dimension is divisible
by three. An order-five element conjugated to its square excludes field
dimensions at most three by the action on character weights. The field
dimension is therefore at least six, and the binary dimension at least twelve.

The argument uses neither absolute irreducibility nor a character catalogue.
The scalar action is the existing `endFieldRep`, on the original module's
`asModule` carrier, and its dimension is related by the actual scalar tower.

Source: the weight argument of Aschbacher–Smith A.3.21(c), printed pp.55–56;
application to the triple cover of A₇ in B.1.13, pp.73–74, and K.1, p.452.
-/

public section

open scoped MonoidAlgebra TensorProduct
open Subgroup
namespace Representation.CentralCubicDegree

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private noncomputable def centerAction : center G →* Module.End (ZMod 2)[G] ρ.asModule :=
  (IntertwiningMap.equivAlgEnd ρ).toMonoidHom.comp
    { toFun := fun z => IntertwiningMap.centralMul ρ z z.property
      map_one' := by
        apply IntertwiningMap.toLinearMap_injective ρ ρ
        exact ρ.map_one
      map_mul' := by
        intro z t
        apply IntertwiningMap.toLinearMap_injective ρ ρ
        exact ρ.map_mul z t }

private theorem centerAction_injective (hf : Function.Injective ρ) :
    Function.Injective (centerAction ρ) := by
  intro z t h
  apply Subtype.ext
  apply hf
  ext v
  exact LinearMap.congr_fun h (ρ.asModuleEquiv.symm v)

private theorem endFieldRep_injective (hf : Function.Injective ρ) :
    Function.Injective ρ.endFieldRep := by
  intro g h he
  apply hf
  ext v
  exact congrArg ρ.asModuleEquiv (LinearMap.congr_fun he (ρ.asModuleEquiv.symm v))

private theorem centerAction_scalar (z : center G) [FiniteDimensional (ZMod 2) V]
    [IsIrreducible ρ] :
    ρ.endFieldRep z = centerAction ρ z •
      (1 : Module.End (Module.End (ZMod 2)[G] ρ.asModule) ρ.asModule) := by
  ext v
  rfl

/-- A cubic center, perfectness and an order-five squaring automizer force
faithful irreducible binary degree at least twelve. -/
theorem finrank_ge_twelve [FiniteDimensional (ZMod 2) V] [IsIrreducible ρ]
    [Group.IsPerfect G] (hf : Function.Injective ρ)
    (hc : Nat.card (center G) = 3)
    (x y : G) (hx : orderOf x = 5) (hxy : y * x * y⁻¹ = x ^ 2) :
    12 ≤ Module.finrank (ZMod 2) V := by
  let E := Module.End (ZMod 2)[G] ρ.asModule
  let : Finite ρ.asModule := Module.finite_of_finite (ZMod 2)
  let : FiniteDimensional E ρ.asModule := Module.Finite.of_finite
  let : FiniteDimensional (ZMod 2) E := Module.Finite.of_finite
  let : CharP E 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  have he : 2 ≤ Module.finrank (ZMod 2) E := by
    have hcard := Nat.card_le_card_of_injective _ (centerAction_injective ρ hf)
    rw [hc, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hcard
    by_contra h
    have hh : Module.finrank (ZMod 2) E ≤ 1 := by omega
    interval_cases hd : Module.finrank (ZMod 2) E <;> simp_all
  have hd : 4 ≤ Module.finrank E ρ.asModule := by
    by_contra h
    let L := AlgebraicClosure E
    have hdim : Module.finrank L (L ⊗[E] ρ.asModule) ≤ 3 := by
      rw [Module.finrank_baseChange]
      omega
    have hfive : (5 : L) ≠ 0 := by
      apply CharP.cast_ne_zero_of_ne_of_prime L (by decide : Nat.Prime 5)
        (by decide : 2 ≠ 5)
    exact FiveCycleDegreeThree.not_conjugate_square
      (ρ.endFieldRep.extendScalars L)
      ((extendScalars_faithful_iff L ρ.endFieldRep).mp (endFieldRep_injective ρ hf))
      hfive hdim x y hx hxy
  let : Finite (center G) := Finite.of_injective _ (centerAction_injective ρ hf)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center G) 3 (by rw [hc])
  have hzE : orderOf (centerAction ρ z) = 3 :=
    (orderOf_injective (centerAction ρ) (centerAction_injective ρ hf) z).trans hz
  have hdet : LinearMap.det (ρ.endFieldRep z) = 1 := by
    let f : G →* Eˣ := MonoidHom.toHomUnits (LinearMap.det.comp ρ.endFieldRep)
    let : Group.IsPerfect f.range := Group.IsPerfect.range f
    have h : (⟨f z, ⟨z, rfl⟩⟩ : f.range) = 1 := Subsingleton.elim _ _
    exact congrArg (fun a : f.range => (a.val : E)) h
  rw [centerAction_scalar, LinearMap.det_smul, map_one, mul_one] at hdet
  have hdiv : 3 ∣ Module.finrank E ρ.asModule := by
    simpa only [hzE] using orderOf_dvd_of_pow_eq_one hdet
  have hd6 : 6 ≤ Module.finrank E ρ.asModule := by omega
  have ht := Module.finrank_mul_finrank (ZMod 2) E ρ.asModule
  rw [ρ.asModuleEquiv.finrank_eq] at ht
  exact ht ▸ Nat.mul_le_mul he hd6

end Representation.CentralCubicDegree
