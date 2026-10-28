module

public import Theory.Representation.BinaryPrimeDegree
public import Theory.Representation.EndFieldRep
public import Mathlib.GroupTheory.IsPerfect

/-!
# Central prime divisors force binary degree bounds

For a faithful irreducible binary representation of a finite perfect group,
a central element of prime order p acts as a scalar over the Schur endomorphism
field E. Faithfulness puts an element of order p in E, so [E:F₂] is at least
the multiplicative order of 2 modulo p. Perfectness makes the determinant one,
forcing p to divide the positive dimension over E. Multiplying these two
bounds gives the binary bound p * orderOf (2 : ZMod p).

This extends the cubic-center argument in `CentralCubicDegree` to arbitrary
odd primes. Its concrete application excludes central eleven-torsion in the
small J₄ modules considered in Aschbacher–Smith K.4, printed p.457.
-/

public section
open Subgroup Representation
open scoped MonoidAlgebra

namespace Representation.BinaryCoprimeDegree
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

/-- A central prime divisor in a perfect group forces the prime times its
binary multiplicative order as a lower bound on a faithful irreducible degree. -/
theorem perfect_central_prime_degree [Finite G]
    [FiniteDimensional (ZMod 2) V] [IsIrreducible ρ] [Group.IsPerfect G]
    (hf : Function.Injective ρ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hc : p ∣ Nat.card (center G)) :
    p * orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V := by
  let E := Module.End (ZMod 2)[G] ρ.asModule
  let : Finite ρ.asModule := Module.finite_of_finite (ZMod 2)
  let : FiniteDimensional E ρ.asModule := Module.Finite.of_finite
  let : FiniteDimensional (ZMod 2) E := Module.Finite.of_finite
  let τ : Representation (ZMod 2) (center G) E :=
    (Algebra.lmul (ZMod 2) E).toMonoidHom.comp (centerAction ρ)
  have hτ : Function.Injective τ :=
    Algebra.lmul_injective.comp (centerAction_injective ρ hf)
  have he := BinaryPrimeDegree.orderOf_le_finrank τ hτ hp hp2 hc
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center G) p hc
  have hzE : orderOf (centerAction ρ z) = p :=
    (orderOf_injective (centerAction ρ) (centerAction_injective ρ hf) z).trans hz
  have hscalar : ρ.endFieldRep z = centerAction ρ z • (1 : Module.End E ρ.asModule) := by
    ext v
    rfl
  have hdet : LinearMap.det (ρ.endFieldRep z) = 1 := by
    let f : G →* Eˣ := MonoidHom.toHomUnits (LinearMap.det.comp ρ.endFieldRep)
    let : Group.IsPerfect f.range := Group.IsPerfect.range f
    have h : (⟨f z, ⟨z, rfl⟩⟩ : f.range) = 1 := Subsingleton.elim _ _
    exact congrArg (fun a : f.range => (a.val : E)) h
  rw [hscalar, LinearMap.det_smul, map_one, mul_one] at hdet
  have hdiv : p ∣ Module.finrank E ρ.asModule := by
    simpa only [hzE] using orderOf_dvd_of_pow_eq_one hdet
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  let : Nontrivial ρ.asModule :=
    ρ.asModuleEquiv.toEquiv.nontrivial
  have hpos : 0 < Module.finrank E ρ.asModule := Module.finrank_pos
  have hd : p ≤ Module.finrank E ρ.asModule := Nat.le_of_dvd hpos hdiv
  have ht := Module.finrank_mul_finrank (ZMod 2) E ρ.asModule
  rw [ρ.asModuleEquiv.finrank_eq] at ht
  calc
    p * orderOf (2 : ZMod p) = orderOf (2 : ZMod p) * p := Nat.mul_comm _ _
    _ ≤ Module.finrank (ZMod 2) E * Module.finrank E ρ.asModule := Nat.mul_le_mul he hd
    _ = Module.finrank (ZMod 2) V := ht
end Representation.BinaryCoprimeDegree
