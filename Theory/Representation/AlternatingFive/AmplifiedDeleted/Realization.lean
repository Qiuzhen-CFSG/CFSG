module

public import Theory.Representation.AlternatingFive.AmplifiedDeleted.Bounds

/-!
# Literal homogeneous coordinates for amplified deleted modules

An equivariant binary coordinate map transfers the arbitrary-mixing estimates
to an actual homogeneous support module. The acting operator need only induce
the stated conjugation on its A₅ factor; it need not preserve any displayed
simple summand. These are the displacement inputs for the separated-support
multiplicity argument of Aschbacher--Smith D.3.9 and D.3.21.
-/

@[expose] public noncomputable section

namespace Representation.AlternatingFive.AmplifiedDeleted
open BinaryOffender.NaturalTensor
variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Coordinates intertwine the literal A₅ factor action. -/
structure Coordinates (ρ : Representation (ZMod 2) Alt V) where
  equiv : V ≃ₗ[ZMod 2] (ι → C)
  intertwines : ∀ g v, equiv (ρ g v) = deletedSumAction ι g.val (equiv v)

variable {ρ : Representation (ZMod 2) Alt V}

omit [Fintype ι] [FiniteDimensional (ZMod 2) V] in
/-- The conjugated actor has precisely the original permutation twist. -/
theorem Coordinates.conjugate_intertwines (e : Coordinates (ι := ι) ρ)
    (T : Module.End (ZMod 2) V) (p : Sym)
    (hT : ∀ g v, T (ρ g v) = ρ (MulAut.conjNormal p g) (T v)) :
    ∀ (g : Alt) v, e.equiv.conj T (deletedSumAction ι g.val v) =
      deletedSumAction ι (p * g.val * p⁻¹) (e.equiv.conj T v) := by
  intro g v
  simp only [LinearEquiv.conj_apply_apply]
  have hh : e.equiv.symm (deletedSumAction ι g.val v) = ρ g (e.equiv.symm v) := by
    apply e.equiv.injective
    simp [e.intertwines]
  rw [hh, hT, e.intertwines]
  rfl

/-- Nonidentity involutory projection on the marked A₅ factor moves at least
one dimension per deleted copy. -/
theorem Coordinates.nontrivial_bound (e : Coordinates (ι := ι) ρ)
    (T : Module.End (ZMod 2) V) (p : Sym) (hp : p * p = 1) (hne : p ≠ 1)
    (hT : ∀ g v, T (ρ g v) = ρ (MulAut.conjNormal p g) (T v)) :
    Fintype.card ι ≤ operatorFixedCodim T := by
  have hb := nontrivial_involution_bound (e.equiv.conj T) p hp hne
    (e.conjugate_intertwines T p hT)
  have he := operatorFixedCodim_eq_of_equiv T (e.equiv.conj T) e.equiv (by simp)
  exact he ▸ hb

/-- An even nonidentity involutory projection moves at least two dimensions
per deleted copy in the actual support module. -/
theorem Coordinates.inner_bound (e : Coordinates (ι := ι) ρ)
    (T : Module.End (ZMod 2) V) (p : Sym) (hp : p * p = 1) (hne : p ≠ 1)
    (heven : p ∈ alternatingGroup (Fin 5))
    (hT : ∀ g v, T (ρ g v) = ρ (MulAut.conjNormal p g) (T v)) :
    2 * Fintype.card ι ≤ operatorFixedCodim T := by
  let a : Alt := ⟨p, heven⟩
  have ha : a * a = 1 := Subtype.ext hp
  have hane : a ≠ 1 := fun h => hne (congrArg Subtype.val h)
  have hb := inner_involution_bound (e.equiv.conj T) a ha hane
    (e.conjugate_intertwines T p hT)
  have he := operatorFixedCodim_eq_of_equiv T (e.equiv.conj T) e.equiv (by simp)
  exact he ▸ hb

end Representation.AlternatingFive.AmplifiedDeleted
