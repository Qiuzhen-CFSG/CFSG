module
public import Theory.Representation.AlternatingFive.AmplifiedNatural.Bounds
public import Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms

/-!
# Natural coordinates with the literal symmetric-five automorphism

A chosen A₅ ≃ SL₂(F₄) marking transports the automorphism induced by an actual
permutation to the matrix group. Faithfulness of S₅ → Aut(A₅) preserves
nontriviality, and the same marking transports the intertwining identity.
The amplified natural bound allows all mixing of equal simple summands.
-/

public noncomputable section
namespace Representation.AlternatingFive.AmplifiedNatural
open BinaryOffender.NaturalTensor
open Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms
variable (F : Type*) [Field F] [Algebra (ZMod 2) F] [CharP F 2] [Finite F]
variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The chosen marking and coordinates retain the original factor action. -/
structure Coordinates (ρ : Representation (ZMod 2) Alt V) where
  marking : Alt ≃* Matrix.SpecialLinearGroup (Fin 2) F
  equiv : V ≃ₗ[ZMod 2] (ι → NaturalSpace F)
  intertwines : ∀ g v, equiv (ρ g v) = naturalSumAction F ι (marking g) (equiv v)

variable {F} {ρ : Representation (ZMod 2) Alt V}

/-- Every nontrivial involutory symmetric-five projection moves at least two
binary dimensions per copy, for the actual chosen natural coordinates. -/
theorem Coordinates.nontrivial_bound (hF : Nat.card F = 4)
    (e : Coordinates F (ι := ι) ρ)
    (T : Module.End (ZMod 2) V) (hTi : Function.Injective T)
    (p : Sym) (hp : p * p = 1) (hne : p ≠ 1)
    (hT : ∀ g v, T (ρ g v) = ρ (MulAut.conjNormal p g) (T v)) :
    2 * Fintype.card ι ≤ operatorFixedCodim T := by
  let f := (MulAut.congr e.marking).toMonoidHom.comp factorEquiv.toMonoidHom
  have hf : Function.Injective f := (MulAut.congr e.marking).injective.comp factorEquiv.injective
  have hfp : f p * f p = 1 := by rw [← map_mul, hp, map_one]
  have hfn : f p ≠ 1 := by
    intro hh
    exact hne (hf (hh.trans (map_one f).symm))
  have hb := automorphism_involution_bound F (n := 2) hF
    (ρ.comp e.marking.symm.toMonoidHom) e.equiv
    (by
      intro g v
      change e.equiv (ρ (e.marking.symm g) v) = naturalSumAction F ι g (e.equiv v)
      simpa only [e.marking.apply_symm_apply] using e.intertwines (e.marking.symm g) v)
    T hTi (f p) hfp hfn (by
      intro g v
      change T (ρ (e.marking.symm g) v) =
        ρ (e.marking.symm (f p g)) (T v)
      have hg : e.marking.symm (f p g) =
          MulAut.conjNormal p (e.marking.symm g) := by
        change e.marking.symm (e.marking (factorEquiv p (e.marking.symm g))) = _
        rw [e.marking.symm_apply_apply]
        rfl
      rw [hg]
      exact hT _ v)
  simpa only [Nat.mul_comm _ 2] using hb

end Representation.AlternatingFive.AmplifiedNatural
