module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.Models
public import Theory.Representation.FactorDegreeFiltration

/-!
# The actual point-submodule inclusion induces a quotient

An intertwiner from the binary adjoint module to a restricted M22 module
extends to induction by [g ⊗ a] ↦ σ(g⁻¹)f(a). Evaluation at [1 ⊗ a]
recovers the original map. Consequently an adjoint point submodule of an
irreducible M22 module gives a nonzero, hence surjective, induced-module map.

The final consumer uses a concrete simple-factor filtration of the induced
module. Construction of that filtration and binary descent of the local
identification are separate premises, not asserted here. No splitting of
the point restriction is used.

Source context: Guralnick–Malle I, Proposition 5.1, pp.15–16. The induction
formula is Mathlib's Frobenius reciprocity, written without the bundled
category's common-universe restriction on its two carriers.
-/

@[expose] public noncomputable section
open Representation Sporadic.Mathieu Finsupp
open scoped MonoidAlgebra TensorProduct
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Frobenius reciprocity on the literal native point map. -/
def inducedMap (σ : Representation (ZMod 2) M22 V)
    (f : adjointBinary.IntertwiningMap (σ.comp pointSLMap)) :
    inducedAdjoint.IntertwiningMap σ :=
  ⟨Representation.Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift _ _ _ fun h => σ h⁻¹ ∘ₗ f.toLinearMap) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).toLinearMap)
    (fun g => by
      ext h x
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply]
      simp [ofMulAction_single, mul_inv_rev, IntertwiningMap.isIntertwining]),
    fun g => by ext; simp [inducedAdjoint]⟩

/-- Evaluation at the identity coset recovers the original inclusion. -/
theorem inducedMap_mk_one (σ : Representation (ZMod 2) M22 V)
    (f : adjointBinary.IntertwiningMap (σ.comp pointSLMap)) (a : Adjoint) :
    inducedMap σ f (IndV.mk pointSLMap adjointBinary 1 a) = f a := by
  simp [inducedMap]

/-- An actual adjoint point submodule gives a nonzero map from induction. -/
theorem exists_inducedMap_of_point_equiv (σ : Representation (ZMod 2) M22 V)
    (S : Subrepresentation (pointRestriction σ))
    (e : Representation.Equiv (S.toRepresentation.comp pointSL) adjointBinary) :
    ∃ p : inducedAdjoint.IntertwiningMap σ, p ≠ 0 := by
  let j : Representation.IntertwiningMap (S.toRepresentation.comp pointSL) (σ.comp pointSLMap) :=
    ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  let f := j.comp e.symm.toIntertwiningMap
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.toLinearEquiv.injective
  let : Nontrivial Adjoint := Module.nontrivial_of_finrank_pos
    (show 0 < Module.finrank (ZMod 2) Adjoint by rw [finrank_adjoint]; decide)
  obtain ⟨a, ha⟩ := exists_ne (0 : Adjoint)
  refine ⟨inducedMap σ f, ?_⟩
  intro hz
  have h : f a = 0 := by
    rw [← inducedMap_mk_one σ f a, hz]
    rfl
  exact ha (hf (h.trans (map_zero f).symm))

/-- Irreducibility promotes the constructed nonzero map to a genuine quotient. -/
theorem exists_induced_quotient_of_point_equiv (σ : Representation (ZMod 2) M22 V)
    [σ.IsIrreducible] (S : Subrepresentation (pointRestriction σ))
    (e : Representation.Equiv (S.toRepresentation.comp pointSL) adjointBinary) :
    ∃ p : inducedAdjoint.IntertwiningMap σ, Function.Surjective p := by
  obtain ⟨p, hp⟩ := exists_inducedMap_of_point_equiv σ S e
  exact ⟨p, (IsIrreducible.surjective_or_eq_zero p).resolve_right hp⟩

/-- The two concrete remaining inputs exclude the sixteen-dimensional branch.
Neither the local binary identification nor the induced filtration is assumed
to follow merely from its name or degree. -/
theorem impossible_of_equiv_of_filtration [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) M22 V) [σ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 30)
    (S : Subrepresentation (pointRestriction σ))
    (hS : Module.finrank (ZMod 2) S.toSubmodule = 16)
    (e : Representation.Equiv (S.toRepresentation.comp pointSL) adjointBinary)
    (hfiltration : FactorDegreeFiltration {d : ℕ | d ≤ 10 ∨ 30 < d} inducedAdjoint) :
    False := by
  obtain ⟨p, hp⟩ := exists_inducedMap_of_point_equiv σ S e
  have hdegree := hfiltration.finrank_mem p hp
  have hlo := Submodule.finrank_le S.toSubmodule
  rw [hS] at hlo
  change Module.finrank (ZMod 2) V ≤ 10 ∨ 30 < Module.finrank (ZMod 2) V at hdegree
  omega

end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule
