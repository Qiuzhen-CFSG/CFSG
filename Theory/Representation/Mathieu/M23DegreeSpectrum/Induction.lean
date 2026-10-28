module

public import Theory.Representation.Mathieu.M23DegreeSpectrum.Models

/-!
# From an actual point-submodule inclusion to an M23 quotient

Inverse Frobenius reciprocity extends an intertwiner from a point module
into the restriction. Its value on the identity tensor is the original
map, so an inclusion gives a nonzero map. Irreducibility of the M23 target
makes that induced map surjective. The direct coinvariant construction
handles arbitrary target universes and uses no splitting assumption.

The construction adapts Mathlib's `Rep.indResHomEquiv` (Apache 2.0), and is
the comparison step for Guralnick–Malle I, Proposition 5.1, M23 paragraph, manuscript p.16.
-/

public noncomputable section
open Representation Sporadic.Mathieu
namespace Representation.MathieuSmall.M23DegreeSpectrum

/-- Restriction to the actual M23 point stabilizer. -/
abbrev pointRestriction {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) M23 V) :
    Representation (ZMod 2) Models.pointGroup V := σ.comp Models.pointGroup.subtype

variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

open Finsupp _root_.TensorProduct

/-- Inverse Frobenius reciprocity in the coinvariant convention:
`[g ⊗ w]` maps to `σ(g⁻¹)(f(w))`. -/
def induceMap
    (τ : Representation (ZMod 2) (MulAction.stabilizer M23 (9 : Fin 23)) W)
    (σ : Representation (ZMod 2) M23 V)
    (f : τ.IntertwiningMap (pointRestriction σ)) :
    (Representation.ind (MulAction.stabilizer M23 (9 : Fin 23)).subtype τ).IntertwiningMap σ :=
  ⟨Representation.Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift _ _ _ fun h => σ h⁻¹ ∘ₗ f.toLinearMap) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).toLinearMap)
    (fun g ↦ by
      ext h x
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply]
      simp [Representation.ofMulAction_single, mul_inv_rev,
        IntertwiningMap.isIntertwining τ (pointRestriction σ) f g]),
    fun g ↦ by ext; simp⟩

/-- Evaluation on the identity tensor recovers the given inclusion. -/
theorem induceMap_mk_one
    (τ : Representation (ZMod 2) (MulAction.stabilizer M23 (9 : Fin 23)) W)
    (σ : Representation (ZMod 2) M23 V)
    (f : τ.IntertwiningMap (pointRestriction σ)) (w : W) :
    induceMap τ σ f (Representation.IndV.mk
      (MulAction.stabilizer M23 (9 : Fin 23)).subtype τ 1 w) = f w := by
  simp [induceMap, Representation.IndV.mk]

/-- A nonzero restricted map stays nonzero under Frobenius reciprocity. -/
theorem induceMap_ne_zero
    (τ : Representation (ZMod 2) (MulAction.stabilizer M23 (9 : Fin 23)) W)
    (σ : Representation (ZMod 2) M23 V)
    (f : τ.IntertwiningMap (pointRestriction σ)) (hf : f ≠ 0) :
    induceMap τ σ f ≠ 0 := by
  intro hz
  apply hf
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro w
  have h := congrArg (fun k => k (Representation.IndV.mk
    (MulAction.stabilizer M23 (9 : Fin 23)).subtype τ 1 w)) hz
  rw [induceMap_mk_one] at h
  exact h

/-- An actual inclusion of a model in the restriction gives an induced
surjection onto an irreducible M23 representation, in any universe. -/
theorem exists_surjective_induced_of_equiv
    (σ : Representation (ZMod 2) M23 V) [σ.IsIrreducible]
    (S : Subrepresentation (pointRestriction σ))
    (a : Models.pointGroup ≃* M22) (b : Bool)
    (e : S.toRepresentation.Equiv (Models.pointAction a b)) :
    ∃ f : (Models.induced a b).IntertwiningMap σ, Function.Surjective f := by
  let j : S.toRepresentation.IntertwiningMap (pointRestriction σ) :=
    ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  let f := j.comp e.symm.toIntertwiningMap
  have hf : f ≠ 0 := by
    have hpos : 0 < Module.finrank (ZMod 2) (Models.Space b) := by
      rw [Models.finrank_space]; decide
    let : Nontrivial (Models.Space b) := Module.nontrivial_of_finrank_pos hpos
    obtain ⟨w, hw⟩ := exists_ne (0 : Models.Space b)
    intro hz
    have hfw : f w = 0 := congrArg (fun k => k w) hz
    have hew : e.symm w = 0 := Subtype.ext hfw
    exact hw (e.symm.toLinearEquiv.map_eq_zero_iff.mp hew)
  exact ⟨induceMap (Models.pointAction a b) σ f,
    (IsIrreducible.surjective_or_eq_zero _).resolve_right
      (induceMap_ne_zero _ _ f hf)⟩

end Representation.MathieuSmall.M23DegreeSpectrum
