module

public import Theory.Representation.SimpleScalarEmbedding
public import Theory.Representation.SimpleScalarMap
public import Theory.Representation.BinaryAlternatingSixModels.CatalogueSource
public import Theory.Representation.BinaryAlternatingSixModels.TensorSchurDegree

/-!
# Four-dimensional A₆ actions in characteristic two

Choose a simple binary submodule in the restricted action. The complete binary
catalogue gives the trivial, two natural, and sixteen-dimensional tensor models.
The trivial model cannot span a simple four-space. The tensor has Schur degree
at most two, so Jacobson density requires coefficient-field dimension at least
eight. Each remaining natural binary four-space therefore extends to an actual
equivalence with the original action. No absolute-irreducibility hypothesis,
choice of coefficient subfield, or change of the marked actor is needed.
Source: Aschbacher–Smith G.4.1 and G.5.1, printed pp.342–343.
-/
open Representation Module
open scoped MonoidAlgebra TensorProduct
open Theory.SpecificGroups.SymmetricSix
namespace BinaryAlternatingSix.ScalarFour
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
 [AddCommGroup V] [Module F V] [FiniteDimensional F V]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2
/-- Every irreducible four-dimensional A₆ action is a scalar extension of one
of the two literal binary natural actions. -/
theorem classify (ρ : Representation F A6 V) [ρ.IsIrreducible]
 (hd : Module.finrank F V = 4)
 :
 Nonempty ((extendScalars F firstAlternating).Equiv ρ) ∨
 Nonempty ((extendScalars F secondAlternating).Equiv ρ) := by
 classical
 let : Module (ZMod 2) V := Module.compHom V (algebraMap (ZMod 2) F)
 let : IsScalarTower (ZMod 2) F V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
 let : Finite V := Module.finite_of_finite F
 let : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
 let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
 let τ : Representation (ZMod 2) A6 V := restrictScalars ρ
 obtain ⟨U,hU⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional τ
 let : U.toRepresentation.IsIrreducible := hU
 let inc : U.toSubmodule →ₗ[ZMod 2] V := U.toSubmodule.subtype
 have incinj : Function.Injective inc := by
   intro x y h
   apply Subtype.ext
   exact h
 rcases (show IsAlternatingModel U.toRepresentation from alternating_classify U.toRepresentation) with h | h | h | h
 · obtain ⟨e⟩ := h
   let i := inc.comp e.symm.toLinearEquiv.toLinearMap
   have hi : i ≠ 0 := by
     intro hz
     let : Nontrivial (ZMod 2) := inferInstance
     have h1 : (1 : ZMod 2) = 0 := (incinj.comp e.symm.injective) (by
       simpa [i] using congrArg (fun l : ZMod 2 →ₗ[ZMod 2] V => l 1) hz)
     exact one_ne_zero h1
   have hc (g : A6) (u : ZMod 2) : i (trivialAlternating g u) = ρ g (i u) := by
     exact congrArg inc (LinearMap.congr_fun (e.symm.isIntertwining' g) u)
   have hl := SimpleScalarMap.finrank_le trivialAlternating ρ i hi hc
   simp only [Module.finrank_self,hd] at hl
   omega
 · left
   obtain ⟨e⟩ := h
   let i := inc.comp e.symm.toLinearEquiv.toLinearMap
   have hinj : Function.Injective i := incinj.comp e.symm.injective
   have hi : i ≠ 0 := by
     intro hz
     obtain ⟨u,hu⟩ := exists_ne (0 : NaturalModule)
     exact hu (hinj (by simp [hz]))
   exact SimpleScalarMap.equiv_of_finrank_eq firstAlternating ρ i hi
     (fun g u => congrArg inc (LinearMap.congr_fun (e.symm.isIntertwining' g) u))
     (naturalModule_finrank.trans hd.symm)
 · right
   obtain ⟨e⟩ := h
   let i := inc.comp e.symm.toLinearEquiv.toLinearMap
   have hinj : Function.Injective i := incinj.comp e.symm.injective
   have hi : i ≠ 0 := by
     intro hz
     obtain ⟨u,hu⟩ := exists_ne (0 : NaturalModule)
     exact hu (hinj (by simp [hz]))
   exact SimpleScalarMap.equiv_of_finrank_eq secondAlternating ρ i hi
     (fun g u => congrArg inc (LinearMap.congr_fun (e.symm.isIntertwining' g) u))
     (naturalModule_finrank.trans hd.symm)
 · obtain ⟨e⟩ := h
   let i := inc.comp e.symm.toLinearEquiv.toLinearMap
   have hinj : Function.Injective i := incinj.comp e.symm.injective
   let σ : Representation (ZMod 2) A6 TensorModule := alternatingTensor
   let : σ.IsIrreducible := alternatingTensor_irreducible
   have hb := SimpleScalarEmbedding.schur_finrank_le σ ρ i hinj
     (fun g u => congrArg inc (LinearMap.congr_fun (e.symm.isIntertwining' g) u))
   let E := Module.End (ZMod 2)[A6] σ.asModule
   let : Field E := Representation.endField_field σ
   let : Module.Free E σ.asModule := Module.Free.of_divisionRing E σ.asModule
   let : Finite σ.asModule := Module.finite_of_finite (ZMod 2)
   let : FiniteDimensional E σ.asModule := Module.Finite.of_finite
   have heq : 16 = Module.finrank (ZMod 2) E * Module.finrank E σ.asModule := by
     rw [Module.finrank_mul_finrank]
     exact tensor_finrank.symm.trans σ.asModuleEquiv.finrank_eq.symm
   rw [hd] at hb
   have ht : Module.finrank (ZMod 2) E ≤ 2 := alternatingTensor_endField_finrank_le_two
   nlinarith

/-- Keep the original actor and its specified A₆ identification in the literal
coefficient-field intertwiner. -/
theorem exists_intertwiner {N : Type*} [Group N]
    (ρ : Representation F N V) [ρ.IsIrreducible] (e : N ≃* A6)
    (hd : Module.finrank F V = 4) :
    ∃ A : V ≃ₗ[F] F ⊗[ZMod 2] NaturalModule,
      (∀ n v, A (ρ n v) = extendScalars F firstAlternating (e n) (A v)) ∨
      (∀ n v, A (ρ n v) = extendScalars F secondAlternating (e n) (A v)) := by
  let τ : Representation F A6 V := ρ.comp e.symm.toMonoidHom
  let : τ.IsIrreducible := (irreducible_comp_surjective_iff e.symm.toMonoidHom
    e.symm.surjective ρ).mpr inferInstance
  rcases classify τ hd with ha | ha
  · obtain ⟨a⟩ := ha
    refine ⟨a.symm.toLinearEquiv,Or.inl ?_⟩
    intro n v
    have hh := LinearMap.congr_fun (a.symm.isIntertwining' (e n)) v
    simpa [τ] using hh
  · obtain ⟨a⟩ := ha
    refine ⟨a.symm.toLinearEquiv,Or.inr ?_⟩
    intro n v
    have hh := LinearMap.congr_fun (a.symm.isIntertwining' (e n)) v
    simpa [τ] using hh

end
end BinaryAlternatingSix.ScalarFour
