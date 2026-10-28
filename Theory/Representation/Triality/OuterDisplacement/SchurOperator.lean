module

public import Theory.Representation.SchurLinearOperator
public import Theory.Representation.Triality.OuterDisplacement.TensorCoordinates
public import Theory.Representation.Triality.OuterDisplacement.Commutant

/-!
# Descent of the actual commutant-centralizing triality actor

The original ambient operator becomes linear over the component's actual
Schur field. Scalar extension preserves its displacement rank and the Schur
field tower multiplies both module degree and displacement by the same factor.
Thus the paired-tensor ratio over the algebraic closure descends to the original
action. Component absolute irreducibility over the starting field is unnecessary.
The independent paired-tensor construction supplies the displayed ratio.
Source: Guralnick--Malle II, Section 3.5 and Lemma 8.6.
-/

@[expose] public noncomputable section
open scoped MonoidAlgebra TensorProduct
open Representation
namespace Triality.OuterDisplacement
variable {E H W : Type*} [Field E] [Finite E] [Group H]
  [AddCommGroup W] [Module E W] [FiniteDimensional E W]
  (σ : Representation E H W) (N : Subgroup H) [IsIrreducible (σ.comp N.subtype)]
  (t : H) (hc : CentralizesCommutant σ N t)

/-- The literal original actor over the component Schur field. -/
def componentSchurOperator :
    Module.End (Module.End E[N] (Representation.asModule (σ.comp N.subtype))) (Representation.asModule (σ.comp N.subtype)) :=
  SchurOperator.linear (σ.comp N.subtype) (σ t) hc

/-- The actual paired-operator ratio descends from the component Schur closure. -/
theorem displacement_ratio_of_absolute_schur
    (K : Type*) [Field K] [Algebra (Module.End E[N] (Representation.asModule (σ.comp N.subtype))) K]
    [FiniteDimensional (Module.End E[N] (Representation.asModule (σ.comp N.subtype))) (Representation.asModule (σ.comp N.subtype))]
    (hratio : 7 * Module.finrank K (K ⊗[Module.End E[N] (Representation.asModule (σ.comp N.subtype))]
          (Representation.asModule (σ.comp N.subtype))) ≤
      16 * Module.finrank K (LinearMap.range
        ((componentSchurOperator σ N t hc).baseChange K - LinearMap.id))) :
    7 * Module.finrank E W ≤ 16 * Module.finrank E (LinearMap.range (σ t - LinearMap.id)) := by
  apply SchurOperator.ratio_descent (σ.comp N.subtype) (σ t) hc 7 16
  have hd : Module.finrank K (K ⊗[Module.End E[N] (Representation.asModule (σ.comp N.subtype))]
      (Representation.asModule (σ.comp N.subtype))) =
      Module.finrank (Module.End E[N] (Representation.asModule (σ.comp N.subtype)))
        (Representation.asModule (σ.comp N.subtype)) := Module.finrank_baseChange
  have hr := displacement_finrank_baseChange (componentSchurOperator σ N t hc) K
  rw [hd,hr] at hratio
  exact hratio

end Triality.OuterDisplacement
