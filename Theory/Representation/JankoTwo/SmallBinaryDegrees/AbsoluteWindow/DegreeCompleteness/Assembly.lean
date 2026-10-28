module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.Contracts
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.DegreeCompleteness.Inputs
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.DegreeCompleteness.LowerBound
public import Theory.Representation.PSL3Three.AbsoluteDegrees.Saturation
import Lean.Elab.Tactic.Omega

/-!
# Scalar-extension assembly of the Hall--Janko degree window

The literal carrier's faithful irreducible representations have dimension at
least six, by the order-eight and Scott-inequality arguments in `LowerBound`.
To finish the window, extension to an algebraic closure preserves faithfulness
and dimension, and absolute irreducibility supplies simplicity there. A proved
closed-field spectrum then gives degrees six or fourteen.

The second route derives that spectrum from actual pairwise inequivalent
simple actions and an odd-order conjugacy-class bound, using the general modular
trace-independence exhaustion theorem. The candidates may have any larger
dimensions; only their separation from the interval up to 32 is needed.

The closed-field spectrum and model certificates remain explicit inputs to
these reusable conditional assemblies. `ModularCertificate.Complete` constructs
the spectrum, and `DegreeCompleteness` applies it to prove `DegreeWindow`.
Keeping the scalar-extension assembly here avoids a cycle with that producer.

Sources: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
manuscript p.16; corrected Hiss--Malle Table 2, characteristic-two J₂ rows.
-/

public section
open scoped TensorProduct
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
open Sporadic.LeechRelated.J2
universe v w

/-- Genuine pairwise inequivalent simple actions saturating the odd-order class
bound give the algebraically closed degree alternatives. -/
theorem small_degree_of_saturating_family
    {F U : Type v} {ι : Type w}
    [Field F] [IsAlgClosed F] [CharP F 2] [Fintype ι]
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    (V : ι → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)]
    [∀ i, FiniteDimensional F (V i)] (ρ : ∀ i, Representation F Carrier (V i))
    [∀ i, IsIrreducible (ρ i)]
    (hne : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)))
    (hclasses : Nat.card (ConjClasses.mk ''
      {g : Carrier | ¬ 2 ∣ orderOf g}) ≤ Nat.card ι)
    (hdegrees : ∀ i, Module.finrank F (V i) = 1 ∨ Module.finrank F (V i) = 6 ∨
      Module.finrank F (V i) = 14 ∨ 32 < Module.finrank F (V i))
    (τ : Representation F Carrier U) [τ.IsIrreducible]
    (hd : Module.finrank F U ≤ 32) :
    Module.finrank F U = 1 ∨ Module.finrank F U = 6 ∨ Module.finrank F U = 14 := by
  obtain ⟨i, ⟨e⟩⟩ := exists_equiv_of_pRegular_class_bound V ρ 2 hne hclasses τ
  have he := e.toLinearEquiv.finrank_eq
  have hi := hdegrees i
  omega

/-- Extending scalars preserves the degree and faithfulness, and absolute
irreducibility supplies irreducibility over the algebraic closure. The
one-dimensional branch is excluded by the separately proved carrier bound. -/
theorem degreeWindow_of_closedSmallDegreeSpectrum
    (hspectrum : ClosedSmallDegreeSpectrum.{v}) : DegreeWindow.{v} := by
  intro K _ _ _ U _ _ _ τ hf hi hd
  let F := AlgebraicClosure K
  let := hi.irreducible_of_closure
  have hd' : Module.finrank F (F ⊗[K] U) ≤ 32 := by
    simpa only [Module.finrank_baseChange] using hd
  have h := hspectrum F (F ⊗[K] U) (extendScalars F τ) hd'
  have hf' := (extendScalars_faithful_iff F τ).mp hf
  have hlow := six_le_finrank_of_faithful_irreducible (extendScalars F τ) hf' inferInstance
  simp only [Module.finrank_baseChange] at h hlow
  omega

/-- Actual model constructions and the class bound feed the literal degree-window
consumer. The existence certificate remains an explicit undischarged input. -/
theorem degreeWindow_of_saturating_models
    (hmodels : SaturatingModelsExist.{v}) : DegreeWindow.{v} := by
  apply degreeWindow_of_closedSmallDegreeSpectrum
  intro F _ _ _ U _ _ _ τ _ hd
  obtain ⟨n, d, ρ, hirr, hne, hclasses, hdegrees⟩ := hmodels F
  let := hirr
  apply small_degree_of_saturating_family (fun i => Fin (d i) → F) ρ hne
    (by simpa only [Nat.card_fin] using hclasses) ?_ τ hd
  intro i
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hdegrees i

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
