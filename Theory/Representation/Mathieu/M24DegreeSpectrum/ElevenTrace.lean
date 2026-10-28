module

public import Theory.Representation.Mathieu.M24DegreeSpectrum
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.PrimeFusion
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.TraceReduction
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.Remaining
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.OrderRestrictions
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.OrderSpectrum
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.MixedCoverage

/-!
# Native square fusion and the degree-eleven M₂₄ trace field

The kernel-checked cyclic representatives and Sylow argument prove square
conjugacy for every element of odd prime order. The odd-order spectrum and
mixed-order cyclic coverage complete square conjugacy on all 2-regular
elements. The p-regular trace reduction then fixes every characteristic-two
trace under Frobenius, in particular those of all absolute degree-eleven
representations over every finite field of characteristic two.

The application below uses the actual Schur-field representation of a binary
irreducible module, exactly as in `finrank_eq_eleven_of_absolute_eleven`.
The native spectrum and mixed-order coverage discharge both group-theoretic
inputs, giving the unconditional `degreeElevenTraceField`. The absolute degree
spectrum remains a separate calculation; it is not needed for this trace result.

Source: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
M₂₄ paragraph, manuscript p.17; James, The modular characters of the Mathieu
groups, J. Algebra 27 (1973), 57–111.
-/

public section
namespace Sporadic.Mathieu.M24OddCyclic

/-- Assembly of all odd classes from the two native coverage calculations. -/
theorem odd_square_conjugacy_of_calculations
    (hspectrum : OddOrderSpectrum) (hmixed : MixedOrderCyclicCoverage)
    (g : M24) (hg : ¬ 2 ∣ orderOf g) : IsConj g (g ^ 2) := by
  rcases hspectrum g hg with h | h | h | h
  · have he : g = 1 := orderOf_eq_one_iff.mp h
    simp [he]
  · exact square_conjugacy_of_odd_prime_order g h hg
  · obtain ⟨i, n, hn⟩ := hmixed g (Or.inl h)
    exact IsConj.square_of_conjugate_power (representative_square_conjugacy _) n hn
  · obtain ⟨i, n, hn⟩ := hmixed g (Or.inr h)
    exact IsConj.square_of_conjugate_power (representative_square_conjugacy _) n hn

/-- Every odd-order element of the native Witt-design M₂₄ is conjugate to its square. -/
theorem odd_square_conjugacy (g : M24) (hg : ¬ 2 ∣ orderOf g) :
    IsConj g (g ^ 2) :=
  odd_square_conjugacy_of_calculations oddOrderSpectrum mixedOrderCyclicCoverage g hg

end Sporadic.Mathieu.M24OddCyclic

namespace Representation.Mathieu.M24DegreeSpectrum
open Sporadic.Mathieu M24OddCyclic
universe v

/-- Conditional trace-field calculation; neither a chosen model nor its field is assumed. -/
theorem degreeElevenTraceField_of_odd_order_calculations
    (hspectrum : OddOrderSpectrum) (hmixed : MixedOrderCyclicCoverage) :
    DegreeElevenTraceField.{v} := by
  intro K _ _ _ W _ _ _ τ _ _ _ g
  exact character_sq_of_odd_square_conjugacy τ
    (odd_square_conjugacy_of_calculations hspectrum hmixed) g

/-- All faithful absolutely irreducible degree-eleven actions have binary-valued traces. -/
theorem degreeElevenTraceField : DegreeElevenTraceField.{v} :=
  degreeElevenTraceField_of_odd_order_calculations oddOrderSpectrum mixedOrderCyclicCoverage

open scoped MonoidAlgebra

/-- The literal Schur-field consumer of the two native group calculations. -/
theorem finrank_eq_eleven_of_odd_order_calculations
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) M24 V) [σ.IsIrreducible]
    (hspectrum : OddOrderSpectrum) (hmixed : MixedOrderCyclicCoverage)
    (hf : Function.Injective σ)
    (ha : Module.finrank (Module.End (ZMod 2)[M24] σ.asModule) σ.asModule = 11) :
    Module.finrank (ZMod 2) V = 11 :=
  finrank_eq_eleven_of_absolute_eleven σ
    (degreeElevenTraceField_of_odd_order_calculations hspectrum hmixed) hf ha

/-- Absolute degree eleven for the actual Schur-field action forces binary degree eleven.
The trace-field premise of `finrank_eq_eleven_of_absolute_eleven` is discharged. -/
theorem finrank_eq_eleven_of_native_absolute_eleven
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) M24 V) [σ.IsIrreducible]
    (hf : Function.Injective σ)
    (ha : Module.finrank (Module.End (ZMod 2)[M24] σ.asModule) σ.asModule = 11) :
    Module.finrank (ZMod 2) V = 11 :=
  finrank_eq_eleven_of_absolute_eleven σ degreeElevenTraceField hf ha

end Representation.Mathieu.M24DegreeSpectrum
