module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.Inputs
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.TraceComparison
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.Factors
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors

/-!
# Recognition through the actual twenty-dimensional principal-series factor

The canonical permutation flag and the Borel coset count select a simple
twenty-dimensional interior section. Borel-preserving field transport
places it in the original induced module. An exhaustive trace comparison,
followed by simple-module density, identifies the specified arbitrary
representation with this literal quotient over the original field.

The conditional assembly is retained, and
`root_center_free_twenty_recognition` discharges all three group-specific
inputs using the proved middle flag, literal coset count and exhaustive
trace comparison. The original root-center fixed-space premise remains;
the parent recognition assembly supplies it from nonlinear multiplicities.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

public section

namespace Representation.SU3.FiveSmallModules.SevenRestriction

universe v
open Degrees.TrivialCalculation Twenty

/-- The trace calculation and concrete middle flag give the requested
equivalence to an interior section of trivial Borel induction. -/
theorem root_center_free_twenty_recognition_of_trace_and_middle_flags
    (htrace : TwentyTraceComparison.{v})
    (hcard : Nat.card CanonicalPoints = 126)
    (hmiddle : CanonicalMiddleFlags.{v}) :
    RootCenterFreeTwentyRecognition.{0, v} := by
  intro F _ _ J hc hconj K _ _ _ U _ _ _ τ hk hi hd hz
  obtain ⟨S, T, hs, hdim⟩ :=
    trivial_twenty_factor_of_middle_flags hcard hmiddle J hc hconj K
  let : FiniteDimensional K (S.toSubmodule ⧸ T.toSubmodule) :=
    FiniteDimensional.of_finrank_pos (by omega)
  let : τ.IsAbsolutelyIrreducible := hi
  let : T.quotientRepresentation.IsIrreducible := hs
  exact ⟨1, S, T, equiv_of_equal_trace τ T.quotientRepresentation
    (htrace F J hc hconj K U τ hk hi hd hz S T hs hdim)⟩

/-- Every root-center-free absolute degree-twenty representation in the
recognition contract is equivalent, over its original coefficient field,
to an interior quotient of the literal Borel-induced representation. -/
theorem root_center_free_twenty_recognition : RootCenterFreeTwentyRecognition.{0, v} :=
  root_center_free_twenty_recognition_of_trace_and_middle_flags
    twenty_trace_comparison canonical_borel_coset_card canonical_middle_flags

end Representation.SU3.FiveSmallModules.SevenRestriction
