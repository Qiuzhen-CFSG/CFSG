module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.Matrices.Rows

/-!
# Separation of the packed J4 normal forms

Six entries in row zero distinguish the 27 proposed matrices. The complete
finite injectivity check is performed by the Lean kernel. The numeric row
witnesses and source attribution are in `Matrices.Rows`; their interpretation
as the actual group words is a separate matrix-evaluation obligation.
-/

@[expose] public section
namespace Janko4.Simplicity.ThreeLocalCertificates

/-- A small observable sufficient to separate the 27 matrices. -/
def normalFormSignature (m : BinaryMatrix) : List (ZMod 2) :=
  [m 0 0, m 0 9, m 0 74, m 0 83, m 0 37, m 0 2]

set_option maxRecDepth 10000 in
theorem normalFormSignature_injective :
    Function.Injective (fun t => normalFormSignature (decodeRows (normalRows t))) := by
  decide +kernel

theorem normalRows_decode_injective :
    Function.Injective (fun t => decodeRows (normalRows t)) := by
  intro s t h
  exact normalFormSignature_injective (congrArg normalFormSignature h)

end Janko4.Simplicity.ThreeLocalCertificates
