module
public import Theory.SpecificGroups.ReeF4.DerivedTits.Realization.SimpleComparison
import all Theory.SpecificGroups.ReeF4.DerivedTits.Realization.SimpleComparison
/-!
# Checked binary coefficients for the two short simple roots

The compact row masks below describe the three divided powers at F4 nodes 2
and 3 in Cartan-first lexicographic-root coordinates. Their equality with the
actual integral Geck coefficients is verified by kernel reduction over F₂.
These are polynomial coefficients, so specialization does not lose the root
parameter. The internal import of `SimpleComparison` deliberately reuses its
root-string computation; no private declaration appears in the public API.

The sparse tables were suggested by an untrusted Python calculation. Only the
Lean-checked equalities are used in the subsequent chart comparison.
Source: the integral Geck construction and GLS3 §§2.3–2.6.
-/

namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart

/-- Cartan coordinates followed by the complete lexicographic root table. -/
public abbrev Index := Fin 4 ⊕ Fin 48

/-- The specified numbering of the actual Geck lattice. -/
@[expose] public noncomputable def basisCoordinates :
    Index ≃ Theory.AlgebraicGroup.F4Chevalley.BasisIndex :=
  Equiv.sumCongr Theory.AlgebraicGroup.StandardRootSystem.typeF4RootPairing_baseEquiv
    ReeF4.Parabolics.BinarySuzuki.MatrixIdentification.KernelProof.AmbientComputation.rootEquiv

namespace Coefficients
open ReeF4.DerivedTits.Realization.SimpleComparison
@[expose] public def rows : Bool → Fin 3 → Array ℕ
  | false => ![#[0, 0, 0, 262144, 0, 0, 0, 0, 0, 0, 0, 128, 256, 512, 0, 1024, 0, 0, 0, 0, 0, 16384, 0, 0, 0, 65536, 0, 131072, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 268435456, 1073741824, 2147483648, 17179869184, 34359738368, 68719476736, 0, 0, 0, 0, 17592186044416, 0, 0, 0],
      #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 256, 512, 0, 0, 0, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 262144, 0, 0, 0, 0, 0, 0, 0, 2147483648, 34359738368, 68719476736, 0, 0, 0, 0],
      #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
  | true => ![#[0, 0, 134217728, 0, 0, 0, 0, 64, 0, 0, 0, 0, 2048, 0, 8192, 0, 32768, 0, 131072, 0, 0, 1048576, 0, 0, 0, 16777216, 0, 0, 10, 0, 536870912, 0, 0, 0, 8589934592, 0, 0, 0, 137438953472, 0, 549755813888, 0, 2199023255552, 0, 8796093022208, 0, 0, 0, 140737488355328, 0, 0, 0],
      #[0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1048576, 0, 0, 0, 16777216, 0, 134217728, 0, 0, 536870912, 0, 0, 0, 8589934592, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 140737488355328, 0, 0],
      #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
@[expose] public def coefficient (k : Bool) (n : Fin 3) : Matrix Index Index (ZMod 2) :=
  fun r c => Thompson.BinaryMatrix.decode 52 (rows k n) (finSumFinEquiv r) (finSumFinEquiv c)
private def intCoeff (k : Bool) (n : Fin 3) : Matrix Index Index ℤ :=
  if n = 0 then eLinear (if k then 2 else 3)
  else eHigher (if k then 2 else 3) (n.val + 1)
private theorem positive_table : ∀ (k : Bool) (n : Fin 3) (r c : Index),
    (intCoeff k n r c : ZMod 2) = coefficient k n r c := by
  let dec : Decidable (∀ (k : Bool) (n : Fin 3) (r c : Index),
      (intCoeff k n r c : ZMod 2) = coefficient k n r c) :=
    @Fintype.decidableForallFintype Bool _ (fun k =>
      @Fintype.decidableForallFintype (Fin 3) _ (fun n =>
        @Fintype.decidableForallFintype Index _ (fun r =>
          @Fintype.decidableForallFintype Index _
            (fun c => ZMod.decidableEq 2 _ _) inferInstance) inferInstance) inferInstance)
        inferInstance
  exact @of_decide_eq_true _ dec (by decide +kernel)
end Coefficients
end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart
