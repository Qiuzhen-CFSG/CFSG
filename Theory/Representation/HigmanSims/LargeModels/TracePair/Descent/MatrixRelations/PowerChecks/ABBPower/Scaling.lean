module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.LinearCertificates
import Batteries.Data.Nat.Bitwise

/-!
# Normalized multiplication by omega squared

The existing omega-scaling constructor applied twice is multiplication by
omega + 1. Cancelling the repeated XOR gives one XOR per plane pair.
The dense certificates for the literal source relator (AB²)¹⁰ consume this
constructor; no numerical matrix equation is assumed.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABBPower
open Representation.HigmanSims.LargeModels.TracePair.Certificates
open LinearCertificates

noncomputable def tt {n : ℕ} {b : Packed.Mat} (x : Cert (n := n) b) : Cert (n := n) b :=
  ⟨(x.input.1 ^^^ x.input.2, x.input.1),
    (x.output.1 ^^^ x.output.2, x.output.1), by
      have h := good_t b _ _ (good_t b _ _ x.sound)
      have hc (a b : ℕ) : b ^^^ (a ^^^ b) = a := by
        rw [Nat.xor_comm a b, Nat.xor_xor_cancel_left]
      simpa only [Packed.Base.timesT, hc] using h⟩

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABBPower
