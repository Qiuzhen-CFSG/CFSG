module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.NormalGeneration.Bridge
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates.Packed

/-!
# Transport of packed certificates for normal-generation bridges

The arithmetic checker in `GeneratorCertificates.Packed` proves multiplication
of the concrete matrices. These two lemmas transport its results to the
faithful matrix image of a product or a power in the actual group carrier.
-/

public section
namespace Janko4.Simplicity.NormalGeneration
open GeneratorCertificates

theorem decode_mul_step {xs ys zs : Vector ℕ 112} {x y : Model}
    (h : packedMul xs ys = zs) (hx : decodeRows xs = toMatrix x)
    (hy : decodeRows ys = toMatrix y) : decodeRows zs = toMatrix (x * y) := by
  rw [← h, decode_packedMul, hx, hy, map_mul]

theorem decode_pow_step {xs ys zs : Vector ℕ 112} {x : Model} {m n : ℕ}
    (h : packedMul xs ys = zs) (hx : decodeRows xs = toMatrix (x ^ m))
    (hy : decodeRows ys = toMatrix (x ^ n)) : decodeRows zs = toMatrix (x ^ (m + n)) := by
  simpa only [← pow_add] using decode_mul_step h hx hy

end Janko4.Simplicity.NormalGeneration
