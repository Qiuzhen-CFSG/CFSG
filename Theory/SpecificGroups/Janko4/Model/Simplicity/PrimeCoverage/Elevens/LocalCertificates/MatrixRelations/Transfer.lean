module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.LocalCertificates.Relations
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates.Packed
/-!
# Transfer of packed certificates to group words

Products and right-inverse witnesses are transported through the faithful
112-dimensional representation. The matrix arithmetic interface is `Packed`.
-/

public section
open Janko4 Janko4.GeneratorCertificates
namespace Janko4.Simplicity.Elevens.MatrixCertificates
lemma mul_certificate {g h : Model} {rs ss ts : Vector ℕ 112}
    (hg : toMatrix g = decodeRows rs) (hh : toMatrix h = decodeRows ss)
    (hc : packedMul rs ss = ts) : toMatrix (g * h) = decodeRows ts := by
  rw [map_mul, hg, hh, ← decode_packedMul, hc]
lemma pow_certificate {g : Model} {m n : ℕ} {rs ss ts : Vector ℕ 112}
    (hg : toMatrix (g ^ m) = decodeRows rs) (hh : toMatrix (g ^ n) = decodeRows ss)
    (hc : packedMul rs ss = ts) : toMatrix (g ^ (m + n)) = decodeRows ts := by
  rw [pow_add]
  exact mul_certificate hg hh hc
lemma inv_certificate {g : Model} {rs ss : Vector ℕ 112}
    (hg : toMatrix g = decodeRows rs) (hc : packedMul rs ss = packedOne) :
    toMatrix g⁻¹ = decodeRows ss := by
  have h : toMatrix g * decodeRows ss = 1 := by
    rw [hg, ← decode_packedMul, hc, decode_packedOne]
  calc
    toMatrix g⁻¹ = toMatrix g⁻¹ * 1 := (mul_one _).symm
    _ = toMatrix g⁻¹ * (toMatrix g * decodeRows ss) := by rw [h]
    _ = decodeRows ss := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
end Janko4.Simplicity.Elevens.MatrixCertificates
