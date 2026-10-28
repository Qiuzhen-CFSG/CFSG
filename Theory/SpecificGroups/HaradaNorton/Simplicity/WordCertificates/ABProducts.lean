module

public import Theory.SpecificGroups.HaradaNorton.Simplicity.WordCertificates.Tables

/-!
# HN ABProducts multiplication certificates

Each packed product is checked by kernel reduction. The soundness
theorem converts it to ordinary matrix multiplication over GF(5).

Source: ATLAS HN standard generators and class-25A word,
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/HN/.
Matrix attribution: `../../MatrixSources.md`. Regenerate with
`GenerateCertificates.py`; Python only supplies candidate data.
-/

public section
namespace HaradaNorton.WordCertificates

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Certified matrix multiplication for `ab`. -/
theorem product_ab : decode aPacked * decode bPacked = decode abRows :=
  decode_mul _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Certified matrix multiplication for `ab2`. -/
theorem product_ab2 : decode abRows * decode abRows = decode ab2Rows :=
  decode_mul _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Certified matrix multiplication for `ab4`. -/
theorem product_ab4 : decode ab2Rows * decode ab2Rows = decode ab4Rows :=
  decode_mul _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Certified matrix multiplication for `ab5`. -/
theorem product_ab5 : decode ab4Rows * decode abRows = decode ab5Rows :=
  decode_mul _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Certified matrix multiplication for `ab10`. -/
theorem product_ab10 : decode ab5Rows * decode ab5Rows = decode ab10Rows :=
  decode_mul _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Certified matrix multiplication for `ab11`. -/
theorem product_ab11 : decode ab10Rows * decode abRows = decode ab11Rows :=
  decode_mul _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Certified matrix multiplication for `ab22`. -/
theorem product_ab22 : decode ab11Rows * decode ab11Rows = decode oneRows :=
  decode_mul _ _ _ (by decide +kernel)

end HaradaNorton.WordCertificates
