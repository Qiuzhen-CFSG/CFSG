module

public import Theory.SpecificGroups.HaradaNorton.Simplicity.WordCertificates.Tables

/-!
# HN PerfectProducts multiplication certificates

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
/-- Certified matrix multiplication for `word`. -/
theorem product_word : decode ab5Rows * decode bPacked = decode wordRows :=
  decode_mul _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Certified matrix multiplication for `word2`. -/
theorem product_word2 : decode wordRows * decode wordRows = decode word2Rows :=
  decode_mul _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Certified matrix multiplication for `word4`. -/
theorem product_word4 : decode word2Rows * decode word2Rows = decode word4Rows :=
  decode_mul _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Certified matrix multiplication for `word8`. -/
theorem product_word8 : decode word4Rows * decode word4Rows = decode word8Rows :=
  decode_mul _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Certified matrix multiplication for `word12`. -/
theorem product_word12 : decode word8Rows * decode word4Rows = decode word12Rows :=
  decode_mul _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Certified matrix multiplication for `word24`. -/
theorem product_word24 : decode word12Rows * decode word12Rows = decode word24Rows :=
  decode_mul _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Certified matrix multiplication for `word25`. -/
theorem product_word25 : decode word24Rows * decode wordRows = decode oneRows :=
  decode_mul _ _ _ (by decide +kernel)

end HaradaNorton.WordCertificates
