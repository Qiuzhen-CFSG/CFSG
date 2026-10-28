module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Tables

/-! Centralizer-coset certificate for the thirteen ATLAS HS relators.
Untrusted data generated from the retained trace; all deduction checks use
Lean's kernel and the actual abstract relations. See `source/README.md`. -/

public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_163840 : Scan.checkChunk context facts instructions 163840 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_164352 : Scan.checkChunk context facts instructions 164352 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_164864 : Scan.checkChunk context facts instructions 164864 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_165376 : Scan.checkChunk context facts instructions 165376 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_165888 : Scan.checkChunk context facts instructions 165888 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_166400 : Scan.checkChunk context facts instructions 166400 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_166912 : Scan.checkChunk context facts instructions 166912 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_167424 : Scan.checkChunk context facts instructions 167424 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_167936 : Scan.checkChunk context facts instructions 167936 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_168448 : Scan.checkChunk context facts instructions 168448 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_168960 : Scan.checkChunk context facts instructions 168960 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_169472 : Scan.checkChunk context facts instructions 169472 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_169984 : Scan.checkChunk context facts instructions 169984 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_170496 : Scan.checkChunk context facts instructions 170496 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_171008 : Scan.checkChunk context facts instructions 171008 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_171520 : Scan.checkChunk context facts instructions 171520 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_172032 : Scan.checkChunk context facts instructions 172032 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_172544 : Scan.checkChunk context facts instructions 172544 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_173056 : Scan.checkChunk context facts instructions 173056 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_173568 : Scan.checkChunk context facts instructions 173568 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_174080 : Scan.checkChunk context facts instructions 174080 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_174592 : Scan.checkChunk context facts instructions 174592 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_175104 : Scan.checkChunk context facts instructions 175104 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_175616 : Scan.checkChunk context facts instructions 175616 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_176128 : Scan.checkChunk context facts instructions 176128 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_176640 : Scan.checkChunk context facts instructions 176640 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_177152 : Scan.checkChunk context facts instructions 177152 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_177664 : Scan.checkChunk context facts instructions 177664 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_178176 : Scan.checkChunk context facts instructions 178176 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_178688 : Scan.checkChunk context facts instructions 178688 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_179200 : Scan.checkChunk context facts instructions 179200 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_179712 : Scan.checkChunk context facts instructions 179712 512 = true := by
  decide +kernel

theorem all_hold_180224 (prior : ∀ n, n < 163840 → Holds centralizer certGenerator (definitions.repr certGenerator) (facts n)) : ∀ n, n < 180224 →
    Holds centralizer certGenerator (definitions.repr certGenerator) (facts n) := by
  have h164352 := Scan.chunk_sound context_valid facts instructions 163840 512
    prior checked_163840
  have h164864 := Scan.chunk_sound context_valid facts instructions 164352 512
    h164352 checked_164352
  have h165376 := Scan.chunk_sound context_valid facts instructions 164864 512
    h164864 checked_164864
  have h165888 := Scan.chunk_sound context_valid facts instructions 165376 512
    h165376 checked_165376
  have h166400 := Scan.chunk_sound context_valid facts instructions 165888 512
    h165888 checked_165888
  have h166912 := Scan.chunk_sound context_valid facts instructions 166400 512
    h166400 checked_166400
  have h167424 := Scan.chunk_sound context_valid facts instructions 166912 512
    h166912 checked_166912
  have h167936 := Scan.chunk_sound context_valid facts instructions 167424 512
    h167424 checked_167424
  have h168448 := Scan.chunk_sound context_valid facts instructions 167936 512
    h167936 checked_167936
  have h168960 := Scan.chunk_sound context_valid facts instructions 168448 512
    h168448 checked_168448
  have h169472 := Scan.chunk_sound context_valid facts instructions 168960 512
    h168960 checked_168960
  have h169984 := Scan.chunk_sound context_valid facts instructions 169472 512
    h169472 checked_169472
  have h170496 := Scan.chunk_sound context_valid facts instructions 169984 512
    h169984 checked_169984
  have h171008 := Scan.chunk_sound context_valid facts instructions 170496 512
    h170496 checked_170496
  have h171520 := Scan.chunk_sound context_valid facts instructions 171008 512
    h171008 checked_171008
  have h172032 := Scan.chunk_sound context_valid facts instructions 171520 512
    h171520 checked_171520
  have h172544 := Scan.chunk_sound context_valid facts instructions 172032 512
    h172032 checked_172032
  have h173056 := Scan.chunk_sound context_valid facts instructions 172544 512
    h172544 checked_172544
  have h173568 := Scan.chunk_sound context_valid facts instructions 173056 512
    h173056 checked_173056
  have h174080 := Scan.chunk_sound context_valid facts instructions 173568 512
    h173568 checked_173568
  have h174592 := Scan.chunk_sound context_valid facts instructions 174080 512
    h174080 checked_174080
  have h175104 := Scan.chunk_sound context_valid facts instructions 174592 512
    h174592 checked_174592
  have h175616 := Scan.chunk_sound context_valid facts instructions 175104 512
    h175104 checked_175104
  have h176128 := Scan.chunk_sound context_valid facts instructions 175616 512
    h175616 checked_175616
  have h176640 := Scan.chunk_sound context_valid facts instructions 176128 512
    h176128 checked_176128
  have h177152 := Scan.chunk_sound context_valid facts instructions 176640 512
    h176640 checked_176640
  have h177664 := Scan.chunk_sound context_valid facts instructions 177152 512
    h177152 checked_177152
  have h178176 := Scan.chunk_sound context_valid facts instructions 177664 512
    h177664 checked_177664
  have h178688 := Scan.chunk_sound context_valid facts instructions 178176 512
    h178176 checked_178176
  have h179200 := Scan.chunk_sound context_valid facts instructions 178688 512
    h178688 checked_178688
  have h179712 := Scan.chunk_sound context_valid facts instructions 179200 512
    h179200 checked_179200
  have h180224 := Scan.chunk_sound context_valid facts instructions 179712 512
    h179712 checked_179712
  exact h180224

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
