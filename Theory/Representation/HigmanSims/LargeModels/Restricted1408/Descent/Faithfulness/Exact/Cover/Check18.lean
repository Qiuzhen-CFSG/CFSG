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
theorem checked_294912 : Scan.checkChunk context facts instructions 294912 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_295424 : Scan.checkChunk context facts instructions 295424 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_295936 : Scan.checkChunk context facts instructions 295936 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_296448 : Scan.checkChunk context facts instructions 296448 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_296960 : Scan.checkChunk context facts instructions 296960 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_297472 : Scan.checkChunk context facts instructions 297472 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_297984 : Scan.checkChunk context facts instructions 297984 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_298496 : Scan.checkChunk context facts instructions 298496 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_299008 : Scan.checkChunk context facts instructions 299008 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_299520 : Scan.checkChunk context facts instructions 299520 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_300032 : Scan.checkChunk context facts instructions 300032 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_300544 : Scan.checkChunk context facts instructions 300544 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_301056 : Scan.checkChunk context facts instructions 301056 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_301568 : Scan.checkChunk context facts instructions 301568 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_302080 : Scan.checkChunk context facts instructions 302080 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_302592 : Scan.checkChunk context facts instructions 302592 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_303104 : Scan.checkChunk context facts instructions 303104 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_303616 : Scan.checkChunk context facts instructions 303616 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_304128 : Scan.checkChunk context facts instructions 304128 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_304640 : Scan.checkChunk context facts instructions 304640 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_305152 : Scan.checkChunk context facts instructions 305152 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_305664 : Scan.checkChunk context facts instructions 305664 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_306176 : Scan.checkChunk context facts instructions 306176 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_306688 : Scan.checkChunk context facts instructions 306688 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_307200 : Scan.checkChunk context facts instructions 307200 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_307712 : Scan.checkChunk context facts instructions 307712 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_308224 : Scan.checkChunk context facts instructions 308224 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_308736 : Scan.checkChunk context facts instructions 308736 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_309248 : Scan.checkChunk context facts instructions 309248 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_309760 : Scan.checkChunk context facts instructions 309760 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_310272 : Scan.checkChunk context facts instructions 310272 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_310784 : Scan.checkChunk context facts instructions 310784 512 = true := by
  decide +kernel

theorem all_hold_311296 (prior : ∀ n, n < 294912 → Holds centralizer certGenerator (definitions.repr certGenerator) (facts n)) : ∀ n, n < 311296 →
    Holds centralizer certGenerator (definitions.repr certGenerator) (facts n) := by
  have h295424 := Scan.chunk_sound context_valid facts instructions 294912 512
    prior checked_294912
  have h295936 := Scan.chunk_sound context_valid facts instructions 295424 512
    h295424 checked_295424
  have h296448 := Scan.chunk_sound context_valid facts instructions 295936 512
    h295936 checked_295936
  have h296960 := Scan.chunk_sound context_valid facts instructions 296448 512
    h296448 checked_296448
  have h297472 := Scan.chunk_sound context_valid facts instructions 296960 512
    h296960 checked_296960
  have h297984 := Scan.chunk_sound context_valid facts instructions 297472 512
    h297472 checked_297472
  have h298496 := Scan.chunk_sound context_valid facts instructions 297984 512
    h297984 checked_297984
  have h299008 := Scan.chunk_sound context_valid facts instructions 298496 512
    h298496 checked_298496
  have h299520 := Scan.chunk_sound context_valid facts instructions 299008 512
    h299008 checked_299008
  have h300032 := Scan.chunk_sound context_valid facts instructions 299520 512
    h299520 checked_299520
  have h300544 := Scan.chunk_sound context_valid facts instructions 300032 512
    h300032 checked_300032
  have h301056 := Scan.chunk_sound context_valid facts instructions 300544 512
    h300544 checked_300544
  have h301568 := Scan.chunk_sound context_valid facts instructions 301056 512
    h301056 checked_301056
  have h302080 := Scan.chunk_sound context_valid facts instructions 301568 512
    h301568 checked_301568
  have h302592 := Scan.chunk_sound context_valid facts instructions 302080 512
    h302080 checked_302080
  have h303104 := Scan.chunk_sound context_valid facts instructions 302592 512
    h302592 checked_302592
  have h303616 := Scan.chunk_sound context_valid facts instructions 303104 512
    h303104 checked_303104
  have h304128 := Scan.chunk_sound context_valid facts instructions 303616 512
    h303616 checked_303616
  have h304640 := Scan.chunk_sound context_valid facts instructions 304128 512
    h304128 checked_304128
  have h305152 := Scan.chunk_sound context_valid facts instructions 304640 512
    h304640 checked_304640
  have h305664 := Scan.chunk_sound context_valid facts instructions 305152 512
    h305152 checked_305152
  have h306176 := Scan.chunk_sound context_valid facts instructions 305664 512
    h305664 checked_305664
  have h306688 := Scan.chunk_sound context_valid facts instructions 306176 512
    h306176 checked_306176
  have h307200 := Scan.chunk_sound context_valid facts instructions 306688 512
    h306688 checked_306688
  have h307712 := Scan.chunk_sound context_valid facts instructions 307200 512
    h307200 checked_307200
  have h308224 := Scan.chunk_sound context_valid facts instructions 307712 512
    h307712 checked_307712
  have h308736 := Scan.chunk_sound context_valid facts instructions 308224 512
    h308224 checked_308224
  have h309248 := Scan.chunk_sound context_valid facts instructions 308736 512
    h308736 checked_308736
  have h309760 := Scan.chunk_sound context_valid facts instructions 309248 512
    h309248 checked_309248
  have h310272 := Scan.chunk_sound context_valid facts instructions 309760 512
    h309760 checked_309760
  have h310784 := Scan.chunk_sound context_valid facts instructions 310272 512
    h310272 checked_310272
  have h311296 := Scan.chunk_sound context_valid facts instructions 310784 512
    h310784 checked_310784
  exact h311296

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
