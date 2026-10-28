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
theorem checked_262144 : Scan.checkChunk context facts instructions 262144 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_262656 : Scan.checkChunk context facts instructions 262656 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_263168 : Scan.checkChunk context facts instructions 263168 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_263680 : Scan.checkChunk context facts instructions 263680 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_264192 : Scan.checkChunk context facts instructions 264192 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_264704 : Scan.checkChunk context facts instructions 264704 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_265216 : Scan.checkChunk context facts instructions 265216 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_265728 : Scan.checkChunk context facts instructions 265728 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_266240 : Scan.checkChunk context facts instructions 266240 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_266752 : Scan.checkChunk context facts instructions 266752 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_267264 : Scan.checkChunk context facts instructions 267264 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_267776 : Scan.checkChunk context facts instructions 267776 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_268288 : Scan.checkChunk context facts instructions 268288 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_268800 : Scan.checkChunk context facts instructions 268800 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_269312 : Scan.checkChunk context facts instructions 269312 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_269824 : Scan.checkChunk context facts instructions 269824 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_270336 : Scan.checkChunk context facts instructions 270336 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_270848 : Scan.checkChunk context facts instructions 270848 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_271360 : Scan.checkChunk context facts instructions 271360 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_271872 : Scan.checkChunk context facts instructions 271872 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_272384 : Scan.checkChunk context facts instructions 272384 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_272896 : Scan.checkChunk context facts instructions 272896 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_273408 : Scan.checkChunk context facts instructions 273408 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_273920 : Scan.checkChunk context facts instructions 273920 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_274432 : Scan.checkChunk context facts instructions 274432 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_274944 : Scan.checkChunk context facts instructions 274944 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_275456 : Scan.checkChunk context facts instructions 275456 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_275968 : Scan.checkChunk context facts instructions 275968 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_276480 : Scan.checkChunk context facts instructions 276480 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_276992 : Scan.checkChunk context facts instructions 276992 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_277504 : Scan.checkChunk context facts instructions 277504 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_278016 : Scan.checkChunk context facts instructions 278016 512 = true := by
  decide +kernel

theorem all_hold_278528 (prior : ∀ n, n < 262144 → Holds centralizer certGenerator (definitions.repr certGenerator) (facts n)) : ∀ n, n < 278528 →
    Holds centralizer certGenerator (definitions.repr certGenerator) (facts n) := by
  have h262656 := Scan.chunk_sound context_valid facts instructions 262144 512
    prior checked_262144
  have h263168 := Scan.chunk_sound context_valid facts instructions 262656 512
    h262656 checked_262656
  have h263680 := Scan.chunk_sound context_valid facts instructions 263168 512
    h263168 checked_263168
  have h264192 := Scan.chunk_sound context_valid facts instructions 263680 512
    h263680 checked_263680
  have h264704 := Scan.chunk_sound context_valid facts instructions 264192 512
    h264192 checked_264192
  have h265216 := Scan.chunk_sound context_valid facts instructions 264704 512
    h264704 checked_264704
  have h265728 := Scan.chunk_sound context_valid facts instructions 265216 512
    h265216 checked_265216
  have h266240 := Scan.chunk_sound context_valid facts instructions 265728 512
    h265728 checked_265728
  have h266752 := Scan.chunk_sound context_valid facts instructions 266240 512
    h266240 checked_266240
  have h267264 := Scan.chunk_sound context_valid facts instructions 266752 512
    h266752 checked_266752
  have h267776 := Scan.chunk_sound context_valid facts instructions 267264 512
    h267264 checked_267264
  have h268288 := Scan.chunk_sound context_valid facts instructions 267776 512
    h267776 checked_267776
  have h268800 := Scan.chunk_sound context_valid facts instructions 268288 512
    h268288 checked_268288
  have h269312 := Scan.chunk_sound context_valid facts instructions 268800 512
    h268800 checked_268800
  have h269824 := Scan.chunk_sound context_valid facts instructions 269312 512
    h269312 checked_269312
  have h270336 := Scan.chunk_sound context_valid facts instructions 269824 512
    h269824 checked_269824
  have h270848 := Scan.chunk_sound context_valid facts instructions 270336 512
    h270336 checked_270336
  have h271360 := Scan.chunk_sound context_valid facts instructions 270848 512
    h270848 checked_270848
  have h271872 := Scan.chunk_sound context_valid facts instructions 271360 512
    h271360 checked_271360
  have h272384 := Scan.chunk_sound context_valid facts instructions 271872 512
    h271872 checked_271872
  have h272896 := Scan.chunk_sound context_valid facts instructions 272384 512
    h272384 checked_272384
  have h273408 := Scan.chunk_sound context_valid facts instructions 272896 512
    h272896 checked_272896
  have h273920 := Scan.chunk_sound context_valid facts instructions 273408 512
    h273408 checked_273408
  have h274432 := Scan.chunk_sound context_valid facts instructions 273920 512
    h273920 checked_273920
  have h274944 := Scan.chunk_sound context_valid facts instructions 274432 512
    h274432 checked_274432
  have h275456 := Scan.chunk_sound context_valid facts instructions 274944 512
    h274944 checked_274944
  have h275968 := Scan.chunk_sound context_valid facts instructions 275456 512
    h275456 checked_275456
  have h276480 := Scan.chunk_sound context_valid facts instructions 275968 512
    h275968 checked_275968
  have h276992 := Scan.chunk_sound context_valid facts instructions 276480 512
    h276480 checked_276480
  have h277504 := Scan.chunk_sound context_valid facts instructions 276992 512
    h276992 checked_276992
  have h278016 := Scan.chunk_sound context_valid facts instructions 277504 512
    h277504 checked_277504
  have h278528 := Scan.chunk_sound context_valid facts instructions 278016 512
    h278016 checked_278016
  exact h278528

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
