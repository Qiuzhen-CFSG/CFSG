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
theorem checked_311296 : Scan.checkChunk context facts instructions 311296 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_311808 : Scan.checkChunk context facts instructions 311808 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_312320 : Scan.checkChunk context facts instructions 312320 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_312832 : Scan.checkChunk context facts instructions 312832 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_313344 : Scan.checkChunk context facts instructions 313344 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_313856 : Scan.checkChunk context facts instructions 313856 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_314368 : Scan.checkChunk context facts instructions 314368 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_314880 : Scan.checkChunk context facts instructions 314880 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_315392 : Scan.checkChunk context facts instructions 315392 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_315904 : Scan.checkChunk context facts instructions 315904 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_316416 : Scan.checkChunk context facts instructions 316416 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_316928 : Scan.checkChunk context facts instructions 316928 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_317440 : Scan.checkChunk context facts instructions 317440 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_317952 : Scan.checkChunk context facts instructions 317952 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_318464 : Scan.checkChunk context facts instructions 318464 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_318976 : Scan.checkChunk context facts instructions 318976 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_319488 : Scan.checkChunk context facts instructions 319488 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_320000 : Scan.checkChunk context facts instructions 320000 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_320512 : Scan.checkChunk context facts instructions 320512 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_321024 : Scan.checkChunk context facts instructions 321024 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_321536 : Scan.checkChunk context facts instructions 321536 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_322048 : Scan.checkChunk context facts instructions 322048 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_322560 : Scan.checkChunk context facts instructions 322560 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_323072 : Scan.checkChunk context facts instructions 323072 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_323584 : Scan.checkChunk context facts instructions 323584 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_324096 : Scan.checkChunk context facts instructions 324096 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_324608 : Scan.checkChunk context facts instructions 324608 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_325120 : Scan.checkChunk context facts instructions 325120 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_325632 : Scan.checkChunk context facts instructions 325632 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_326144 : Scan.checkChunk context facts instructions 326144 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_326656 : Scan.checkChunk context facts instructions 326656 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_327168 : Scan.checkChunk context facts instructions 327168 512 = true := by
  decide +kernel

theorem all_hold_327680 (prior : ∀ n, n < 311296 → Holds centralizer certGenerator (definitions.repr certGenerator) (facts n)) : ∀ n, n < 327680 →
    Holds centralizer certGenerator (definitions.repr certGenerator) (facts n) := by
  have h311808 := Scan.chunk_sound context_valid facts instructions 311296 512
    prior checked_311296
  have h312320 := Scan.chunk_sound context_valid facts instructions 311808 512
    h311808 checked_311808
  have h312832 := Scan.chunk_sound context_valid facts instructions 312320 512
    h312320 checked_312320
  have h313344 := Scan.chunk_sound context_valid facts instructions 312832 512
    h312832 checked_312832
  have h313856 := Scan.chunk_sound context_valid facts instructions 313344 512
    h313344 checked_313344
  have h314368 := Scan.chunk_sound context_valid facts instructions 313856 512
    h313856 checked_313856
  have h314880 := Scan.chunk_sound context_valid facts instructions 314368 512
    h314368 checked_314368
  have h315392 := Scan.chunk_sound context_valid facts instructions 314880 512
    h314880 checked_314880
  have h315904 := Scan.chunk_sound context_valid facts instructions 315392 512
    h315392 checked_315392
  have h316416 := Scan.chunk_sound context_valid facts instructions 315904 512
    h315904 checked_315904
  have h316928 := Scan.chunk_sound context_valid facts instructions 316416 512
    h316416 checked_316416
  have h317440 := Scan.chunk_sound context_valid facts instructions 316928 512
    h316928 checked_316928
  have h317952 := Scan.chunk_sound context_valid facts instructions 317440 512
    h317440 checked_317440
  have h318464 := Scan.chunk_sound context_valid facts instructions 317952 512
    h317952 checked_317952
  have h318976 := Scan.chunk_sound context_valid facts instructions 318464 512
    h318464 checked_318464
  have h319488 := Scan.chunk_sound context_valid facts instructions 318976 512
    h318976 checked_318976
  have h320000 := Scan.chunk_sound context_valid facts instructions 319488 512
    h319488 checked_319488
  have h320512 := Scan.chunk_sound context_valid facts instructions 320000 512
    h320000 checked_320000
  have h321024 := Scan.chunk_sound context_valid facts instructions 320512 512
    h320512 checked_320512
  have h321536 := Scan.chunk_sound context_valid facts instructions 321024 512
    h321024 checked_321024
  have h322048 := Scan.chunk_sound context_valid facts instructions 321536 512
    h321536 checked_321536
  have h322560 := Scan.chunk_sound context_valid facts instructions 322048 512
    h322048 checked_322048
  have h323072 := Scan.chunk_sound context_valid facts instructions 322560 512
    h322560 checked_322560
  have h323584 := Scan.chunk_sound context_valid facts instructions 323072 512
    h323072 checked_323072
  have h324096 := Scan.chunk_sound context_valid facts instructions 323584 512
    h323584 checked_323584
  have h324608 := Scan.chunk_sound context_valid facts instructions 324096 512
    h324096 checked_324096
  have h325120 := Scan.chunk_sound context_valid facts instructions 324608 512
    h324608 checked_324608
  have h325632 := Scan.chunk_sound context_valid facts instructions 325120 512
    h325120 checked_325120
  have h326144 := Scan.chunk_sound context_valid facts instructions 325632 512
    h325632 checked_325632
  have h326656 := Scan.chunk_sound context_valid facts instructions 326144 512
    h326144 checked_326144
  have h327168 := Scan.chunk_sound context_valid facts instructions 326656 512
    h326656 checked_326656
  have h327680 := Scan.chunk_sound context_valid facts instructions 327168 512
    h327168 checked_327168
  exact h327680

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
