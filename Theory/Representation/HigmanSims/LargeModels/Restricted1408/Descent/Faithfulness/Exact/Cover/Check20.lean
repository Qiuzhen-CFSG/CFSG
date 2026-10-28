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
theorem checked_327680 : Scan.checkChunk context facts instructions 327680 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_328192 : Scan.checkChunk context facts instructions 328192 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_328704 : Scan.checkChunk context facts instructions 328704 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_329216 : Scan.checkChunk context facts instructions 329216 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_329728 : Scan.checkChunk context facts instructions 329728 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_330240 : Scan.checkChunk context facts instructions 330240 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_330752 : Scan.checkChunk context facts instructions 330752 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_331264 : Scan.checkChunk context facts instructions 331264 512 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_331776 : Scan.checkChunk context facts instructions 331776 213 = true := by
  decide +kernel

theorem all_hold_331989 (prior : ∀ n, n < 327680 → Holds centralizer certGenerator (definitions.repr certGenerator) (facts n)) : ∀ n, n < 331989 →
    Holds centralizer certGenerator (definitions.repr certGenerator) (facts n) := by
  have h328192 := Scan.chunk_sound context_valid facts instructions 327680 512
    prior checked_327680
  have h328704 := Scan.chunk_sound context_valid facts instructions 328192 512
    h328192 checked_328192
  have h329216 := Scan.chunk_sound context_valid facts instructions 328704 512
    h328704 checked_328704
  have h329728 := Scan.chunk_sound context_valid facts instructions 329216 512
    h329216 checked_329216
  have h330240 := Scan.chunk_sound context_valid facts instructions 329728 512
    h329728 checked_329728
  have h330752 := Scan.chunk_sound context_valid facts instructions 330240 512
    h330240 checked_330240
  have h331264 := Scan.chunk_sound context_valid facts instructions 330752 512
    h330752 checked_330752
  have h331776 := Scan.chunk_sound context_valid facts instructions 331264 512
    h331264 checked_331264
  have h331989 := Scan.chunk_sound context_valid facts instructions 331776 213
    h331776 checked_331776
  exact h331989

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
