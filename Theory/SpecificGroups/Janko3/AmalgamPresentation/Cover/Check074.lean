module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_606208 : Path.checkChunk context decode facts instructions 606208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_606720 : Path.checkChunk context decode facts instructions 606720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_607232 : Path.checkChunk context decode facts instructions 607232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_607744 : Path.checkChunk context decode facts instructions 607744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_608256 : Path.checkChunk context decode facts instructions 608256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_608768 : Path.checkChunk context decode facts instructions 608768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_609280 : Path.checkChunk context decode facts instructions 609280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_609792 : Path.checkChunk context decode facts instructions 609792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_610304 : Path.checkChunk context decode facts instructions 610304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_610816 : Path.checkChunk context decode facts instructions 610816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_611328 : Path.checkChunk context decode facts instructions 611328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_611840 : Path.checkChunk context decode facts instructions 611840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_612352 : Path.checkChunk context decode facts instructions 612352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_612864 : Path.checkChunk context decode facts instructions 612864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_613376 : Path.checkChunk context decode facts instructions 613376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_613888 : Path.checkChunk context decode facts instructions 613888 512 = true := by
  decide +kernel

theorem sound_606208 (prior : ∀ n, n < 606208 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 614400 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h606720 := Path.chunk_sound context_valid decode facts instructions 606208 512
    prior checked_606208
  have h607232 := Path.chunk_sound context_valid decode facts instructions 606720 512
    h606720 checked_606720
  have h607744 := Path.chunk_sound context_valid decode facts instructions 607232 512
    h607232 checked_607232
  have h608256 := Path.chunk_sound context_valid decode facts instructions 607744 512
    h607744 checked_607744
  have h608768 := Path.chunk_sound context_valid decode facts instructions 608256 512
    h608256 checked_608256
  have h609280 := Path.chunk_sound context_valid decode facts instructions 608768 512
    h608768 checked_608768
  have h609792 := Path.chunk_sound context_valid decode facts instructions 609280 512
    h609280 checked_609280
  have h610304 := Path.chunk_sound context_valid decode facts instructions 609792 512
    h609792 checked_609792
  have h610816 := Path.chunk_sound context_valid decode facts instructions 610304 512
    h610304 checked_610304
  have h611328 := Path.chunk_sound context_valid decode facts instructions 610816 512
    h610816 checked_610816
  have h611840 := Path.chunk_sound context_valid decode facts instructions 611328 512
    h611328 checked_611328
  have h612352 := Path.chunk_sound context_valid decode facts instructions 611840 512
    h611840 checked_611840
  have h612864 := Path.chunk_sound context_valid decode facts instructions 612352 512
    h612352 checked_612352
  have h613376 := Path.chunk_sound context_valid decode facts instructions 612864 512
    h612864 checked_612864
  have h613888 := Path.chunk_sound context_valid decode facts instructions 613376 512
    h613376 checked_613376
  have h614400 := Path.chunk_sound context_valid decode facts instructions 613888 512
    h613888 checked_613888
  exact h614400

end Sporadic.Janko3.AmalgamPresentation.Cover
