module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_1425408 : Path.checkChunk context decode facts instructions 1425408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1425920 : Path.checkChunk context decode facts instructions 1425920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1426432 : Path.checkChunk context decode facts instructions 1426432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1426944 : Path.checkChunk context decode facts instructions 1426944 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1427456 : Path.checkChunk context decode facts instructions 1427456 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1427968 : Path.checkChunk context decode facts instructions 1427968 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1428480 : Path.checkChunk context decode facts instructions 1428480 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1428992 : Path.checkChunk context decode facts instructions 1428992 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1429504 : Path.checkChunk context decode facts instructions 1429504 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1430016 : Path.checkChunk context decode facts instructions 1430016 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1430528 : Path.checkChunk context decode facts instructions 1430528 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1431040 : Path.checkChunk context decode facts instructions 1431040 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1431552 : Path.checkChunk context decode facts instructions 1431552 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1432064 : Path.checkChunk context decode facts instructions 1432064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1432576 : Path.checkChunk context decode facts instructions 1432576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_1433088 : Path.checkChunk context decode facts instructions 1433088 512 = true := by
  decide +kernel

theorem sound_1425408 (prior : ∀ n, n < 1425408 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 1433600 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h1425920 := Path.chunk_sound context_valid decode facts instructions 1425408 512
    prior checked_1425408
  have h1426432 := Path.chunk_sound context_valid decode facts instructions 1425920 512
    h1425920 checked_1425920
  have h1426944 := Path.chunk_sound context_valid decode facts instructions 1426432 512
    h1426432 checked_1426432
  have h1427456 := Path.chunk_sound context_valid decode facts instructions 1426944 512
    h1426944 checked_1426944
  have h1427968 := Path.chunk_sound context_valid decode facts instructions 1427456 512
    h1427456 checked_1427456
  have h1428480 := Path.chunk_sound context_valid decode facts instructions 1427968 512
    h1427968 checked_1427968
  have h1428992 := Path.chunk_sound context_valid decode facts instructions 1428480 512
    h1428480 checked_1428480
  have h1429504 := Path.chunk_sound context_valid decode facts instructions 1428992 512
    h1428992 checked_1428992
  have h1430016 := Path.chunk_sound context_valid decode facts instructions 1429504 512
    h1429504 checked_1429504
  have h1430528 := Path.chunk_sound context_valid decode facts instructions 1430016 512
    h1430016 checked_1430016
  have h1431040 := Path.chunk_sound context_valid decode facts instructions 1430528 512
    h1430528 checked_1430528
  have h1431552 := Path.chunk_sound context_valid decode facts instructions 1431040 512
    h1431040 checked_1431040
  have h1432064 := Path.chunk_sound context_valid decode facts instructions 1431552 512
    h1431552 checked_1431552
  have h1432576 := Path.chunk_sound context_valid decode facts instructions 1432064 512
    h1432064 checked_1432064
  have h1433088 := Path.chunk_sound context_valid decode facts instructions 1432576 512
    h1432576 checked_1432576
  have h1433600 := Path.chunk_sound context_valid decode facts instructions 1433088 512
    h1433088 checked_1433088
  exact h1433600

end Sporadic.Janko3.AmalgamPresentation.Cover
