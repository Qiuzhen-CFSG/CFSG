module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_344064 : Path.checkChunk context decode facts instructions 344064 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_344576 : Path.checkChunk context decode facts instructions 344576 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_345088 : Path.checkChunk context decode facts instructions 345088 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_345600 : Path.checkChunk context decode facts instructions 345600 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_346112 : Path.checkChunk context decode facts instructions 346112 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_346624 : Path.checkChunk context decode facts instructions 346624 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_347136 : Path.checkChunk context decode facts instructions 347136 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_347648 : Path.checkChunk context decode facts instructions 347648 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_348160 : Path.checkChunk context decode facts instructions 348160 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_348672 : Path.checkChunk context decode facts instructions 348672 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_349184 : Path.checkChunk context decode facts instructions 349184 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_349696 : Path.checkChunk context decode facts instructions 349696 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_350208 : Path.checkChunk context decode facts instructions 350208 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_350720 : Path.checkChunk context decode facts instructions 350720 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_351232 : Path.checkChunk context decode facts instructions 351232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_351744 : Path.checkChunk context decode facts instructions 351744 512 = true := by
  decide +kernel

theorem sound_344064 (prior : ∀ n, n < 344064 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 352256 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h344576 := Path.chunk_sound context_valid decode facts instructions 344064 512
    prior checked_344064
  have h345088 := Path.chunk_sound context_valid decode facts instructions 344576 512
    h344576 checked_344576
  have h345600 := Path.chunk_sound context_valid decode facts instructions 345088 512
    h345088 checked_345088
  have h346112 := Path.chunk_sound context_valid decode facts instructions 345600 512
    h345600 checked_345600
  have h346624 := Path.chunk_sound context_valid decode facts instructions 346112 512
    h346112 checked_346112
  have h347136 := Path.chunk_sound context_valid decode facts instructions 346624 512
    h346624 checked_346624
  have h347648 := Path.chunk_sound context_valid decode facts instructions 347136 512
    h347136 checked_347136
  have h348160 := Path.chunk_sound context_valid decode facts instructions 347648 512
    h347648 checked_347648
  have h348672 := Path.chunk_sound context_valid decode facts instructions 348160 512
    h348160 checked_348160
  have h349184 := Path.chunk_sound context_valid decode facts instructions 348672 512
    h348672 checked_348672
  have h349696 := Path.chunk_sound context_valid decode facts instructions 349184 512
    h349184 checked_349184
  have h350208 := Path.chunk_sound context_valid decode facts instructions 349696 512
    h349696 checked_349696
  have h350720 := Path.chunk_sound context_valid decode facts instructions 350208 512
    h350208 checked_350208
  have h351232 := Path.chunk_sound context_valid decode facts instructions 350720 512
    h350720 checked_350720
  have h351744 := Path.chunk_sound context_valid decode facts instructions 351232 512
    h351232 checked_351232
  have h352256 := Path.chunk_sound context_valid decode facts instructions 351744 512
    h351744 checked_351744
  exact h352256

end Sporadic.Janko3.AmalgamPresentation.Cover
