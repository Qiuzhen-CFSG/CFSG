module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_139264 : Path.checkChunk context decode facts instructions 139264 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_139776 : Path.checkChunk context decode facts instructions 139776 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_140288 : Path.checkChunk context decode facts instructions 140288 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_140800 : Path.checkChunk context decode facts instructions 140800 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_141312 : Path.checkChunk context decode facts instructions 141312 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_141824 : Path.checkChunk context decode facts instructions 141824 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_142336 : Path.checkChunk context decode facts instructions 142336 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_142848 : Path.checkChunk context decode facts instructions 142848 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_143360 : Path.checkChunk context decode facts instructions 143360 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_143872 : Path.checkChunk context decode facts instructions 143872 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_144384 : Path.checkChunk context decode facts instructions 144384 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_144896 : Path.checkChunk context decode facts instructions 144896 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_145408 : Path.checkChunk context decode facts instructions 145408 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_145920 : Path.checkChunk context decode facts instructions 145920 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_146432 : Path.checkChunk context decode facts instructions 146432 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_146944 : Path.checkChunk context decode facts instructions 146944 512 = true := by
  decide +kernel

theorem sound_139264 (prior : ∀ n, n < 139264 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 147456 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h139776 := Path.chunk_sound context_valid decode facts instructions 139264 512
    prior checked_139264
  have h140288 := Path.chunk_sound context_valid decode facts instructions 139776 512
    h139776 checked_139776
  have h140800 := Path.chunk_sound context_valid decode facts instructions 140288 512
    h140288 checked_140288
  have h141312 := Path.chunk_sound context_valid decode facts instructions 140800 512
    h140800 checked_140800
  have h141824 := Path.chunk_sound context_valid decode facts instructions 141312 512
    h141312 checked_141312
  have h142336 := Path.chunk_sound context_valid decode facts instructions 141824 512
    h141824 checked_141824
  have h142848 := Path.chunk_sound context_valid decode facts instructions 142336 512
    h142336 checked_142336
  have h143360 := Path.chunk_sound context_valid decode facts instructions 142848 512
    h142848 checked_142848
  have h143872 := Path.chunk_sound context_valid decode facts instructions 143360 512
    h143360 checked_143360
  have h144384 := Path.chunk_sound context_valid decode facts instructions 143872 512
    h143872 checked_143872
  have h144896 := Path.chunk_sound context_valid decode facts instructions 144384 512
    h144384 checked_144384
  have h145408 := Path.chunk_sound context_valid decode facts instructions 144896 512
    h144896 checked_144896
  have h145920 := Path.chunk_sound context_valid decode facts instructions 145408 512
    h145408 checked_145408
  have h146432 := Path.chunk_sound context_valid decode facts instructions 145920 512
    h145920 checked_145920
  have h146944 := Path.chunk_sound context_valid decode facts instructions 146432 512
    h146432 checked_146432
  have h147456 := Path.chunk_sound context_valid decode facts instructions 146944 512
    h146944 checked_146944
  exact h147456

end Sporadic.Janko3.AmalgamPresentation.Cover
