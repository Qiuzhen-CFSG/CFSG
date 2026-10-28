module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Cover.Tables

/-! Kernel-checked path deductions from the literal twenty-two amalgam relations.
No permutation table or untrusted producer supplies a proof rule. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 8192 in
theorem checked_991232 : Path.checkChunk context decode facts instructions 991232 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_991744 : Path.checkChunk context decode facts instructions 991744 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_992256 : Path.checkChunk context decode facts instructions 992256 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_992768 : Path.checkChunk context decode facts instructions 992768 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_993280 : Path.checkChunk context decode facts instructions 993280 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_993792 : Path.checkChunk context decode facts instructions 993792 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_994304 : Path.checkChunk context decode facts instructions 994304 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_994816 : Path.checkChunk context decode facts instructions 994816 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_995328 : Path.checkChunk context decode facts instructions 995328 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_995840 : Path.checkChunk context decode facts instructions 995840 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_996352 : Path.checkChunk context decode facts instructions 996352 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_996864 : Path.checkChunk context decode facts instructions 996864 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_997376 : Path.checkChunk context decode facts instructions 997376 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_997888 : Path.checkChunk context decode facts instructions 997888 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_998400 : Path.checkChunk context decode facts instructions 998400 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem checked_998912 : Path.checkChunk context decode facts instructions 998912 512 = true := by
  decide +kernel

theorem sound_991232 (prior : ∀ n, n < 991232 →
    Holds firstLocal generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 999424 → Holds firstLocal generator (definitions.repr generator) (facts n) := by
  have h991744 := Path.chunk_sound context_valid decode facts instructions 991232 512
    prior checked_991232
  have h992256 := Path.chunk_sound context_valid decode facts instructions 991744 512
    h991744 checked_991744
  have h992768 := Path.chunk_sound context_valid decode facts instructions 992256 512
    h992256 checked_992256
  have h993280 := Path.chunk_sound context_valid decode facts instructions 992768 512
    h992768 checked_992768
  have h993792 := Path.chunk_sound context_valid decode facts instructions 993280 512
    h993280 checked_993280
  have h994304 := Path.chunk_sound context_valid decode facts instructions 993792 512
    h993792 checked_993792
  have h994816 := Path.chunk_sound context_valid decode facts instructions 994304 512
    h994304 checked_994304
  have h995328 := Path.chunk_sound context_valid decode facts instructions 994816 512
    h994816 checked_994816
  have h995840 := Path.chunk_sound context_valid decode facts instructions 995328 512
    h995328 checked_995328
  have h996352 := Path.chunk_sound context_valid decode facts instructions 995840 512
    h995840 checked_995840
  have h996864 := Path.chunk_sound context_valid decode facts instructions 996352 512
    h996352 checked_996352
  have h997376 := Path.chunk_sound context_valid decode facts instructions 996864 512
    h996864 checked_996864
  have h997888 := Path.chunk_sound context_valid decode facts instructions 997376 512
    h997376 checked_997376
  have h998400 := Path.chunk_sound context_valid decode facts instructions 997888 512
    h997888 checked_997888
  have h998912 := Path.chunk_sound context_valid decode facts instructions 998400 512
    h998400 checked_998400
  have h999424 := Path.chunk_sound context_valid decode facts instructions 998912 512
    h998912 checked_998912
  exact h999424

end Sporadic.Janko3.AmalgamPresentation.Cover
