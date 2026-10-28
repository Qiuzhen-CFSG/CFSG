module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.CentralInvolutionBounds.Data

/-!
# Initial invariant cells

The equality, adjacency and fixed-point signatures are checked on every letter.
-/
namespace Held.TwoLocalCandidates.CentralInvolutionBounds

open Cores

public theorem invariant00 : Invariant [] weight00 := by
  apply initial_labels_invariant [] weight00 decode00
  apply allLetters
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 8000000 in
    decide +kernel

public theorem invariant10 : Invariant [48] weight10 := by
  apply initial_labels_invariant [48] weight10 decode10
  apply allLetters
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 8000000 in
    decide +kernel

public theorem invariant20 : Invariant [48, 191] weight20 := by
  apply initial_labels_invariant [48, 191] weight20 decode20
  apply allLetters
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 8000000 in
    decide +kernel

public theorem invariant30 : Invariant [48, 191, 877] weight30 := by
  apply initial_labels_invariant [48, 191, 877] weight30 decode30
  apply allLetters
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 8000000 in
    decide +kernel

public theorem invariant40 : Invariant [48, 191, 877, 65] weight40 := by
  apply initial_labels_invariant [48, 191, 877, 65] weight40 decode40
  apply allLetters
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 8000000 in
    decide +kernel

public theorem invariant50 : Invariant [48, 191, 877, 65, 0] weight50 := by
  apply initial_labels_invariant [48, 191, 877, 65, 0] weight50 decode50
  apply allLetters
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 8000000 in
    decide +kernel

public theorem invariant60 : Invariant [48, 191, 877, 65, 0, 1] weight60 := by
  apply initial_labels_invariant [48, 191, 877, 65, 0, 1] weight60 decode60
  apply allLetters
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 8000000 in
    decide +kernel

public theorem invariant70 : Invariant [48, 191, 877, 65, 0, 1, 2] weight70 := by
  apply initial_labels_invariant [48, 191, 877, 65, 0, 1, 2] weight70 decode70
  apply allLetters
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 8000000 in
    decide +kernel

end Held.TwoLocalCandidates.CentralInvolutionBounds
