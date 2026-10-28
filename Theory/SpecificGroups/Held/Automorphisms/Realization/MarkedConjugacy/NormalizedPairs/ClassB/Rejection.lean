module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Checks
import Mathlib.Tactic.FinCases

/-!
# Rejection of every second-class representative

Each of the 11025 actual representatives fails one of the literal source
relators, at each exponent 1 and 3. Every check uses its supplied moved point.
The final block wraps around, so all representatives are checked. Serial
declaration elaboration bounds memory; the measured 128-row rejection sample
used 2.3 GB, including import preparation.

Source: HeG1-P1.M and the HeG1-p2058B0 carrier. The untrusted discovery and
this module's emitter are in `ClassB/Source/`.
-/

namespace Held.Realization.MarkedConjugacy.NormalizedPairs.ClassB

set_option Elab.async false

private def rejectionBlock (start : Nat) : Bool :=
  (List.range 128).all (fun j => decide (RejectedAt
    ⟨(start + j) % 11025, Nat.mod_lt _ (by decide)⟩))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock000 : rejectionBlock 0 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock001 : rejectionBlock 128 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock002 : rejectionBlock 256 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock003 : rejectionBlock 384 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock004 : rejectionBlock 512 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock005 : rejectionBlock 640 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock006 : rejectionBlock 768 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock007 : rejectionBlock 896 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock008 : rejectionBlock 1024 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock009 : rejectionBlock 1152 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock010 : rejectionBlock 1280 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock011 : rejectionBlock 1408 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock012 : rejectionBlock 1536 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock013 : rejectionBlock 1664 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock014 : rejectionBlock 1792 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock015 : rejectionBlock 1920 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock016 : rejectionBlock 2048 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock017 : rejectionBlock 2176 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock018 : rejectionBlock 2304 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock019 : rejectionBlock 2432 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock020 : rejectionBlock 2560 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock021 : rejectionBlock 2688 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock022 : rejectionBlock 2816 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock023 : rejectionBlock 2944 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock024 : rejectionBlock 3072 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock025 : rejectionBlock 3200 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock026 : rejectionBlock 3328 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock027 : rejectionBlock 3456 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock028 : rejectionBlock 3584 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock029 : rejectionBlock 3712 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock030 : rejectionBlock 3840 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock031 : rejectionBlock 3968 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock032 : rejectionBlock 4096 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock033 : rejectionBlock 4224 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock034 : rejectionBlock 4352 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock035 : rejectionBlock 4480 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock036 : rejectionBlock 4608 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock037 : rejectionBlock 4736 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock038 : rejectionBlock 4864 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock039 : rejectionBlock 4992 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock040 : rejectionBlock 5120 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock041 : rejectionBlock 5248 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock042 : rejectionBlock 5376 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock043 : rejectionBlock 5504 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock044 : rejectionBlock 5632 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock045 : rejectionBlock 5760 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock046 : rejectionBlock 5888 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock047 : rejectionBlock 6016 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock048 : rejectionBlock 6144 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock049 : rejectionBlock 6272 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock050 : rejectionBlock 6400 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock051 : rejectionBlock 6528 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock052 : rejectionBlock 6656 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock053 : rejectionBlock 6784 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock054 : rejectionBlock 6912 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock055 : rejectionBlock 7040 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock056 : rejectionBlock 7168 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock057 : rejectionBlock 7296 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock058 : rejectionBlock 7424 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock059 : rejectionBlock 7552 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock060 : rejectionBlock 7680 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock061 : rejectionBlock 7808 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock062 : rejectionBlock 7936 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock063 : rejectionBlock 8064 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock064 : rejectionBlock 8192 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock065 : rejectionBlock 8320 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock066 : rejectionBlock 8448 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock067 : rejectionBlock 8576 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock068 : rejectionBlock 8704 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock069 : rejectionBlock 8832 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock070 : rejectionBlock 8960 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock071 : rejectionBlock 9088 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock072 : rejectionBlock 9216 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock073 : rejectionBlock 9344 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock074 : rejectionBlock 9472 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock075 : rejectionBlock 9600 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock076 : rejectionBlock 9728 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock077 : rejectionBlock 9856 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock078 : rejectionBlock 9984 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock079 : rejectionBlock 10112 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock080 : rejectionBlock 10240 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock081 : rejectionBlock 10368 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock082 : rejectionBlock 10496 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock083 : rejectionBlock 10624 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock084 : rejectionBlock 10752 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock085 : rejectionBlock 10880 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem rejectionBlock086 : rejectionBlock 11008 = true := by
  decide +kernel

/-- Both normalized exponents fail a source relator at every representative. -/
public theorem rejectedAt_all (i : Fin 11025) : RejectedAt i := by
  have h : ∀ j : Fin 87, rejectionBlock (j.val * 128) = true := by
    intro j
    fin_cases j
    · exact rejectionBlock000
    · exact rejectionBlock001
    · exact rejectionBlock002
    · exact rejectionBlock003
    · exact rejectionBlock004
    · exact rejectionBlock005
    · exact rejectionBlock006
    · exact rejectionBlock007
    · exact rejectionBlock008
    · exact rejectionBlock009
    · exact rejectionBlock010
    · exact rejectionBlock011
    · exact rejectionBlock012
    · exact rejectionBlock013
    · exact rejectionBlock014
    · exact rejectionBlock015
    · exact rejectionBlock016
    · exact rejectionBlock017
    · exact rejectionBlock018
    · exact rejectionBlock019
    · exact rejectionBlock020
    · exact rejectionBlock021
    · exact rejectionBlock022
    · exact rejectionBlock023
    · exact rejectionBlock024
    · exact rejectionBlock025
    · exact rejectionBlock026
    · exact rejectionBlock027
    · exact rejectionBlock028
    · exact rejectionBlock029
    · exact rejectionBlock030
    · exact rejectionBlock031
    · exact rejectionBlock032
    · exact rejectionBlock033
    · exact rejectionBlock034
    · exact rejectionBlock035
    · exact rejectionBlock036
    · exact rejectionBlock037
    · exact rejectionBlock038
    · exact rejectionBlock039
    · exact rejectionBlock040
    · exact rejectionBlock041
    · exact rejectionBlock042
    · exact rejectionBlock043
    · exact rejectionBlock044
    · exact rejectionBlock045
    · exact rejectionBlock046
    · exact rejectionBlock047
    · exact rejectionBlock048
    · exact rejectionBlock049
    · exact rejectionBlock050
    · exact rejectionBlock051
    · exact rejectionBlock052
    · exact rejectionBlock053
    · exact rejectionBlock054
    · exact rejectionBlock055
    · exact rejectionBlock056
    · exact rejectionBlock057
    · exact rejectionBlock058
    · exact rejectionBlock059
    · exact rejectionBlock060
    · exact rejectionBlock061
    · exact rejectionBlock062
    · exact rejectionBlock063
    · exact rejectionBlock064
    · exact rejectionBlock065
    · exact rejectionBlock066
    · exact rejectionBlock067
    · exact rejectionBlock068
    · exact rejectionBlock069
    · exact rejectionBlock070
    · exact rejectionBlock071
    · exact rejectionBlock072
    · exact rejectionBlock073
    · exact rejectionBlock074
    · exact rejectionBlock075
    · exact rejectionBlock076
    · exact rejectionBlock077
    · exact rejectionBlock078
    · exact rejectionBlock079
    · exact rejectionBlock080
    · exact rejectionBlock081
    · exact rejectionBlock082
    · exact rejectionBlock083
    · exact rejectionBlock084
    · exact rejectionBlock085
    · exact rejectionBlock086
  have hi := List.all_eq_true.mp (h ⟨i.val / 128, by omega⟩) (i.val % 128)
    (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have he : i.val / 128 * 128 + i.val % 128 = i.val := by omega
  simpa only [he, Nat.mod_eq_of_lt i.isLt, decide_eq_true_eq] using hi

end Held.Realization.MarkedConjugacy.NormalizedPairs.ClassB
