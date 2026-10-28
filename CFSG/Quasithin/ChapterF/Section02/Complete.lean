module

public import CFSG.Quasithin.ChapterF.Section02.RepairedExtension

/-!
# Assembled amalgam and automorphism results

This interface exports the results of Aschbacher–Smith §F.2 used by the later
amalgam arguments: universal completion existence, equivalence and kernel
criteria, automorphism descent, and the repaired extension theorem.

For F.2.11 use `YAmalgam.NormalIn.repairedExtension`, or its finite two-local
specialization `repairedExtension_of_index_le_two` for F.4.23(5). The latter
constructs a faithful completion of the larger amalgam from source conditions
(a)–(f) and the local Sylow, index-at-most-two, and center conditions. It also
proves faithfulness of the inner restriction and equivalence with the original
completion when its group is centerless. `conjugation_mem_kernelStabilizer`
converts the source's invariance of a completion class to the descent input.

The unrestricted printed F.2.11 is false: see the separately importable
`Section02.Obstruction`. No assertion of the false version is exported here.
-/
