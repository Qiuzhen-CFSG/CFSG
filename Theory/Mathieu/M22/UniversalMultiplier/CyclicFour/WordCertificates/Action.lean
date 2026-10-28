module

public import Theory.Mathieu.M22.UniversalMultiplier.CyclicFour.WordCertificates.Tables

/-!
# The lookup actions are the published ATLAS permutations

For each generator, sorting its cycle entries together with its fixed points
certifies a partition of all 4928 points. The kernel checks the lookup action
on each short cycle. The partition theorem then identifies that action with
the original product of cycles in `Data.lean`, including the original cycle
orientation and the conversion from labels 1,...,4928 to 0,...,4927.

Source: retained ATLAS representation `4M22G1-p4928aB0`, as attributed in
`../source/README.md`; application to Aschbacher–Smith I.1.3(4).
-/

namespace Sporadic.Mathieu.M22CyclicFour.WordCertificates

-- The depth allowance accommodates the literal lists of 4928 entries.
set_option maxRecDepth 20000 in
private theorem a_partition_checked : (sort 13 aPartition.flatten == List.range 4928) = true := by
  decide +kernel

set_option maxRecDepth 20000 in
private theorem b_partition_checked : (sort 13 bPartition.flatten == List.range 4928) = true := by
  decide +kernel

set_option maxRecDepth 20000 in
private theorem a_cycles_checked : cycleCheck aPartition (action a) = true := by
  decide +kernel

set_option maxRecDepth 20000 in
private theorem b_cycles_checked : cycleCheck bPartition (action b) = true := by
  decide +kernel

public theorem a_apply (x : Fin 4928) : Data.aPerm x = action a x := by
  have h := action_of_checks aPartition (action a) (eq_of_beq a_partition_checked)
    a_cycles_checked x
  rw [aPartition, ofCycles_append_fixed] at h
  exact h

public theorem b_apply (x : Fin 4928) : Data.bPerm x = action b x := by
  have h := action_of_checks bPartition (action b) (eq_of_beq b_partition_checked)
    b_cycles_checked x
  rw [bPartition, ofCycles_append_fixed] at h
  exact h

end Sporadic.Mathieu.M22CyclicFour.WordCertificates
