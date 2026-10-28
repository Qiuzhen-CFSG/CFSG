module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionLocalCommutant.Kernel.Data

/-!
# The distinguished columns of the kernel certificate

The annihilator kills the seed; the last two columns of its augmented inverse
are the seed and `3 e₀ + 4 T e₀`. Closed checks use packed natural-number digits.
Source and candidate generation: `Kernel/source/GenerateKernel.py`.
-/

namespace Lyons.SimplicityCertificate.LocalCommutant.Kernel
open Atlas111WordCertificate
open Matrix
set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem zero_check : allRows (fun i => digit (rRows i) 0 == 0) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seed_check :
    allRows (fun i => digit (dRows i) 109 == (if i = 0 then 1 else 0)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem t_check :
    allRows (fun i => digit (dRows i) 110 ==
      (3 * (if i = 0 then 1 else 0) + 4 * digit (ab7Rows i) 0) % 5) = true := by
  decide +kernel

private theorem cast_delta (i : Fin 111) :
    ((if i = 0 then 1 else 0 : ℕ) : ZMod 5) = (localSeed (n := 111) (K := ZMod 5)) i := by
  by_cases h : i = 0 <;> simp [h, localSeed]

public theorem annihilates_seed : rMatrix *ᵥ (localSeed (n := 111) (K := ZMod 5)) = 0 := by
  funext i
  simp only [localSeed, mulVec_single_one, col_apply]
  change (digit (rRows i) 0 : ZMod 5) = 0
  rw [beq_iff_eq.mp (allRows_sound zero_check i), Nat.cast_zero]

public theorem inverse_seed_column : (fun i => dMatrix i 109) =
    (localSeed (n := 111) (K := ZMod 5)) := by
  funext i
  change (digit (dRows i) 109 : ZMod 5) = _
  rw [beq_iff_eq.mp (allRows_sound seed_check i)]
  exact cast_delta i

public theorem inverse_t_column : (fun i => dMatrix i 110) =
    (3 : ZMod 5) • (localSeed (n := 111) (K := ZMod 5)) +
      (4 : ZMod 5) • (ab7Matrix *ᵥ (localSeed (n := 111) (K := ZMod 5))) := by
  funext i
  change (digit (dRows i) 110 : ZMod 5) = _
  rw [beq_iff_eq.mp (allRows_sound t_check i), ZMod.natCast_mod]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, cast_delta,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [localSeed, mulVec_single_one, col_apply]
  rfl

end Lyons.SimplicityCertificate.LocalCommutant.Kernel
