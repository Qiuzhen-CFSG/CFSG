module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.PermutationData

/-!
# All-letter certificates for the Held Bray word

The blocks identify the fast permutation with the actual Held word on
all 2058 letters. Sequential checking bounds memory independently of the
number of blocks. The assembly theorem is in the parent module.
Source: the ATLAS HeG1-p2058B0 tables; reproduced by `Source/generate.py`.
-/

namespace Held.OuterInvolution.FixedStructure.PermutationCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_0 : ∀ r : Fin 16,
    representation bray ⟨(0 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(0 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_1 : ∀ r : Fin 16,
    representation bray ⟨(1 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(1 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_2 : ∀ r : Fin 16,
    representation bray ⟨(2 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(2 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_3 : ∀ r : Fin 16,
    representation bray ⟨(3 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(3 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_4 : ∀ r : Fin 16,
    representation bray ⟨(4 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(4 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_5 : ∀ r : Fin 16,
    representation bray ⟨(5 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(5 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_6 : ∀ r : Fin 16,
    representation bray ⟨(6 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(6 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_7 : ∀ r : Fin 16,
    representation bray ⟨(7 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(7 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_8 : ∀ r : Fin 16,
    representation bray ⟨(8 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(8 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_9 : ∀ r : Fin 16,
    representation bray ⟨(9 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(9 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_10 : ∀ r : Fin 16,
    representation bray ⟨(10 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(10 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_11 : ∀ r : Fin 16,
    representation bray ⟨(11 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(11 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_12 : ∀ r : Fin 16,
    representation bray ⟨(12 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(12 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_13 : ∀ r : Fin 16,
    representation bray ⟨(13 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(13 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_14 : ∀ r : Fin 16,
    representation bray ⟨(14 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(14 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_15 : ∀ r : Fin 16,
    representation bray ⟨(15 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(15 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_16 : ∀ r : Fin 16,
    representation bray ⟨(16 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(16 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_17 : ∀ r : Fin 16,
    representation bray ⟨(17 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(17 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_18 : ∀ r : Fin 16,
    representation bray ⟨(18 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(18 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_19 : ∀ r : Fin 16,
    representation bray ⟨(19 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(19 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_20 : ∀ r : Fin 16,
    representation bray ⟨(20 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(20 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_21 : ∀ r : Fin 16,
    representation bray ⟨(21 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(21 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_22 : ∀ r : Fin 16,
    representation bray ⟨(22 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(22 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_23 : ∀ r : Fin 16,
    representation bray ⟨(23 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(23 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_24 : ∀ r : Fin 16,
    representation bray ⟨(24 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(24 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_25 : ∀ r : Fin 16,
    representation bray ⟨(25 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(25 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_26 : ∀ r : Fin 16,
    representation bray ⟨(26 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(26 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_27 : ∀ r : Fin 16,
    representation bray ⟨(27 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(27 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_28 : ∀ r : Fin 16,
    representation bray ⟨(28 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(28 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_29 : ∀ r : Fin 16,
    representation bray ⟨(29 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(29 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_30 : ∀ r : Fin 16,
    representation bray ⟨(30 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(30 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_31 : ∀ r : Fin 16,
    representation bray ⟨(31 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(31 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_32 : ∀ r : Fin 16,
    representation bray ⟨(32 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(32 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_33 : ∀ r : Fin 16,
    representation bray ⟨(33 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(33 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_34 : ∀ r : Fin 16,
    representation bray ⟨(34 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(34 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_35 : ∀ r : Fin 16,
    representation bray ⟨(35 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(35 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_36 : ∀ r : Fin 16,
    representation bray ⟨(36 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(36 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_37 : ∀ r : Fin 16,
    representation bray ⟨(37 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(37 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_38 : ∀ r : Fin 16,
    representation bray ⟨(38 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(38 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_39 : ∀ r : Fin 16,
    representation bray ⟨(39 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(39 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_40 : ∀ r : Fin 16,
    representation bray ⟨(40 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(40 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_41 : ∀ r : Fin 16,
    representation bray ⟨(41 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(41 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_42 : ∀ r : Fin 16,
    representation bray ⟨(42 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(42 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_43 : ∀ r : Fin 16,
    representation bray ⟨(43 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(43 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_44 : ∀ r : Fin 16,
    representation bray ⟨(44 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(44 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_45 : ∀ r : Fin 16,
    representation bray ⟨(45 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(45 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_46 : ∀ r : Fin 16,
    representation bray ⟨(46 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(46 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_47 : ∀ r : Fin 16,
    representation bray ⟨(47 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(47 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_48 : ∀ r : Fin 16,
    representation bray ⟨(48 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(48 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_49 : ∀ r : Fin 16,
    representation bray ⟨(49 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(49 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_50 : ∀ r : Fin 16,
    representation bray ⟨(50 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(50 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_51 : ∀ r : Fin 16,
    representation bray ⟨(51 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(51 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_52 : ∀ r : Fin 16,
    representation bray ⟨(52 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(52 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_53 : ∀ r : Fin 16,
    representation bray ⟨(53 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(53 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_54 : ∀ r : Fin 16,
    representation bray ⟨(54 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(54 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_55 : ∀ r : Fin 16,
    representation bray ⟨(55 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(55 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_56 : ∀ r : Fin 16,
    representation bray ⟨(56 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(56 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_57 : ∀ r : Fin 16,
    representation bray ⟨(57 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(57 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_58 : ∀ r : Fin 16,
    representation bray ⟨(58 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(58 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_59 : ∀ r : Fin 16,
    representation bray ⟨(59 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(59 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_60 : ∀ r : Fin 16,
    representation bray ⟨(60 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(60 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_61 : ∀ r : Fin 16,
    representation bray ⟨(61 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(61 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_62 : ∀ r : Fin 16,
    representation bray ⟨(62 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(62 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_63 : ∀ r : Fin 16,
    representation bray ⟨(63 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(63 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_64 : ∀ r : Fin 16,
    representation bray ⟨(64 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(64 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_65 : ∀ r : Fin 16,
    representation bray ⟨(65 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(65 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_66 : ∀ r : Fin 16,
    representation bray ⟨(66 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(66 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_67 : ∀ r : Fin 16,
    representation bray ⟨(67 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(67 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_68 : ∀ r : Fin 16,
    representation bray ⟨(68 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(68 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_69 : ∀ r : Fin 16,
    representation bray ⟨(69 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(69 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_70 : ∀ r : Fin 16,
    representation bray ⟨(70 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(70 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_71 : ∀ r : Fin 16,
    representation bray ⟨(71 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(71 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_72 : ∀ r : Fin 16,
    representation bray ⟨(72 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(72 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_73 : ∀ r : Fin 16,
    representation bray ⟨(73 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(73 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_74 : ∀ r : Fin 16,
    representation bray ⟨(74 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(74 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_75 : ∀ r : Fin 16,
    representation bray ⟨(75 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(75 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_76 : ∀ r : Fin 16,
    representation bray ⟨(76 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(76 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_77 : ∀ r : Fin 16,
    representation bray ⟨(77 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(77 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_78 : ∀ r : Fin 16,
    representation bray ⟨(78 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(78 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_79 : ∀ r : Fin 16,
    representation bray ⟨(79 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(79 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_80 : ∀ r : Fin 16,
    representation bray ⟨(80 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(80 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_81 : ∀ r : Fin 16,
    representation bray ⟨(81 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(81 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_82 : ∀ r : Fin 16,
    representation bray ⟨(82 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(82 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_83 : ∀ r : Fin 16,
    representation bray ⟨(83 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(83 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_84 : ∀ r : Fin 16,
    representation bray ⟨(84 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(84 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_85 : ∀ r : Fin 16,
    representation bray ⟨(85 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(85 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_86 : ∀ r : Fin 16,
    representation bray ⟨(86 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(86 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_87 : ∀ r : Fin 16,
    representation bray ⟨(87 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(87 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_88 : ∀ r : Fin 16,
    representation bray ⟨(88 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(88 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_89 : ∀ r : Fin 16,
    representation bray ⟨(89 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(89 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_90 : ∀ r : Fin 16,
    representation bray ⟨(90 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(90 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_91 : ∀ r : Fin 16,
    representation bray ⟨(91 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(91 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_92 : ∀ r : Fin 16,
    representation bray ⟨(92 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(92 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_93 : ∀ r : Fin 16,
    representation bray ⟨(93 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(93 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_94 : ∀ r : Fin 16,
    representation bray ⟨(94 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(94 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_95 : ∀ r : Fin 16,
    representation bray ⟨(95 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(95 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_96 : ∀ r : Fin 16,
    representation bray ⟨(96 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(96 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_97 : ∀ r : Fin 16,
    representation bray ⟨(97 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(97 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_98 : ∀ r : Fin 16,
    representation bray ⟨(98 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(98 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_99 : ∀ r : Fin 16,
    representation bray ⟨(99 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(99 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_100 : ∀ r : Fin 16,
    representation bray ⟨(100 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(100 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_101 : ∀ r : Fin 16,
    representation bray ⟨(101 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(101 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_102 : ∀ r : Fin 16,
    representation bray ⟨(102 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(102 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_103 : ∀ r : Fin 16,
    representation bray ⟨(103 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(103 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_104 : ∀ r : Fin 16,
    representation bray ⟨(104 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(104 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_105 : ∀ r : Fin 16,
    representation bray ⟨(105 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(105 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_106 : ∀ r : Fin 16,
    representation bray ⟨(106 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(106 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_107 : ∀ r : Fin 16,
    representation bray ⟨(107 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(107 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_108 : ∀ r : Fin 16,
    representation bray ⟨(108 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(108 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_109 : ∀ r : Fin 16,
    representation bray ⟨(109 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(109 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_110 : ∀ r : Fin 16,
    representation bray ⟨(110 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(110 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_111 : ∀ r : Fin 16,
    representation bray ⟨(111 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(111 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_112 : ∀ r : Fin 16,
    representation bray ⟨(112 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(112 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_113 : ∀ r : Fin 16,
    representation bray ⟨(113 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(113 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_114 : ∀ r : Fin 16,
    representation bray ⟨(114 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(114 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_115 : ∀ r : Fin 16,
    representation bray ⟨(115 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(115 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_116 : ∀ r : Fin 16,
    representation bray ⟨(116 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(116 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_117 : ∀ r : Fin 16,
    representation bray ⟨(117 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(117 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_118 : ∀ r : Fin 16,
    representation bray ⟨(118 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(118 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_119 : ∀ r : Fin 16,
    representation bray ⟨(119 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(119 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_120 : ∀ r : Fin 16,
    representation bray ⟨(120 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(120 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_121 : ∀ r : Fin 16,
    representation bray ⟨(121 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(121 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_122 : ∀ r : Fin 16,
    representation bray ⟨(122 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(122 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_123 : ∀ r : Fin 16,
    representation bray ⟨(123 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(123 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_124 : ∀ r : Fin 16,
    representation bray ⟨(124 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(124 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_125 : ∀ r : Fin 16,
    representation bray ⟨(125 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(125 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_126 : ∀ r : Fin 16,
    representation bray ⟨(126 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(126 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_127 : ∀ r : Fin 16,
    representation bray ⟨(127 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(127 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
public theorem bray_eq_128 : ∀ r : Fin 16,
    representation bray ⟨(128 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ = brayPermutation ⟨(128 * 16 + r.val) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  decide +kernel

end Held.OuterInvolution.FixedStructure.PermutationCertificate
