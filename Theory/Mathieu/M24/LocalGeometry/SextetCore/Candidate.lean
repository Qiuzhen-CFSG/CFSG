module
public import Theory.Mathieu.M24.LocalGeometry.EvenCandidates
public import Theory.Mathieu.M24.LocalGeometry.Seed
public import Theory.Mathieu.M24.Properties.Order
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineLifts.CodePreservation

/-!
# A native Sylow marking for the standard sextet

Six commuting involutions from the certified Sylow enumeration generate the
sextet candidate. A decoding certificate distinguishes 64 words by their
images on three points. A native coordinate conjugator, checked on all twelve
Golay rows, places this subgroup and the whole Sylow group at the standard
sextet and its incident standard octad. The candidate fixes each tetrad.

These statements do not assume the candidate is a two-core. Its identification
is proved in the parent `SextetCore` module. Every finite certificate is checked
by Lean's kernel; GAP only finds the coordinate table. Source context:
Aschbacher–Smith H.14, printed pp.396–397; the native Sylow catalogue is in
`EvenCandidates` and `SylowNormalizer.Order`.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.SextetCore
open Subgroup EvenCandidates
open scoped Pointwise

/-- The six commuting involutions for the sextet row of the native Sylow catalogue. -/
noncomputable abbrev candidate : Subgroup M24 := elementary 1

private def word (m : Fin 64) : List (Fin 6) :=
  (List.finRange 6).filter (fun i => m.val.testBit i.val)

private noncomputable def evaluate : List (Fin 6) → M24
  | [] => 1
  | i :: w => generator 1 i * evaluate w

private theorem evaluate_mem (w : List (Fin 6)) : evaluate w ∈ candidate := by
  induction w with
  | nil => exact candidate.one_mem
  | cons i w ih => exact candidate.mul_mem (generator_mem 1 i) ih

private theorem evaluate_apply (w : List (Fin 6)) (x : Fin 24) :
    (evaluate w).val x = evaluatePoint 1 w x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (generator 1 i).val ((evaluate w).val x) = _
    rw [generator_apply, ih]
    rfl

private noncomputable def element (m : Fin 64) : candidate :=
  ⟨evaluate (word m), evaluate_mem _⟩

private def point (m : Fin 64) (x : Fin 24) : Fin 24 := evaluatePoint 1 (word m) x

private theorem element_apply (m : Fin 64) (x : Fin 24) :
    (element m).val.val x = point m x := evaluate_apply _ _

private def decode : Fin 24 → Fin 24 → Fin 24 → Fin 64
  | 0, 1, 5 => 0
  | 11, 1, 7 => 1
  | 9, 1, 5 => 2
  | 8, 1, 7 => 3
  | 11, 20, 5 => 4
  | 0, 20, 7 => 5
  | 8, 20, 5 => 6
  | 9, 20, 7 => 7
  | 8, 22, 17 => 8
  | 9, 22, 10 => 9
  | 11, 22, 17 => 10
  | 0, 22, 10 => 11
  | 9, 2, 17 => 12
  | 8, 2, 10 => 13
  | 0, 2, 17 => 14
  | 11, 2, 10 => 15
  | 0, 1, 7 => 16
  | 11, 1, 5 => 17
  | 9, 1, 7 => 18
  | 8, 1, 5 => 19
  | 11, 20, 7 => 20
  | 0, 20, 5 => 21
  | 8, 20, 7 => 22
  | 9, 20, 5 => 23
  | 8, 22, 10 => 24
  | 9, 22, 17 => 25
  | 11, 22, 10 => 26
  | 0, 22, 17 => 27
  | 9, 2, 10 => 28
  | 8, 2, 17 => 29
  | 0, 2, 10 => 30
  | 11, 2, 17 => 31
  | 0, 22, 5 => 32
  | 11, 22, 7 => 33
  | 9, 22, 5 => 34
  | 8, 22, 7 => 35
  | 11, 2, 5 => 36
  | 0, 2, 7 => 37
  | 8, 2, 5 => 38
  | 9, 2, 7 => 39
  | 8, 1, 17 => 40
  | 9, 1, 10 => 41
  | 11, 1, 17 => 42
  | 0, 1, 10 => 43
  | 9, 20, 17 => 44
  | 8, 20, 10 => 45
  | 0, 20, 17 => 46
  | 11, 20, 10 => 47
  | 0, 22, 7 => 48
  | 11, 22, 5 => 49
  | 9, 22, 7 => 50
  | 8, 22, 5 => 51
  | 11, 2, 7 => 52
  | 0, 2, 5 => 53
  | 8, 2, 7 => 54
  | 9, 2, 5 => 55
  | 8, 1, 10 => 56
  | 9, 1, 17 => 57
  | 11, 1, 10 => 58
  | 0, 1, 17 => 59
  | 9, 20, 10 => 60
  | 8, 20, 17 => 61
  | 0, 20, 10 => 62
  | 11, 20, 17 => 63
  | _, _, _ => 0

private theorem decode_point : ∀ m, decode (point m 0) (point m 1) (point m 5) = m := by
  decide +kernel

private theorem element_injective : Function.Injective element := by
  intro m n h
  have hd := congrArg (fun g : candidate => decode (g.val.val 0) (g.val.val 1) (g.val.val 5)) h
  simpa only [element_apply, decode_point] using hd

/-- Sixty-four distinct words in the native sextet candidate. -/
theorem candidate_card_lower : 64 ≤ Nat.card candidate := by
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective element element_injective


/-- A coordinate permutation found by an untrusted GAP search and certified below. -/
def transportPerm : Equiv.Perm (Fin 24) where
  toFun := ![3,9,19,10,16,7,11,20,2,1,15,0,13,18,5,4,8,12,21,22,14,23,6,17]
  invFun := ![11,9,8,0,15,14,22,5,16,1,3,6,17,12,20,10,4,23,13,2,7,18,19,21]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def transportRowMessage : Fin 12 → Fin 4096 := ![2104,592,2144,320,2352,416,3136,2384,52,2338,2385,368]

private theorem transport_rows : ∀ i,
    m24PermuteMask transportPerm (m24GolayRow i) =
      m24GolayCode (transportRowMessage i) := by decide +kernel

/-- The transporter belongs to the actual native design group. -/
noncomputable def transport : M24 :=
  ⟨transportPerm, by
    apply PairOvergroups.QuotientConstruction.AffineLiftConstruction.mem_M24_of_rows
    intro i
    exact ⟨transportRowMessage i, transport_rows i⟩⟩

/-- The catalogue's elementary candidate, placed at the standard sextet. -/
noncomputable def standardCandidate : Subgroup M24 :=
  candidate.map (MulAut.conj transport).toMonoidHom

/-- The already enumerated order-1024 subgroup as a literal native Sylow group. -/
noncomputable def nativeSylow : Sylow 2 M24 :=
  (IsPGroup.of_card (p := 2) (n := 10) SylowNormalizer.candidate_card).toSylow (by
    have hc := Subgroup.card_mul_index SylowNormalizer.candidate
    rw [SylowNormalizer.candidate_card, m24_order] at hc
    have hi : SylowNormalizer.candidate.index = 239085 := by omega
    rw [hi]
    decide)

theorem nativeSylow_coe : nativeSylow.toSubgroup = SylowNormalizer.candidate := rfl

/-- The whole certified native Sylow group transported with the candidate. -/
noncomputable def standardSylow : Sylow 2 M24 :=
  transport • nativeSylow

theorem standardSylow_coe : standardSylow.toSubgroup =
    SylowNormalizer.candidate.map (MulAut.conj transport).toMonoidHom := rfl

theorem standardCandidate_le_standardSylow : standardCandidate ≤ standardSylow.toSubgroup :=
  Subgroup.map_mono (elementary_le_candidate 1)

/-- The transported full Sylow group stabilizes the actual standard sextet. -/
theorem standardSylow_le_stabilizer : standardSylow.toSubgroup ≤
    sextetStabilizer standardSextet := by
  rw [standardSylow_coe, Subgroup.map_le_iff_le_comap, SylowNormalizer.candidate,
    Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  change (transportPerm * SylowNormalizer.generatorPerm i * transportPerm⁻¹) •
    standardSextet.parts = standardSextet.parts
  revert i
  decide +kernel

/-- This marking also preserves the incident standard octad. -/
theorem standardSylow_le_octadStabilizer : standardSylow.toSubgroup ≤
    octadStabilizer standardOctad := by
  rw [standardSylow_coe, Subgroup.map_le_iff_le_comap, SylowNormalizer.candidate,
    Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  change (transportPerm * SylowNormalizer.generatorPerm i * transportPerm⁻¹) •
    standardOctad.val = standardOctad.val
  revert i
  decide +kernel

theorem standardCandidate_le_stabilizer : standardCandidate ≤ sextetStabilizer standardSextet :=
  standardCandidate_le_standardSylow.trans standardSylow_le_stabilizer

/-- The subgroup fixing each of the six tetrads setwise. -/
noncomputable def partFixers : Subgroup M24 :=
  ⨅ i : Fin 6, MulAction.stabilizer M24 (standardTetrad i)

/-- The elementary candidate fixes all six individual tetrads. -/
theorem standardCandidate_le_partFixers : standardCandidate ≤ partFixers := by
  rw [standardCandidate, Subgroup.map_le_iff_le_comap, candidate, elementary,
    Subgroup.closure_le]
  rintro _ ⟨a, rfl⟩
  apply Subgroup.mem_iInf.mpr
  intro i
  change (transport * generator 1 a * transport⁻¹) • standardTetrad i = standardTetrad i
  change (standardTetrad i).image
    (fun x => (transport * generator 1 a * transport⁻¹).val x) = _
  have he (x : Fin 24) :
      (transport * generator 1 a * transport⁻¹).val x =
      transportPerm (generatorPoint 1 a (transportPerm.symm x)) := by
    change transportPerm ((generator 1 a).val (transportPerm.symm x)) = _
    rw [generator_apply]
  simp only [he]
  clear he
  revert a i
  decide +kernel

theorem standardCandidate_elementary : IsElementaryAbelian 2 standardCandidate :=
  IsElementaryAbelian.map (MulAut.conj transport).toMonoidHom

theorem standardCandidate_card_lower : 64 ≤ Nat.card standardCandidate := by
  rw [standardCandidate, Subgroup.card_map_of_injective (MulAut.conj transport).injective]
  exact candidate_card_lower

/-- Sylow conjugacy uses conjugators in the native M₂₄ carrier. -/
theorem exists_conjugate_standardSylow (S : Sylow 2 M24) :
    ∃ g : M24, standardSylow.toSubgroup.map (MulAut.conj g).toMonoidHom = S.toSubgroup := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M24 standardSylow S
  exact ⟨g, congrArg Sylow.toSubgroup hg⟩

end Sporadic.Mathieu.M24LocalGeometry.SextetCore
