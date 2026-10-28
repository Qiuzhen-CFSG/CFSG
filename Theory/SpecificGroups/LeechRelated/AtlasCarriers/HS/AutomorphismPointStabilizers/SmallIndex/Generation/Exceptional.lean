module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation.Support
public import Mathlib.GroupTheory.Index

/-!
# The exceptional subgroup and 101 distinct cosets

Words in the two exceptional generators recover the normalizing element and
representative 1. The same generators preserve a specified 11-point set.
We exhibit 101 translates separated by nine Boolean coordinates, proving
that the exceptional subgroup has index greater than 100 inside the certified
stabilizer. All finite checks reduce in the kernel; neither an order calculation
nor a PSL₂(11) identification is assumed.
Source context: GLS3 Table 5.3m, p.274; Aschbacher–Smith p.510.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.SmallIndex.GenerationCertificate
open Theory.GroupTheory Subgroup
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem normalizer_word : pairWord 1 [0, 2, 2, 1, 3, 0, 3] = normalizerElement := by
  apply Subtype.ext
  apply Equiv.ext
  apply OrderCertificate.allFin
  decide +kernel

theorem representative_one_word : pairWord 1 [1, 3, 0, 2, 1, 3] = representative 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply OrderCertificate.allFin
  decide +kernel

def color (x : Fin 100) : Bool :=
  (2475881406736334685881765392 >>> x.val) % 2 == 1

def colorStabilizer : Subgroup CertifiedStabilizer where
  carrier := {g | ∀ x, color ((g : Equiv.Perm (Fin 100)) x) = color x}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro a b ha hb x
    exact (ha ((b : Equiv.Perm (Fin 100)) x)).trans (hb x)
  inv_mem' := by
    intro a ha x
    have h := ha ((a : Equiv.Perm (Fin 100))⁻¹ x)
    simpa only [Subgroup.coe_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using h.symm

theorem exceptional_le_colorStabilizer : exceptionalSubgroup ≤ colorStabilizer := by
  apply sup_le
  · apply zpowers_le.mpr
    change ∀ x, color ((elevenElement : Equiv.Perm (Fin 100)) x) = color x
    apply OrderCertificate.allFin
    decide +kernel
  · rw [primeSubgroup, MonoidHom.map_zpowers]
    apply zpowers_le.mpr
    change ∀ x, color ((conjugateElement 1 : Equiv.Perm (Fin 100)) x) = color x
    apply OrderCertificate.allFin
    decide +kernel

def coordinate (i : Fin 9) : Fin 100 :=
  match i.val with
  | 0 => 11
  | 1 => 52
  | 2 => 40
  | 3 => 71
  | 4 => 9
  | 5 => 44
  | 6 => 47
  | 7 => 8
  | _ => 32

def cosetWord (i : Fin 101) : List (Fin 17) :=
  match i.val with
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | 3 => [2]
  | 4 => [3]
  | 5 => [4]
  | 6 => [5]
  | 7 => [6]
  | 8 => [7]
  | 9 => [8]
  | 10 => [9]
  | 11 => [10]
  | 12 => [11]
  | 13 => [12]
  | 14 => [13]
  | 15 => [14]
  | 16 => [15]
  | 17 => [1, 0]
  | 18 => [2, 0]
  | 19 => [3, 0]
  | 20 => [4, 0]
  | 21 => [5, 0]
  | 22 => [6, 0]
  | 23 => [7, 0]
  | 24 => [8, 0]
  | 25 => [9, 0]
  | 26 => [10, 0]
  | 27 => [11, 0]
  | 28 => [12, 0]
  | 29 => [13, 0]
  | 30 => [14, 0]
  | 31 => [15, 0]
  | 32 => [1, 1]
  | 33 => [3, 1]
  | 34 => [4, 1]
  | 35 => [5, 1]
  | 36 => [6, 1]
  | 37 => [8, 1]
  | 38 => [9, 1]
  | 39 => [10, 1]
  | 40 => [11, 1]
  | 41 => [12, 1]
  | 42 => [13, 1]
  | 43 => [14, 1]
  | 44 => [15, 1]
  | 45 => [16, 1]
  | 46 => [0, 2]
  | 47 => [2, 2]
  | 48 => [3, 2]
  | 49 => [4, 2]
  | 50 => [5, 2]
  | 51 => [6, 2]
  | 52 => [8, 2]
  | 53 => [9, 2]
  | 54 => [10, 2]
  | 55 => [11, 2]
  | 56 => [12, 2]
  | 57 => [13, 2]
  | 58 => [14, 2]
  | 59 => [15, 2]
  | 60 => [16, 2]
  | 61 => [0, 3]
  | 62 => [1, 3]
  | 63 => [2, 3]
  | 64 => [3, 3]
  | 65 => [5, 3]
  | 66 => [6, 3]
  | 67 => [7, 3]
  | 68 => [8, 3]
  | 69 => [9, 3]
  | 70 => [10, 3]
  | 71 => [11, 3]
  | 72 => [12, 3]
  | 73 => [13, 3]
  | 74 => [14, 3]
  | 75 => [15, 3]
  | 76 => [16, 3]
  | 77 => [0, 4]
  | 78 => [1, 4]
  | 79 => [2, 4]
  | 80 => [4, 4]
  | 81 => [5, 4]
  | 82 => [6, 4]
  | 83 => [7, 4]
  | 84 => [8, 4]
  | 85 => [9, 4]
  | 86 => [11, 4]
  | 87 => [13, 4]
  | 88 => [15, 4]
  | 89 => [0, 5]
  | 90 => [1, 5]
  | 91 => [2, 5]
  | 92 => [4, 5]
  | 93 => [5, 5]
  | 94 => [8, 5]
  | 95 => [9, 5]
  | 96 => [10, 5]
  | 97 => [11, 5]
  | 98 => [14, 5]
  | 99 => [15, 5]
  | _ => [0, 6]

def fingerprintValue (i : Fin 101) : Nat :=
  match i.val with
  | 0 => 273
  | 1 => 398
  | 2 => 164
  | 3 => 399
  | 4 => 116
  | 5 => 192
  | 6 => 492
  | 7 => 66
  | 8 => 317
  | 9 => 297
  | 10 => 203
  | 11 => 384
  | 12 => 185
  | 13 => 117
  | 14 => 137
  | 15 => 151
  | 16 => 107
  | 17 => 83
  | 18 => 368
  | 19 => 426
  | 20 => 47
  | 21 => 27
  | 22 => 508
  | 23 => 131
  | 24 => 174
  | 25 => 261
  | 26 => 31
  | 27 => 358
  | 28 => 271
  | 29 => 319
  | 30 => 302
  | 31 => 310
  | 32 => 15
  | 33 => 466
  | 34 => 423
  | 35 => 275
  | 36 => 123
  | 37 => 173
  | 38 => 290
  | 39 => 55
  | 40 => 367
  | 41 => 259
  | 42 => 49
  | 43 => 37
  | 44 => 316
  | 45 => 70
  | 46 => 281
  | 47 => 53
  | 48 => 188
  | 49 => 93
  | 50 => 58
  | 51 => 348
  | 52 => 436
  | 53 => 21
  | 54 => 339
  | 55 => 360
  | 56 => 6
  | 57 => 282
  | 58 => 270
  | 59 => 315
  | 60 => 323
  | 61 => 119
  | 62 => 457
  | 63 => 460
  | 64 => 129
  | 65 => 86
  | 66 => 217
  | 67 => 80
  | 68 => 126
  | 69 => 240
  | 70 => 235
  | 71 => 432
  | 72 => 219
  | 73 => 197
  | 74 => 212
  | 75 => 480
  | 76 => 178
  | 77 => 75
  | 78 => 353
  | 79 => 471
  | 80 => 22
  | 81 => 208
  | 82 => 168
  | 83 => 220
  | 84 => 222
  | 85 => 344
  | 86 => 202
  | 87 => 245
  | 88 => 408
  | 89 => 378
  | 90 => 280
  | 91 => 437
  | 92 => 285
  | 93 => 74
  | 94 => 216
  | 95 => 113
  | 96 => 242
  | 97 => 456
  | 98 => 338
  | 99 => 154
  | _ => 201

def fingerprint (g : CertifiedStabilizer) : Nat :=
  (List.ofFn fun j : Fin 9 =>
    if color ((g : Equiv.Perm (Fin 100))⁻¹ (coordinate j)) then 2 ^ j.val else 0).sum

theorem fingerprint_spec : ∀ i, fingerprint (word (cosetWord i)) = fingerprintValue i := by
  apply OrderCertificate.allFin
  decide +kernel

theorem fingerprintValue_injective : Function.Injective fingerprintValue := by
  have h : ∀ i j : Fin 101, fingerprintValue i = fingerprintValue j → i = j := by
    apply OrderCertificate.allFin
    decide +kernel
  exact h

theorem fingerprint_eq_of_coset_eq (a b : CertifiedStabilizer)
    (h : (a : CertifiedStabilizer ⧸ exceptionalSubgroup) = b) :
    fingerprint a = fingerprint b := by
  have hp := exceptional_le_colorStabilizer (QuotientGroup.eq.mp h)
  have hc (x : Fin 100) : color ((a : Equiv.Perm (Fin 100))⁻¹ x) =
      color ((b : Equiv.Perm (Fin 100))⁻¹ x) := by
    have hx := hp ((b : Equiv.Perm (Fin 100))⁻¹ x)
    change color ((a : Equiv.Perm (Fin 100))⁻¹
      ((b : Equiv.Perm (Fin 100)) ((b : Equiv.Perm (Fin 100))⁻¹ x))) = _ at hx
    simpa only [Subgroup.coe_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using hx
  unfold fingerprint
  simp_rw [hc]

theorem exceptional_index_lower_bound : 101 ≤ exceptionalSubgroup.index := by
  let f : Fin 101 → CertifiedStabilizer ⧸ exceptionalSubgroup := fun i =>
    (word (cosetWord i) : CertifiedStabilizer)
  have hf : Function.Injective f := by
    intro i j h
    apply fingerprintValue_injective
    rw [← fingerprint_spec i, ← fingerprint_spec j]
    exact fingerprint_eq_of_coset_eq _ _ h
  have hcard := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_fin, ← Subgroup.index_eq_card] using hcard

end Sporadic.LeechRelated.HS.SmallIndex.GenerationCertificate
