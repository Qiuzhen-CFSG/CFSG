module
public import Theory.SpecificGroups.Triality.LeviRankOneMatrices.Comparison
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.RootElements
public import Theory.SpecificGroups.Triality.BinaryCenter

/-!
# A nontrivial fourth power in the genuine split D4 model

Sixteen sparse vector actions certify one nonzero entry of the fourth power
of x₁(1)x₀(1)x₂(1)x₃(1). The integral tables are checked modulo two, then
transported through the existing Geck entry formulas and the actual split
matrix homomorphism. No group enumeration or independent model is used.
This supplies a small rank witness for Aschbacher–Smith G.9.3, printed p.356;
Geck coordinates follow GLS3 2.6.2 and the repository's Levi comparison.
-/

@[expose] public section
namespace Triality.Standard.BinaryRootWord
open Matrix
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.Parabolics.RankOneMatrices
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.SimpleGeckGroup
noncomputable section
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

/-- Four actual positive-simple matrices over the prime field, in common coordinates. -/
private def rowBits (i : Fin 4) : Fin 28 → ℕ :=
  ![![65, 2, 4, 8, 16, 98, 64, 128, 65792, 131584, 1024, 2048, 1052672, 2105344, 16384, 32768, 65536, 131072, 263168, 526336, 1048576, 2097152, 4210688, 8421376, 16777216, 33554432, 67108864, 134217728],
    ![1, 262146, 4, 8, 272, 32, 1088, 128, 256, 544, 1024, 2176, 4096, 8192, 16384, 32768, 65536, 393229, 262144, 524288, 17825792, 35651584, 4194304, 8388608, 16777216, 33554432, 71303168, 142606336],
    ![1, 2, 67108868, 8, 16, 32, 64, 128, 4352, 512, 17408, 2048, 4096, 8704, 16384, 34816, 1114112, 131072, 4456448, 524288, 1048576, 2228224, 4194304, 8912896, 16777216, 100663298, 67108864, 134217728],
    ![1, 2, 4, 134217736, 16, 32, 64, 128, 8448, 512, 33792, 2048, 4608, 8192, 18432, 32768, 2162688, 131072, 8650752, 524288, 1179648, 2097152, 4718592, 8388608, 150994946, 33554432, 67108864, 134217728]] i

private def intMatrix (i : Fin 4) : Matrix (Fin 28) (Fin 28) ℤ :=
  fun r c => if (rowBits i r).testBit c.val then 1 else 0

private def vectorBits : Fin 17 → ℕ :=
  ![128, 128, 128, 128, 2176, 18560, 52352, 13421696, 214877378, 211468490, 205243598, 218101711, 16777117, 11184797, 658077, 133277, 157]

private def intVector (k : Fin 17) : Fin 28 → ℤ :=
  fun r => if (vectorBits k).testBit r.val then 1 else 0

private def stepRoot (k : Fin 16) : Fin 4 := ![3, 2, 0, 1] ⟨k.val % 4, Nat.mod_lt _ (by decide)⟩

private def forwardCoordinates (i : Fin 4) : FlatIndex ≃ Fin 28 :=
  (Equiv.sumCongr (Equiv.refl _) (rootOrder i)).trans finSumFinEquiv

private def commonEquiv : Fin 28 ≃ LatticeIndex :=
  finSumFinEquiv.symm.trans
    (Equiv.sumCongr (typeDRootPairing_baseEquiv 2) rootEnumeration)

private lemma common_forward (i : Fin 4) (r : FlatIndex) :
    commonEquiv (forwardCoordinates i r) = flatEquiv i r := by
  simp only [commonEquiv, forwardCoordinates, Equiv.trans_apply, Equiv.symm_apply_apply]
  rcases r with r | r <;> rfl

private def integralCurve (i : Fin 4) (r s : FlatIndex) : ℤ :=
  (if r = s then 1 else 0) + eData i r s +
    (if r = .inr 0 ∧ s = .inr 1 then 1 else 0)

/- The finite table matches the already proved Geck entry formula modulo two. -/
set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma intMatrix_matches : ∀ (i : Fin 4) (r s : FlatIndex),
    integralCurve i r s % 2 =
      intMatrix i (forwardCoordinates i r) (forwardCoordinates i s) := by
  decide +kernel

/- Each certificate step is one matrix/vector product over the prime field. -/
set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma vector_steps : ∀ (k : Fin 16) (r : Fin 28),
    ((intMatrix (stepRoot k)) *ᵥ (intVector ⟨k.val, by omega⟩)) r % 2 =
      intVector ⟨k.val + 1, by omega⟩ r := by
  decide +kernel

variable {F : Type*} [CommRing F] [CharP F 2]

private def smallMatrix (i : Fin 4) : Matrix (Fin 28) (Fin 28) F :=
  (intMatrix i).map (Int.castRingHom F)

private def smallVector (k : Fin 17) : Fin 28 → F :=
  fun r => (intVector k r : F)

private lemma small_step (k : Fin 16) :
    smallMatrix (F := F) (stepRoot k) *ᵥ smallVector ⟨k.val, by omega⟩ =
      smallVector ⟨k.val + 1, by omega⟩ := by
  ext r
  change ((intMatrix (stepRoot k)).map (Int.castRingHom F) *ᵥ
    ((Int.castRingHom F) ∘ intVector ⟨k.val, by omega⟩)) r = _
  rw [← RingHom.map_mulVec]
  change (((intMatrix (stepRoot k) *ᵥ intVector ⟨k.val, by omega⟩) r : ℤ) : F) = _
  rw [CharTwo.intCast_eq_mod, vector_steps]
  rfl

private lemma common_positive (i : Fin 4) :
    Matrix.reindexRingEquiv F commonEquiv.symm
      (positiveMatrix (typeDRootPairing_baseEquiv 2 i) (1 : F)) = smallMatrix i := by
  ext r s
  obtain ⟨r, rfl⟩ := (forwardCoordinates i).surjective r
  obtain ⟨s, rfl⟩ := (forwardCoordinates i).surjective s
  change positiveMatrix _ (1 : F)
    (commonEquiv (forwardCoordinates i r)) (commonEquiv (forwardCoordinates i s)) = _
  rw [common_forward, common_forward, positiveMatrix_entry]
  have hcast :
      (if r = s then (1 : F) else 0) + 1 * (eData i r s : F) +
        1 ^ 2 * (if r = .inr 0 ∧ s = .inr 1 then 1 else 0) =
      (integralCurve i r s : F) := by
    simp [integralCurve]
  rw [hcast, CharTwo.intCast_eq_mod, intMatrix_matches]
  rfl

private def wordMatrix : Matrix (Fin 28) (Fin 28) F :=
  smallMatrix 1 * (smallMatrix 0 * smallMatrix 2 * smallMatrix 3)

private lemma word_four_action :
    (wordMatrix (F := F) ^ 4) *ᵥ smallVector 0 = smallVector 16 := by
  simp only [wordMatrix, pow_succ, pow_zero, ← Matrix.mulVec_mulVec]
  rw [show smallMatrix (F := F) 3 *ᵥ smallVector 0 = smallVector 1 from small_step 0]
  rw [show smallMatrix (F := F) 2 *ᵥ smallVector 1 = smallVector 2 from small_step 1]
  rw [show smallMatrix (F := F) 0 *ᵥ smallVector 2 = smallVector 3 from small_step 2]
  rw [show smallMatrix (F := F) 1 *ᵥ smallVector 3 = smallVector 4 from small_step 3]
  rw [show smallMatrix (F := F) 3 *ᵥ smallVector 4 = smallVector 5 from small_step 4]
  rw [show smallMatrix (F := F) 2 *ᵥ smallVector 5 = smallVector 6 from small_step 5]
  rw [show smallMatrix (F := F) 0 *ᵥ smallVector 6 = smallVector 7 from small_step 6]
  rw [show smallMatrix (F := F) 1 *ᵥ smallVector 7 = smallVector 8 from small_step 7]
  rw [show smallMatrix (F := F) 3 *ᵥ smallVector 8 = smallVector 9 from small_step 8]
  rw [show smallMatrix (F := F) 2 *ᵥ smallVector 9 = smallVector 10 from small_step 9]
  rw [show smallMatrix (F := F) 0 *ᵥ smallVector 10 = smallVector 11 from small_step 10]
  rw [show smallMatrix (F := F) 1 *ᵥ smallVector 11 = smallVector 12 from small_step 11]
  rw [show smallMatrix (F := F) 3 *ᵥ smallVector 12 = smallVector 13 from small_step 12]
  rw [show smallMatrix (F := F) 2 *ᵥ smallVector 13 = smallVector 14 from small_step 13]
  rw [show smallMatrix (F := F) 0 *ᵥ smallVector 14 = smallVector 15 from small_step 14]
  rw [show smallMatrix (F := F) 1 *ᵥ smallVector 15 = smallVector 16 from small_step 15]
  exact Matrix.one_mulVec _

private lemma word_four_ne_one [Nontrivial F] : (wordMatrix (F := F)) ^ 4 ≠ 1 := by
  intro h
  have hc := congrArg (fun a : Matrix (Fin 28) (Fin 28) F =>
    (a *ᵥ smallVector 0) 0) h
  rw [word_four_action, Matrix.one_mulVec] at hc
  have h0 : intVector 0 0 = 0 := by decide +kernel
  have h16 : intVector 16 0 = 1 := by decide +kernel
  change (intVector 16 0 : F) = (intVector 0 0 : F) at hc
  rw [h16, h0, Int.cast_one, Int.cast_zero] at hc
  exact one_ne_zero hc

/-- The actual split carrier is mapped to the same common-coordinate matrices. -/
private def splitMatrixHom (P : Parameters) :
    SplitGroup P →* Matrix (Fin 28) (Fin 28) (ExtensionField P) where
  toFun g := Matrix.reindexRingEquiv _ commonEquiv.symm g.val.val
  map_one' := map_one (Matrix.reindexRingEquiv _ commonEquiv.symm)
  map_mul' a b := map_mul (Matrix.reindexRingEquiv _ commonEquiv.symm) a.val.val b.val.val

private lemma splitMatrix_positive (P : Parameters) (hp : P.prime = 2) (i : Fin 4) :
    splitMatrixHom P (positiveRoot P i 1) = smallMatrix i := by
  let := rankOneExtensionCharTwo P hp
  exact common_positive i

lemma split_word_four_ne_one (P : Parameters) (hp : P.prime = 2) :
    (positiveRoot P 1 1 * (positiveRoot P 0 1 * positiveRoot P 2 1 *
      positiveRoot P 3 1)) ^ 4 ≠ 1 := by
  let := rankOneExtensionCharTwo P hp
  intro h
  have hm := congrArg (splitMatrixHom P) h
  simp only [map_pow, map_mul, map_one, splitMatrix_positive P hp] at hm
  exact word_four_ne_one hm

end
end Triality.Standard.BinaryRootWord
