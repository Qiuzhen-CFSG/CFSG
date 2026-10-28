module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourCubicCertificates
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.MatrixInspection
/-!
# Exhaustion of the cubic four-space overgroups

Normalize the first two independent columns by an even permutation, then
apply the seven kernel-checked certificate families. Transport the resulting
double-coset expression through the literal coordinate permutation action.
The previously checked representative words exclude every overgroup outside
S₅ at cubic rank one, proving the formerly explicit inspection premise.
The companion action module applies this result to the original Hermitian U.
Source: Aschbacher–Smith 8.2.8(1), printed p.719, refs/quasithin.pdf.
-/
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.MatrixInspection.HermitianCoverage
private theorem permute_one : permuteBits 1 = 1 := by
  rw [← bitAction_permutationAction, map_one, map_one]

private theorem permute_mul (σ τ : Equiv.Perm (Fin 5)) :
    permuteBits (σ * τ) = permuteBits σ * permuteBits τ := by
  rw [← bitAction_permutationAction, map_mul, map_mul,
    bitAction_permutationAction, bitAction_permutationAction]

private theorem permute_injective (σ : Equiv.Perm (Fin 5)) :
    Function.Injective (permuteBits σ) := by
  intro x y h
  apply decode_bijective.injective
  apply (permutationAction σ).injective
  rw [permutationAction_decode, permutationAction_decode, h]

private theorem permute_applyMatrix (σ : Equiv.Perm (Fin 5)) (c : Columns) :
    applyMatrix (fun i => permuteBits σ (c i)) = permuteBits σ * applyMatrix c := by
  funext x
  apply decode_bijective.injective
  change decode (applyMatrix _ x) = decode (permuteBits σ (applyMatrix c x))
  rw [← permutationAction_decode, decode_applyMatrix, decode_applyMatrix]
  simp only [map_mul, apply_ite (permutationAction σ), map_one, permutationAction_decode]

private theorem applyMatrix_zero (c : Columns) : applyMatrix c 0 = 0 := by
  simp [applyMatrix]

private theorem applyMatrix_basis (c : Columns) (i : Fin 4) :
    applyMatrix c (basisBits i) = c i := by
  fin_cases i <;> simp [basisBits, applyMatrix]

/-- The seven ordered-pair families exhaust every invertible binary matrix,
with actual even permutations on both sides of the fourteen representatives. -/
public theorem doubleCosetCoverage : DoubleCosetCoverage := by
  intro c hc
  have hz (i : Fin 4) : c i ≠ 0 := by
    intro he
    have hb := hc ((applyMatrix_basis c i).trans (he.trans (applyMatrix_zero c).symm))
    have hn : basisBits i ≠ 0 := by fin_cases i <;> decide
    exact hn hb
  have hne : c 0 ≠ c 1 := by
    intro he
    have hb := hc ((applyMatrix_basis c 0).trans (he.trans (applyMatrix_basis c 1).symm))
    exact (by decide : basisBits 0 ≠ basisBits 1) hb
  obtain ⟨i,σ,hσeven,hp0,hp1⟩ := orderedPair_marking (c 0) (c 1) (hz 0) (hz 1) hne
  let d : Columns := fun i => permuteBits σ⁻¹ (c i)
  have hσ : permuteBits σ⁻¹ * permuteBits σ = 1 := by
    rw [← permute_mul, inv_mul_cancel, permute_one]
  have hd0 : d 0 = (pairRep i).1 := by
    change permuteBits σ⁻¹ (c 0) = _
    rw [← hp0]
    exact congrFun hσ _
  have hd1 : d 1 = (pairRep i).2 := by
    change permuteBits σ⁻¹ (c 1) = _
    rw [← hp1]
    exact congrFun hσ _
  have hdeq : d = ![(pairRep i).1, (pairRep i).2, d 2, d 3] := by
    funext i
    fin_cases i
    · exact hd0
    · exact hd1
    · rfl
    · rfl
  have hdi : Function.Injective (applyMatrix d) := by
    rw [permute_applyMatrix]
    exact (permute_injective σ⁻¹).comp hc
  obtain ⟨j,s,t,hs,ht,hcov⟩ := normalized_coverage i (d 2).toFin (d 3).toFin
    (hdeq ▸ hdi)
  have hd : applyMatrix d = permuteBits s * allRep j * permuteBits t := by
    simpa only [← hdeq, BitVec.ofFin_toFin] using hcov
  have hrecover : applyMatrix c = permuteBits σ * applyMatrix d := by
    rw [permute_applyMatrix, ← mul_assoc, ← permute_mul, mul_inv_cancel, permute_one, one_mul]
  rw [hd] at hrecover
  have hprod : applyMatrix c = permuteBits (σ * s) * allRep j * permuteBits t := by
    rw [permute_mul]
    simpa only [mul_assoc] using hrecover
  by_cases hj : j.val < 2
  · have hr : allRep j = permuteBits (if j.val = 0 then 1 else Equiv.swap 0 1) := by
      simp only [allRep, dif_pos hj]
    refine Or.inl ⟨(σ*s) * (if j.val = 0 then 1 else Equiv.swap 0 1) * t, ?_⟩
    rw [permute_mul, permute_mul, ← hr]
    exact hprod
  · refine Or.inr ⟨⟨j.val-2, by omega⟩, σ*s, t, ?_,ht,?_⟩
    · rw [map_mul, hσeven, hs, one_mul]
    · simpa only [allRep, dif_neg hj] using hprod

/-- The marked binary A₅ has no cubic-rank-one overgroup outside its S₅ normalizer. -/
public theorem cubicOvergroupInspection : CubicOvergroupInspection :=
  inspection_of_doubleCosetCoverage doubleCosetCoverage

end CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.FourSpaceInspection.MatrixInspection.HermitianCoverage
