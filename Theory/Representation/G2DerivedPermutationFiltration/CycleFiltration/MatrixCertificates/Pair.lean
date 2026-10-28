module

public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCertificates.Coordinates

/-!
# The preserved or interchanged pair of cycle halves

The saved half and its root-F image are the two halves of an invertible basis.
Every ambient root/Weyl matrix carries each half onto the prescribed half.
The actual group assembly can therefore use the permutation action on this
pair to obtain invariance under the commutator subgroup.

Source: Aschbacher–Smith G.7.2(3), printed p.348/PDF p.359. This proves the
finite linear algebra; the coset identification remains external.
-/

@[expose] public section
namespace G2DerivedPermutationFiltration.CycleData.Certificate

set_option maxRecDepth 8192

def blockIndex (f : Fin 2) (i : Fin 32) : Fin 64 := if f = 0 then first i else last i

def nextHalf (a : Fin 8) (f : Fin 2) : Fin 2 :=
  if swaps a then (if f = 0 then 1 else 0) else f

def pairInjection (f : Fin 2) : Matrix (Fin 64) (Fin 32) (ZMod 2) :=
  fun i j => pairBasis i (blockIndex f j)

def pairHalf (f : Fin 2) : Submodule (ZMod 2) Space :=
  LinearMap.range (pairInjection f).mulVecLin

def pairCoordinates : Space ≃ₗ[ZMod 2] Space :=
  { pairInverse.mulVecLin with
    invFun := pairBasis.mulVec
    left_inv v := by
      change pairBasis.mulVec (pairInverse.mulVec v) = v
      rw [Matrix.mulVec_mulVec, pair_mul_inverse, Matrix.one_mulVec]
    right_inv v := by
      change pairInverse.mulVec (pairBasis.mulVec v) = v
      rw [Matrix.mulVec_mulVec, inverse_mul_pair, Matrix.one_mulVec] }

private theorem sum64 (f : Fin 64 → ZMod 2) :
    ∑ i, f i = (∑ i : Fin 32, f (first i)) + ∑ i : Fin 32, f (last i) :=
  by simpa only [first_eq_castAdd, last_eq_natAdd] using
    (Fin.sum_univ_add (a := 32) (b := 32) f)

theorem injection_zero (v : Half) :
    (pairInjection 0).mulVec v = adaptedCoordinates.symm (Fin.append v (0 : Half)) := by
  rw [adaptedCoordinates_symm_apply]
  ext i
  change (∑ j, pairBasis i (first j) * v j) =
    ∑ j, adaptedBasis.transpose i j * Fin.append v (0 : Half) j
  rw [sum64]
  simp only [first_eq_castAdd, last_eq_natAdd, Fin.append_left, Fin.append_right, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  rw [show pairBasis i (Fin.castAdd 32 j) =
    adaptedBasis.transpose i (Fin.castAdd 32 j) from pair_first i j]

theorem pairHalf_zero : pairHalf 0 = half := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    change (pairInjection 0).mulVec w ∈ half
    rw [injection_zero, mem_half]
    intro i
    simp only [LinearEquiv.apply_symm_apply, last_eq_natAdd, Fin.append_right, Pi.zero_apply]
  · intro hv
    refine ⟨halfCoordinates ⟨v, hv⟩, ?_⟩
    change (pairInjection 0).mulVec (halfCoordinates ⟨v, hv⟩) = v
    rw [injection_zero]
    apply adaptedCoordinates.injective
    rw [LinearEquiv.apply_symm_apply]
    ext i
    refine Fin.addCases (m := 32) (n := 32) (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      change adaptedCoordinates v (first j) = adaptedCoordinates v (Fin.castAdd 32 j)
      rw [first_eq_castAdd]
    · rw [Fin.append_right]
      simpa only [last_eq_natAdd, Pi.zero_apply] using ((mem_half v).mp hv j).symm

theorem pair_sum (u v : Half) :
    (pairInjection 0).mulVec u + (pairInjection 1).mulVec v =
      pairBasis.mulVec (Fin.append u v) := by
  ext i
  change (∑ j, pairBasis i (first j) * u j) + (∑ j, pairBasis i (last j) * v j) =
    ∑ j, pairBasis i j * Fin.append u v j
  rw [sum64]
  simp only [first_eq_castAdd, last_eq_natAdd, Fin.append_left, Fin.append_right]

@[simp] theorem pairCoordinates_injection_zero (v : Half) :
    pairCoordinates ((pairInjection 0).mulVec v) = Fin.append v (0 : Half) := by
  apply pairCoordinates.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change (pairInjection 0).mulVec v = pairBasis.mulVec (Fin.append v (0 : Half))
  simpa using pair_sum v 0

@[simp] theorem pairCoordinates_injection_one (v : Half) :
    pairCoordinates ((pairInjection 1).mulVec v) = Fin.append (0 : Half) v := by
  apply pairCoordinates.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change (pairInjection 1).mulVec v = pairBasis.mulVec (Fin.append (0 : Half) v)
  simpa using pair_sum 0 v

/-- The two actual subspaces are complementary, as certified by the paired basis. -/
theorem pair_complementary : IsCompl (pairHalf 0) (pairHalf 1) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro v ⟨u, hu⟩ ⟨w, hw⟩
    have h := congrArg pairCoordinates (hu.trans hw.symm)
    change pairCoordinates ((pairInjection 0).mulVec u) =
      pairCoordinates ((pairInjection 1).mulVec w) at h
    rw [pairCoordinates_injection_zero, pairCoordinates_injection_one] at h
    have hu0 : u = 0 := by
      ext i
      simpa only [first_eq_castAdd, Fin.append_left, Pi.zero_apply] using congrFun h (first i)
    rw [← hu, hu0]
    exact map_zero _
  · rw [codisjoint_iff_le_sup]
    intro v _
    let u : Half := fun i => pairCoordinates v (first i)
    let w : Half := fun i => pairCoordinates v (last i)
    have h : Fin.append u w = pairCoordinates v := by
      ext i
      refine Fin.addCases (m := 32) (n := 32) (fun j => ?_) (fun j => ?_) i <;> simp only [u, w, first_eq_castAdd, last_eq_natAdd, Fin.append_left, Fin.append_right]
    apply Submodule.mem_sup.mpr
    refine ⟨(pairInjection 0).mulVec u, ⟨u, rfl⟩,
      (pairInjection 1).mulVec w, ⟨w, rfl⟩, ?_⟩
    rw [pair_sum, h]
    exact pairCoordinates.symm_apply_apply v

theorem ambient_square (a : Fin 8) : ambientMatrix a * ambientMatrix a = 1 := by
  have h : cycleEmbedding * (ambientMatrix a * ambientMatrix a) = cycleEmbedding := by
    rw [← Matrix.mul_assoc, embedding_ambient]
    ext i j
    change (cycleEmbedding * ambientMatrix a) (ambientFlagPermutation a i) j = _
    rw [embedding_ambient]
    change cycleEmbedding (ambientFlagPermutation a (ambientFlagPermutation a i)) j = cycleEmbedding i j
    rw [ambient_flag_involution]
  calc
    ambientMatrix a * ambientMatrix a =
        (extraction * cycleEmbedding) * (ambientMatrix a * ambientMatrix a) := by
      rw [extraction_embedding, one_mul]
    _ = extraction * (cycleEmbedding * (ambientMatrix a * ambientMatrix a)) :=
      Matrix.mul_assoc _ _ _
    _ = 1 := by rw [h, extraction_embedding]

private theorem pair_off_block (a : Fin 8) (f : Fin 2) (i j : Fin 32) :
    pairAction a (blockIndex (if nextHalf a f = 0 then 1 else 0) i) (blockIndex f j) = 0 := by
  have h := pair_zero_blocks a i j
  by_cases hs : swaps a = true <;> fin_cases f <;> simp_all [nextHalf, blockIndex]

private theorem nextHalf_involutive (a : Fin 8) (f : Fin 2) :
    nextHalf a (nextHalf a f) = f := by
  revert a f
  decide +kernel

/-- The matrix on one half, with the codomain half chosen by the ambient actor. -/
def pairBlock (a : Fin 8) (f : Fin 2) : Matrix (Fin 32) (Fin 32) (ZMod 2) :=
  fun i j => pairAction a (blockIndex (nextHalf a f) i) (blockIndex f j)

theorem ambient_injection (a : Fin 8) (f : Fin 2) :
    ambientMatrix a * pairInjection f = pairInjection (nextHalf a f) * pairBlock a f := by
  ext i j
  have h := congrFun (congrFun (pair_action a).symm i) (blockIndex f j)
  change (∑ k, ambientMatrix a i k * pairBasis k (blockIndex f j)) = _
  rw [show (∑ k, ambientMatrix a i k * pairBasis k (blockIndex f j)) =
      ∑ k, pairBasis i k * pairAction a k (blockIndex f j) from h, sum64]
  by_cases hf : nextHalf a f = 0
  · have hz (k : Fin 32) : pairAction a (last k) (blockIndex f j) = 0 := by
      simpa [blockIndex, hf] using pair_off_block a f k j
    simp only [hz, mul_zero, Finset.sum_const_zero, add_zero]
    change _ = ∑ k, pairBasis i (blockIndex (nextHalf a f) k) *
      pairAction a (blockIndex (nextHalf a f) k) (blockIndex f j)
    simp only [blockIndex, hf, ↓reduceIte]
  · have hz (k : Fin 32) : pairAction a (first k) (blockIndex f j) = 0 := by
      simpa [blockIndex, hf] using pair_off_block a f k j
    simp only [hz, mul_zero, Finset.sum_const_zero, zero_add]
    change _ = ∑ k, pairBasis i (blockIndex (nextHalf a f) k) *
      pairAction a (blockIndex (nextHalf a f) k) (blockIndex f j)
    simp only [blockIndex, hf, ↓reduceIte]

theorem ambient_mem_pair (a : Fin 8) (f : Fin 2) {v : Space} (hv : v ∈ pairHalf f) :
    (ambientMatrix a).mulVec v ∈ pairHalf (nextHalf a f) := by
  obtain ⟨w, rfl⟩ := hv
  refine ⟨(pairBlock a f).mulVec w, ?_⟩
  change (pairInjection (nextHalf a f)).mulVec ((pairBlock a f).mulVec w) =
    (ambientMatrix a).mulVec ((pairInjection f).mulVec w)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ambient_injection]

/-- Each ambient actor carries each half onto its prescribed half. -/
theorem ambient_map_pair (a : Fin 8) (f : Fin 2) :
    (pairHalf f).map (ambientMatrix a).mulVecLin = pairHalf (nextHalf a f) := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact ambient_mem_pair a f hv
  · intro v hv
    refine ⟨(ambientMatrix a).mulVec v, ?_, ?_⟩
    · change (ambientMatrix a).mulVec v ∈ pairHalf f
      have h := ambient_mem_pair a (nextHalf a f) (v := v) hv
      rw [nextHalf_involutive] at h
      exact h
    · change (ambientMatrix a).mulVec ((ambientMatrix a).mulVec v) = v
      rw [Matrix.mulVec_mulVec, ambient_square, Matrix.one_mulVec]

/-- The second half is literally the image under root F of the saved half. -/
theorem pairHalf_one : pairHalf 1 = half.map (ambientMatrix 5).mulVecLin := by
  rw [← pairHalf_zero, ambient_map_pair]
  rfl

end G2DerivedPermutationFiltration.CycleData.Certificate
