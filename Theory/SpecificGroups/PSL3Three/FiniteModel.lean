module

public import Theory.SpecificGroups.PSL3Three.Subgroups
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Pointwise.Stabilizer

/-!
# A finite encoding of SL₃(3)

Nine base-three digits encode the entries in row-major order. Filtering the
19,683 codes by the explicit three-by-three determinant gives a complete finite
model of the actual special linear group. The group laws are transported through
the matrix equivalence, not checked by an associativity table. All operations and
enumerations are exposed for kernel-checked finite certificates.

The candidate tests below use the existing column action on vectors. In
particular the first line stabilizer has zeros below its first diagonal entry,
whereas the complementary plane stabilizer has zeros to its right.

Source: GLS III, Theorem 6.5.3(a–c), and the concrete definitions in `Subgroups`.
-/

namespace Matrix.PSL3Three

/-- A base-three code for nine entries. -/
public abbrev MatrixCode := Fin (3 ^ 9)

/-- Row-major base-three encoding; entry `(i,j)` has digit index `3*i+j`. -/
@[expose] public def matrixCodeEquiv : Matrix (Fin 3) (Fin 3) (ZMod 3) ≃ MatrixCode :=
  (Equiv.curry (Fin 3) (Fin 3) (Fin 3)).symm |>.trans
    ((Equiv.arrowCongr finProdFinEquiv (Equiv.refl (Fin 3))).trans finFunctionFinEquiv)

@[expose] public def decodeMatrix (c : MatrixCode) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  matrixCodeEquiv.symm c

@[simp] public theorem decode_encode (m : Matrix (Fin 3) (Fin 3) (ZMod 3)) :
    decodeMatrix (matrixCodeEquiv m) = m := matrixCodeEquiv.symm_apply_apply m

@[simp] public theorem encode_decode (c : MatrixCode) :
    matrixCodeEquiv (decodeMatrix c) = c := matrixCodeEquiv.apply_symm_apply c

/-- A six-term determinant, avoiding permutation enumeration in certificates. -/
@[expose] public def codeDet (c : MatrixCode) : ZMod 3 :=
  let m := decodeMatrix c
  m 0 0 * m 1 1 * m 2 2 - m 0 0 * m 1 2 * m 2 1 -
    m 0 1 * m 1 0 * m 2 2 + m 0 1 * m 1 2 * m 2 0 +
    m 0 2 * m 1 0 * m 2 1 - m 0 2 * m 1 1 * m 2 0

public theorem codeDet_eq_det (c : MatrixCode) : codeDet c = (decodeMatrix c).det :=
  (det_fin_three _).symm

/-- Determinant-one codes, with computable equality and finite enumeration. -/
public abbrev FiniteModel := {c : MatrixCode // codeDet c = 1}

/-- Interpretation as the actual determinant-one matrix. -/
@[expose] public def finiteModelEquiv : FiniteModel ≃ SL where
  toFun c := ⟨decodeMatrix c.val, (codeDet_eq_det c.val).symm.trans c.property⟩
  invFun g := ⟨matrixCodeEquiv g.val, by rw [codeDet_eq_det, decode_encode]; exact g.property⟩
  left_inv c := Subtype.ext (encode_decode c.val)
  right_inv g := Subtype.ext (decode_encode g.val)

public instance finiteModelGroup : Group FiniteModel := finiteModelEquiv.group

/-- The encoding preserves the full group structure. -/
@[expose] public def finiteModelMulEquiv : FiniteModel ≃* SL := finiteModelEquiv.mulEquiv

@[simp] public theorem finiteModel_mul (a b : FiniteModel) :
    finiteModelEquiv (a * b) = finiteModelEquiv a * finiteModelEquiv b :=
  finiteModelMulEquiv.map_mul a b

@[simp] public theorem finiteModel_inv (a : FiniteModel) :
    finiteModelEquiv a⁻¹ = (finiteModelEquiv a)⁻¹ := finiteModelMulEquiv.map_inv a

/-- Multiplication computes by multiplying the decoded matrices and encoding. -/
public theorem mul_code (a b : FiniteModel) :
    (a * b).val = matrixCodeEquiv (decodeMatrix a.val * decodeMatrix b.val) := rfl

/-- Inversion computes by the adjugate, since the determinant is one. -/
public theorem inv_code (a : FiniteModel) :
    a⁻¹.val = matrixCodeEquiv (adjugate (decodeMatrix a.val)) := rfl

/-- Complete enumeration without an external table. -/
@[expose] public def determinantOneCodes : Finset MatrixCode :=
  Finset.univ.filter (fun c => codeDet c = 1)

@[simp] public theorem mem_determinantOneCodes (c : MatrixCode) :
    c ∈ determinantOneCodes ↔ codeDet c = 1 := by simp [determinantOneCodes]

@[expose] public def allElements : Finset FiniteModel := Finset.univ

@[simp] public theorem mem_allElements (g : FiniteModel) : g ∈ allElements :=
  Finset.mem_univ g

public theorem enumeration_complete (g : SL) :
    ∃ c ∈ allElements, finiteModelEquiv c = g :=
  ⟨finiteModelEquiv.symm g, mem_allElements _, finiteModelEquiv.apply_symm_apply g⟩

/-- The numerical value of an entry is its base-three digit. -/
public theorem decodeMatrix_entry (c : MatrixCode) (i j : Fin 3) :
    (decodeMatrix c i j).val = c.val / 3 ^ (3 * i.val + j.val) % 3 := by
  change c.val / 3 ^ (j.val + 3 * i.val) % 3 = _
  rw [Nat.add_comm j.val]

/-- The first coordinate line is invariant exactly when column zero lies in it. -/
public theorem mem_lineStabilizerSL_iff (g : SL) :
    g ∈ lineStabilizerSL ↔ g.val 1 0 = 0 ∧ g.val 2 0 = 0 := by
  rw [lineStabilizerSL, MulAction.mem_stabilizer_set' (Set.toFinite _)]
  change (∀ ⦃v : Fin 3 → ZMod 3⦄, v 1 = 0 ∧ v 2 = 0 →
    (g.val.mulVec v) 1 = 0 ∧ (g.val.mulVec v) 2 = 0) ↔ _
  constructor
  · intro h
    simpa [mulVec, dotProduct, Fin.sum_univ_three] using
      h (v := ![1, 0, 0]) (by simp)
  · rintro ⟨h1, h2⟩ v ⟨v1, v2⟩
    simp [mulVec, dotProduct, Fin.sum_univ_three, h1, h2, v1, v2]

/-- The coordinate plane is invariant exactly when row zero vanishes on it. -/
public theorem mem_planeStabilizerSL_iff (g : SL) :
    g ∈ planeStabilizerSL ↔ g.val 0 1 = 0 ∧ g.val 0 2 = 0 := by
  rw [planeStabilizerSL, MulAction.mem_stabilizer_set' (Set.toFinite _)]
  change (∀ ⦃v : Fin 3 → ZMod 3⦄, v 0 = 0 → (g.val.mulVec v) 0 = 0) ↔ _
  constructor
  · intro h
    constructor
    · simpa [mulVec, dotProduct, Fin.sum_univ_three] using
        h (v := ![0, 1, 0]) (by simp)
    · simpa [mulVec, dotProduct, Fin.sum_univ_three] using
        h (v := ![0, 0, 1]) (by simp)
  · rintro ⟨h1, h2⟩ v v0
    simp [mulVec, dotProduct, Fin.sum_univ_three, h1, h2, v0]

/-- The norm equation selects precisely the six signed coordinate vectors. -/
public theorem norm_one_iff_signed_coordinate : ∀ v : Fin 3 → ZMod 3,
    v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 ↔
      ∃ i : Fin 3, v = Pi.single i 1 ∨ v = -Pi.single i 1 := by decide

/-- A finite test for preservation of the signed coordinate vectors. -/
public theorem mem_monomialSL_iff (g : SL) : g ∈ monomialSL ↔
    ∀ v : Fin 3 → ZMod 3, v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 →
      (g.val.mulVec v) 0 ^ 2 + (g.val.mulVec v) 1 ^ 2 + (g.val.mulVec v) 2 ^ 2 = 1 := by
  rw [monomialSL, MulAction.mem_stabilizer_set' (Set.toFinite _)]
  rfl

/-- It suffices to test the three columns, the images of the coordinate basis. -/
public theorem mem_monomialSL_iff_columns (g : SL) : g ∈ monomialSL ↔
    ∀ j : Fin 3, g.val 0 j ^ 2 + g.val 1 j ^ 2 + g.val 2 j ^ 2 = 1 := by
  rw [mem_monomialSL_iff]
  constructor
  · intro h j
    have hj := (norm_one_iff_signed_coordinate (Pi.single j 1)).mpr ⟨j, Or.inl rfl⟩
    simpa using h _ hj
  · intro h v hv
    obtain ⟨j, rfl | rfl⟩ := (norm_one_iff_signed_coordinate v).mp hv
    · simpa [mulVec_neg] using h j
    · simpa [mulVec_neg] using h j

/-- The thirteen powers of the specified companion matrix. -/
@[expose] public def singerPowers : Finset SL :=
  (Finset.range 13).image (singerGenerator ^ ·)

public theorem mem_singerSubgroupSL_iff (g : SL) :
    g ∈ singerSubgroupSL ↔ g ∈ singerPowers := by
  simpa [singerSubgroupSL, singerPowers, orderOf_singerGenerator] using
    (mem_zpowers_iff_mem_range_orderOf (x := singerGenerator) (y := g))

public theorem coe_singerPowers : (singerPowers : Set SL) = singerSubgroupSL := by
  ext g
  exact (mem_singerSubgroupSL_iff g).symm

/-- Normalization is equality of two explicitly enumerated thirteen-element sets. -/
public theorem mem_singerNormalizerSL_iff (g : SL) :
    g ∈ singerNormalizerSL ↔ singerPowers.image (fun h => g * h * g⁻¹) = singerPowers := by
  rw [singerNormalizerSL, Subgroup.mem_normalizer_iff_conj_image_eq,
    ← coe_singerPowers, ← Finset.coe_inj, Finset.coe_image]
  rfl

public instance decidableLineStabilizer (g : SL) : Decidable (g ∈ lineStabilizerSL) :=
  decidable_of_iff _ (mem_lineStabilizerSL_iff g).symm

public instance decidablePlaneStabilizer (g : SL) : Decidable (g ∈ planeStabilizerSL) :=
  decidable_of_iff _ (mem_planeStabilizerSL_iff g).symm

public instance decidableMonomial (g : SL) : Decidable (g ∈ monomialSL) :=
  decidable_of_iff _ (mem_monomialSL_iff_columns g).symm

public instance decidableSingerSubgroup (g : SL) : Decidable (g ∈ singerSubgroupSL) :=
  decidable_of_iff _ (mem_singerSubgroupSL_iff g).symm

public instance decidableSingerNormalizer (g : SL) : Decidable (g ∈ singerNormalizerSL) :=
  decidable_of_iff _ (mem_singerNormalizerSL_iff g).symm

end Matrix.PSL3Three
