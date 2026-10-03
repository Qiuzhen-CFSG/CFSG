module
public import Stellmacher.Recognition.LyonsU3Four.TableIDegreeData
public import Stellmacher.Recognition.LyonsU3Four.TableIPatterns
import Mathlib.Tactic

/-!
# Signed transport of the Table I constraints

A simultaneous sign change of a decomposition row and its degree preserves
orthogonality, the weighted class-product sums, and absolute degrees. Conjugating
the Galois permutation also preserves its relative signs. Consequently the three
numerical constraint packages, including the separation hypothesis of the prime
bound, transport through an explicit signed row equivalence.

The matrix adapter deduces the principal sign from the principal `dᵗ` entries.
It makes no classification claim about an arbitrary Table I pattern witness.
Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), §3 and Table I.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Simultaneous signed reindexing of degrees and decomposition rows. -/
structure SignedDegreeEquiv (d : GeneralizedDecompositionData I)
    (d' : GeneralizedDecompositionData J) (r : I → ℤ) (r' : J → ℤ) where
  equiv : I ≃ J
  sign : I → ℤ
  sign_sq : ∀ j, sign j ^ 2 = 1
  degree_eq : ∀ j, r' (equiv j) = sign j * r j
  t_eq : ∀ j, d'.dT (equiv j) = sign j * d.dT j
  z_eq : ∀ j i, d'.iDz i (equiv j) = sign j * d.iDz i j

namespace SignedDegreeEquiv
variable {d : GeneralizedDecompositionData I} {d' : GeneralizedDecompositionData J}
variable {r : I → ℤ} {r' : J → ℤ}
variable (h : SignedDegreeEquiv d d' r r')
include h

omit [Fintype I] [Fintype J] in
theorem natAbs_eq (j : I) : (r' (h.equiv j)).natAbs = (r j).natAbs := by
  rw [h.degree_eq]
  rcases sq_eq_one_iff.mp (h.sign_sq j) with hs | hs <;> simp [hs]

omit [Fintype I] [Fintype J] in
theorem zValue_eq (j : I) : d'.zValue (h.equiv j) = h.sign j * d.zValue j := by
  simp only [zValue, h.z_eq, Finset.mul_sum]

theorem columnInner_eq {a : I → ℤ} {a' : J → ℤ}
    (ha : ∀ j, a' (h.equiv j) = h.sign j * a j) :
    columnInner r' a' = columnInner r a := by
  unfold columnInner
  apply (Fintype.sum_equiv h.equiv _ _ ?_).symm
  intro j
  rw [h.degree_eq, ha]
  rcases sq_eq_one_iff.mp (h.sign_sq j) with hs | hs <;> simp [hs]

theorem weightedColumn_eq {a : I → ℤ} {a' : J → ℤ}
    (ha : ∀ j, a' (h.equiv j) = h.sign j * a j) :
    d'.weightedColumn r' a' = d.weightedColumn r a := by
  unfold weightedColumn
  apply (Fintype.sum_equiv h.equiv _ _ ?_).symm
  intro j
  rw [h.zValue_eq, h.degree_eq, ha]
  rcases sq_eq_one_iff.mp (h.sign_sq j) with hs | hs <;> simp [hs]

omit [Fintype I] [Fintype J] in
theorem galois (hg : d.SignedGaloisSymmetry r) : d'.SignedGaloisSymmetry r' := by
  obtain ⟨σ, hσ⟩ := hg
  refine ⟨h.equiv.symm.trans (σ.trans h.equiv), ?_⟩
  intro k
  obtain ⟨j, rfl⟩ := h.equiv.surjective k
  obtain ⟨ε, hε, hr, ht, hz⟩ := hσ j
  refine ⟨h.sign j * ε * h.sign (σ j), ?_, ?_, ?_, ?_⟩
  · simp [mul_pow, h.sign_sq, hε]
  · simp only [Equiv.trans_apply, Equiv.symm_apply_apply, h.degree_eq]
    rw [hr]
    rcases sq_eq_one_iff.mp (h.sign_sq (σ j)) with hs | hs <;> simp [hs, mul_assoc]
  · simp only [Equiv.trans_apply, Equiv.symm_apply_apply, h.t_eq]
    rw [ht]
    rcases sq_eq_one_iff.mp (h.sign_sq (σ j)) with hs | hs <;> simp [hs, mul_assoc]
  · intro i
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, h.z_eq]
    rw [hz i]
    rcases sq_eq_one_iff.mp (h.sign_sq (σ j)) with hs | hs <;> simp [hs, mul_assoc]

theorem degreeConstraints {principal : I} (hs : h.sign principal = 1)
    (hd : d.DegreeConstraints principal r) :
    d'.DegreeConstraints (h.equiv principal) r' := by
  constructor
  · rw [h.degree_eq, hs, hd.principal_degree, one_mul]
  · intro k
    obtain ⟨j, rfl⟩ := h.equiv.surjective k
    rw [h.degree_eq]
    exact mul_ne_zero (by intro hz; have := h.sign_sq j; simp [hz] at this) (hd.degree_nonzero j)
  · intro k hk
    obtain ⟨j, rfl⟩ := h.equiv.surjective k
    rw [h.natAbs_eq]
    exact hd.degree_lower j (fun hj => hk (congrArg h.equiv hj))
  · intro k
    obtain ⟨j, rfl⟩ := h.equiv.surjective k
    rw [h.degree_eq, h.zValue_eq, h.t_eq]
    have hi := (hd.multiplicity_integral j).mul_left (h.sign j)
    convert hi using 1 <;> ring
  · intro k
    obtain ⟨j, rfl⟩ := h.equiv.surjective k
    rw [h.degree_eq, h.zValue_eq, h.t_eq]
    rcases sq_eq_one_iff.mp (h.sign_sq j) with hs | hs
    · simpa [hs] using hd.multiplicity_nonneg j
    · convert hd.multiplicity_nonneg j using 1
      simp [hs]
      ring
  · rw [h.columnInner_eq h.t_eq]
    exact hd.orthogonal_t
  · intro i
    rw [h.columnInner_eq (fun j => h.z_eq j i)]
    exact hd.orthogonal_z i
  · exact h.galois hd.galois_symmetry

theorem orderConstraints {g c e : ℕ} (ho : d.OrderConstraints r g c e) :
    d'.OrderConstraints r' g c e := by
  refine ⟨ho.group_pos, ho.centralizer_pos, ho.center_centralizer_pos, ?_, ?_, ?_⟩
  · rw [h.weightedColumn_eq h.t_eq]
    exact ho.zero_t
  · intro i
    rw [h.weightedColumn_eq (fun j => h.z_eq j i),
      h.weightedColumn_eq (fun j => h.z_eq j 0)]
    exact ho.equal_z i
  · rw [h.weightedColumn_eq (fun j => h.z_eq j 0)]
    exact ho.centralizer_identity

omit [Fintype I] [Fintype J] in
theorem rowSeparated (j : I) (hj : d'.RowSeparated r' (h.equiv j)) :
    d.RowSeparated r j := by
  intro k ε hε hr ht hz
  apply h.equiv.injective
  apply hj (h.equiv k) (h.sign k * ε * h.sign j)
  · simp [mul_pow, h.sign_sq, hε]
  · rw [h.degree_eq, h.degree_eq, hr]
    rcases sq_eq_one_iff.mp (h.sign_sq j) with hs | hs <;> simp [hs, mul_assoc]
  · rw [h.t_eq, h.t_eq, ht]
    rcases sq_eq_one_iff.mp (h.sign_sq j) with hs | hs <;> simp [hs, mul_assoc]
  · intro i
    rw [h.z_eq, h.z_eq, hz i]
    rcases sq_eq_one_iff.mp (h.sign_sq j) with hs | hs <;> simp [hs, mul_assoc]

omit [Fintype I] [Fintype J] in
theorem primeConstraints {g : ℕ} (hp : d.PrimeConstraints r g) :
    d'.PrimeConstraints r' g := by
  constructor
  · intro k
    obtain ⟨j, rfl⟩ := h.equiv.surjective k
    rw [h.natAbs_eq]
    exact hp.degree_dvd j
  · intro k hk hsep p hprime hpg
    obtain ⟨j, rfl⟩ := h.equiv.surjective k
    rw [h.natAbs_eq] at hk ⊢
    exact hp.prime_bound j hk (h.rowSeparated j hsep) p hprime hpg

omit [Fintype I] [Fintype J] in
/-- Reverse a simultaneous signed row equivalence. -/
def symm : SignedDegreeEquiv d' d r' r where
  equiv := h.equiv.symm
  sign k := h.sign (h.equiv.symm k)
  sign_sq k := h.sign_sq (h.equiv.symm k)
  degree_eq k := by
    have he := h.degree_eq (h.equiv.symm k)
    simp only [Equiv.apply_symm_apply] at he
    rcases sq_eq_one_iff.mp (h.sign_sq (h.equiv.symm k)) with hs | hs <;>
      simp_all
  t_eq k := by
    have he := h.t_eq (h.equiv.symm k)
    simp only [Equiv.apply_symm_apply] at he
    rcases sq_eq_one_iff.mp (h.sign_sq (h.equiv.symm k)) with hs | hs <;>
      simp_all
  z_eq k i := by
    have he := h.z_eq (h.equiv.symm k) i
    simp only [Equiv.apply_symm_apply] at he
    rcases sq_eq_one_iff.mp (h.sign_sq (h.equiv.symm k)) with hs | hs <;>
      simp_all

omit [Fintype I] [Fintype J] in
theorem rowSeparated_iff (j : I) :
    d'.RowSeparated r' (h.equiv j) ↔ d.RowSeparated r j := by
  refine ⟨h.rowSeparated j, ?_⟩
  intro hj
  apply h.symm.rowSeparated (h.equiv j)
  simpa [symm] using hj

end SignedDegreeEquiv

/-- Interpret an explicitly supplied six-column matrix as decomposition data. -/
def matrixData {K : Type*} (matrix : K → TableIRow) : GeneralizedDecompositionData K where
  dT j := matrix j 0
  iDz i j := matrix j i.succ

omit [Fintype I] [Fintype J] in
/-- A signed row identification transports the degrees by the same signs. -/
def signedDegreeEquivOfMatrix (d : GeneralizedDecompositionData I)
    (matrix : J → TableIRow) (r : I → ℤ) (e : I ≃ J) (ε : I → ℤ)
    (hε : ∀ j, ε j ^ 2 = 1)
    (hm : ∀ j k, d.tableIRow j k = ε j * matrix (e j) k) :
    SignedDegreeEquiv d (matrixData matrix) r
      (fun k => ε (e.symm k) * r (e.symm k)) where
  equiv := e
  sign := ε
  sign_sq := hε
  degree_eq j := by simp
  t_eq j := by
    have ht := hm j 0
    simp only [tableIRow_zero] at ht
    change matrix (e j) 0 = ε j * d.dT j
    rcases sq_eq_one_iff.mp (hε j) with hs | hs <;> simp_all
  z_eq j i := by
    have hz := hm j i.succ
    rw [tableIRow_succ] at hz
    change matrix (e j) i.succ = ε j * d.iDz i j
    rcases sq_eq_one_iff.mp (hε j) with hs | hs <;> simp_all

/-- Transport all numerical constraints along an explicit signed matrix
identification. The principal sign is deduced from the two principal entries. -/
theorem constraints_of_signed_matrix
    {d : GeneralizedDecompositionData I} {principal : I} {r : I → ℤ}
    {matrix : J → TableIRow} {q : J} {g c z : ℕ}
    (e : I ≃ J) (ε : I → ℤ) (hε : ∀ j, ε j ^ 2 = 1)
    (hm : ∀ j k, d.tableIRow j k = ε j * matrix (e j) k)
    (he : e principal = q) (ht : d.dT principal = 1) (hq : matrix q 0 = 1)
    (hd : d.DegreeConstraints principal r) (ho : d.OrderConstraints r g c z)
    (hp : d.PrimeConstraints r g) :
    let r' := fun k => ε (e.symm k) * r (e.symm k)
    (matrixData matrix).DegreeConstraints q r' ∧
      (matrixData matrix).OrderConstraints r' g c z ∧
      (matrixData matrix).PrimeConstraints r' g := by
  let h := signedDegreeEquivOfMatrix d matrix r e ε hε hm
  have hs : h.sign principal = 1 := by
    have hh := hm principal 0
    simpa [tableIRow_zero, ht, he, hq, h, signedDegreeEquivOfMatrix] using hh.symm
  exact ⟨he ▸ h.degreeConstraints hs hd, h.orderConstraints ho, h.primeConstraints hp⟩

end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
