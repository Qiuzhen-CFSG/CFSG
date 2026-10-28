module

public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
public import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Theory.LinearAlgebra.CliffordAlgebra.EvenCenter

/-!
# Center of an odd-dimensional Spin group

For a nondegenerate quadratic form of dimension `2 * m + 1`, with `2 ≤ m`, over
an algebraically closed field in which two is invertible, this module identifies
the abstract center of Mathlib's Clifford `spinGroup` with `rootsOfUnity 2 k`.
This is the concrete Clifford calculation underlying the type-`B_m` center in
GLS3, Chapter 1, Theorem 1.12.5 and Table 1.12.5.

Mathlib defines the Lipschitz group as the subgroup closure of its invertible
Clifford-vector generators, the Pin group by additionally imposing the unitary
condition, and the Spin group as the even part of the Pin group.  Accordingly,
the proof first constructs norm-`-1` vector generators in that closure.  A
central Spin element commutes with their pairwise products and hence with the
whole even Clifford algebra.  The PBW calculation in
`Theory.LinearAlgebra.CliffordAlgebra.EvenCenter` makes it scalar; the unitary
condition then says that the scalar is a second root of unity.  Conversely,
each such scalar belongs to Spin, including `-1`, which is the square of a
norm-`-1` Clifford-vector generator.

The hypothesis `[Invertible (2 : k)]` is essential to the theorem proved here.
Mathlib's `QuadraticMap.Nondegenerate` permits a one-dimensional polar radical,
so odd-dimensional nonsingular forms are meaningful in characteristic two;
they are not vacuous.  Neither the imported PBW scalar-center theorem nor the
current odd Spin/SO action interface covers that case.  Thus this module makes
the characteristic-not-two boundary explicit and proves no characteristic-two
center assertion.
-/

open CliffordAlgebra

universe u

namespace Theory.AlgebraicGroup

variable {k V : Type u} [Field k] [IsAlgClosed k] [Invertible (2 : k)]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {q : QuadraticForm k V}

private noncomputable def cliffordUnitOfNormNegOne (v : V) (hv : q v = -1) :
    (CliffordAlgebra q)ˣ where
  val := ι q v
  inv := -ι q v
  val_inv := by simp [ι_sq_scalar, hv]
  inv_val := by simp [ι_sq_scalar, hv]

omit [IsAlgClosed k] [Invertible (2 : k)] [FiniteDimensional k V] in
@[simp]
private lemma cliffordUnitOfNormNegOne_val (v : V) (hv : q v = -1) :
    (cliffordUnitOfNormNegOne v hv : CliffordAlgebra q) = ι q v :=
  rfl

omit [IsAlgClosed k] [Invertible (2 : k)] [FiniteDimensional k V] in
private lemma normNegOne_mem_pinGroup (v : V) (hv : q v = -1) :
    ι q v ∈ pinGroup q := by
  rw [pinGroup.mem_iff]
  refine ⟨?_, ?_⟩
  · refine ⟨cliffordUnitOfNormNegOne v hv, ?_, rfl⟩
    exact Subgroup.subset_closure ⟨v, cliffordUnitOfNormNegOne_val v hv⟩
  · exact ⟨by simp [hv], by simp [hv]⟩

omit [IsAlgClosed k] [Invertible (2 : k)] [FiniteDimensional k V] in
private lemma normNegOne_pair_mem_spinGroup (v w : V)
    (hv : q v = -1) (hw : q w = -1) :
    ι q v * ι q w ∈ spinGroup q := by
  rw [spinGroup.mem_iff]
  exact ⟨mul_mem (normNegOne_mem_pinGroup v hv) (normNegOne_mem_pinGroup w hw),
    ι_mul_ι_mem_evenOdd_zero q v w⟩

private lemma exists_normNegOne_basis (hq : q.Nondegenerate) :
    ∃ b : Module.Basis (Fin (Module.finrank k V)) k V, ∀ i, q (b i) = -1 := by
  classical
  have hq' : (QuadraticMap.associated (R := k) q).SeparatingLeft :=
    ((QuadraticMap.nondegenerate_associated_iff).mpr hq).1
  obtain ⟨e⟩ := q.equivalent_weightedSumSquares_of_isAlgClosed hq'
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_eq_mul_self (-1 : k)
  have hc0 : c ≠ 0 := by
    intro hc0
    simp [hc0] at hc
  let b0 : Module.Basis (Fin (Module.finrank k V)) k V :=
    (Pi.basisFun k (Fin (Module.finrank k V))).map e.toLinearEquiv.symm
  let b := b0.unitsSMul (fun _ => Units.mk0 c hc0)
  refine ⟨b, fun i => ?_⟩
  have hb0 : q (b0 i) = 1 := by
    dsimp [b0]
    rw [e.symm.map_app]
    simp [QuadraticMap.weightedSumSquares_apply, Pi.single_apply]
  simp only [b, Module.Basis.unitsSMul_apply, Units.smul_def, QuadraticMap.map_smul, hb0,
    Units.val_mk0]
  simpa [smul_eq_mul] using hc.symm

omit [IsAlgClosed k] [Invertible (2 : k)] [FiniteDimensional k V] in
private lemma center_commutes_normNegOne_pair
    (z : Subgroup.center (spinGroup q)) (v w : V)
    (hv : q v = -1) (hw : q w = -1) :
    (z.1 : CliffordAlgebra q) * (ι q v * ι q w) =
      (ι q v * ι q w) * (z.1 : CliffordAlgebra q) := by
  let s : spinGroup q := ⟨ι q v * ι q w, normNegOne_pair_mem_spinGroup v w hv hw⟩
  have h := (Subgroup.mem_center_iff.mp z.property s).symm
  exact congrArg (fun t : spinGroup q => (t : CliffordAlgebra q)) h

private lemma center_spinGroup_commutes_even
    (hq : q.Nondegenerate) (z : Subgroup.center (spinGroup q)) :
    ∀ y : CliffordAlgebra q, y ∈ even q →
      (z.1 : CliffordAlgebra q) * y = y * (z.1 : CliffordAlgebra q) := by
  obtain ⟨b, hb⟩ := exists_normNegOne_basis hq
  have hpair (v w : V) :
      (z.1 : CliffordAlgebra q) * (ι q v * ι q w) =
        (ι q v * ι q w) * (z.1 : CliffordAlgebra q) := by
    rw [← b.sum_repr v, ← b.sum_repr w]
    simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
      mul_smul_comm, smul_mul_assoc]
    simp_rw [center_commutes_normNegOne_pair z _ _ (hb _) (hb _)]
  intro y hy
  induction y, hy using CliffordAlgebra.even_induction q with
  | algebraMap r => exact (Algebra.commutes r (z.1 : CliffordAlgebra q)).symm
  | add x y hx hy ihx ihy => simp only [mul_add, add_mul, ihx, ihy]
  | ι_mul_ι_mul v w y hy ih =>
      rw [← mul_assoc, hpair, mul_assoc, ih, ← mul_assoc]

private lemma exists_normNegOne (hq : q.Nondegenerate)
    (hpos : 0 < Module.finrank k V) : ∃ v : V, q v = -1 := by
  obtain ⟨b, hb⟩ := exists_normNegOne_basis hq
  exact ⟨b ⟨0, hpos⟩, hb ⟨0, hpos⟩⟩

private lemma scalar_sq_one_mem_spinGroup (hq : q.Nondegenerate)
    (hpos : 0 < Module.finrank k V) (a : k) (ha : a ^ 2 = 1) :
    algebraMap k (CliffordAlgebra q) a ∈ spinGroup q := by
  rw [spinGroup.mem_iff, pinGroup.mem_iff]
  refine ⟨⟨?_, ?_⟩, (even q).algebraMap_mem a⟩
  · rcases sq_eq_one_iff.mp ha with rfl | rfl
    · exact ⟨1, one_mem _, by simp⟩
    · obtain ⟨v, hv⟩ := exists_normNegOne hq hpos
      let u := cliffordUnitOfNormNegOne v hv
      refine ⟨u * u, mul_mem ?_ ?_, ?_⟩
      · exact Subgroup.subset_closure ⟨v, cliffordUnitOfNormNegOne_val v hv⟩
      · exact Subgroup.subset_closure ⟨v, cliffordUnitOfNormNegOne_val v hv⟩
      · simp [u, cliffordUnitOfNormNegOne, ι_sq_scalar, hv]
  · exact ⟨by rw [CliffordAlgebra.star_algebraMap, ← map_mul, ← pow_two, ha, map_one],
      by rw [CliffordAlgebra.star_algebraMap, ← map_mul, ← pow_two, ha, map_one]⟩

omit [IsAlgClosed k] [Invertible (2 : k)] in
private lemma root_coe_sq (ω : rootsOfUnity 2 k) : (ω.1 : k) ^ 2 = 1 := by
  have hω := (mem_rootsOfUnity 2 (ω : kˣ)).mp ω.property
  simpa using congrArg ((↑) : kˣ → k) hω

private noncomputable def rootsToSpinCenter (hq : q.Nondegenerate)
    (hpos : 0 < Module.finrank k V) :
    rootsOfUnity 2 k →* Subgroup.center (spinGroup q) where
  toFun ω :=
    ⟨⟨algebraMap k (CliffordAlgebra q) (ω.1 : k),
        scalar_sq_one_mem_spinGroup hq hpos (ω.1 : k) (root_coe_sq ω)⟩,
      Subgroup.mem_center_iff.mpr fun g => by
        apply Subtype.ext
        exact (Algebra.commutes (ω.1 : k) (g : CliffordAlgebra q)).symm⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  map_mul' ω η := by
    apply Subtype.ext
    apply Subtype.ext
    simp

private lemma rootsToSpinCenter_injective (hq : q.Nondegenerate)
    (hpos : 0 < Module.finrank k V) :
    Function.Injective (rootsToSpinCenter (q := q) hq hpos) := by
  intro ω η h
  apply Subtype.ext
  apply Units.ext
  apply FaithfulSMul.algebraMap_injective k (CliffordAlgebra q)
  exact congrArg (fun z : Subgroup.center (spinGroup q) =>
    (z.1 : CliffordAlgebra q)) h

private lemma rootsToSpinCenter_surjective (m : ℕ) (hq : q.Nondegenerate)
    (hdim : Module.finrank k V = 2 * m + 1) (hpos : 0 < Module.finrank k V) :
    Function.Surjective (rootsToSpinCenter (q := q) hq hpos) := by
  intro z
  have hodd : Odd (Module.finrank k V) := ⟨m, hdim⟩
  obtain ⟨a, ha⟩ :=
    CliffordAlgebra.eq_algebraMap_of_mem_even_of_commute_even hq hodd
      (z.1 : CliffordAlgebra q) (spinGroup.mem_even z.1.property)
      (center_spinGroup_commutes_even hq z)
  have ha2 : a ^ 2 = 1 := by
    have hmap :
        algebraMap k (CliffordAlgebra q) a * algebraMap k (CliffordAlgebra q) a = 1 := by
      simpa only [ha, CliffordAlgebra.star_algebraMap] using
        spinGroup.star_mul_self_of_mem z.1.property
    rw [pow_two]
    apply FaithfulSMul.algebraMap_injective k (CliffordAlgebra q)
    simpa only [map_mul, map_one] using hmap
  let ua : kˣ := ⟨a, a, by simpa [pow_two] using ha2, by simpa [pow_two] using ha2⟩
  let ω : rootsOfUnity 2 k := ⟨ua, (mem_rootsOfUnity 2 ua).mpr (by
    apply Units.ext
    exact ha2)⟩
  refine ⟨ω, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact ha.symm

/-- The abstract center of Mathlib's Clifford Spin group in odd type `B_m` is
the group of second roots of unity.  The explicit rank bound matches the
standard type-`B` range used by the odd-orthogonal model. -/
public noncomputable def spinGroup_center_iso_rootsOfUnity_two
    (m : ℕ) (hm : 2 ≤ m) (hq : q.Nondegenerate)
    (hdim : Module.finrank k V = 2 * m + 1) :
    Subgroup.center (spinGroup q) ≃* rootsOfUnity 2 k := by
  have hmpos : 0 < m := lt_of_lt_of_le (by decide) hm
  have hpos : 0 < Module.finrank k V := by omega
  exact
    (MulEquiv.ofBijective (rootsToSpinCenter (q := q) hq hpos)
      ⟨rootsToSpinCenter_injective hq hpos,
        rootsToSpinCenter_surjective m hq hdim hpos⟩).symm

end Theory.AlgebraicGroup
