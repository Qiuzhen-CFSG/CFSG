module

public import Theory.AlgebraicGroup.Instance.SL
public import Theory.AlgebraicGroup.ClosedSubgroup.Basic
public import Theory.AlgebraicGroup.Morphism.Operations

/-!
# The diagonal centralizer inside the determinant-one three-dimensional group

For a product-one triple of nonzero scalars, this is the actual closed
centralizer of its diagonal matrix in the affine SL₃ variety. The point
equivalence retains matrix entries, and its centralizer condition is exactly
the usual equality of row and column weights. Repeated weights are allowed,
including a scalar diagonal matrix, whose centralizer is all of SL₃.

This is the block-variety interface for the octonion proof of the G₂ case of
Steinberg 8.5 and 12.5 (`refs/KGroup/GLS3/Chapter2St2.tex`). Connectedness and
the regular comparison with the octonion model are separate obligations.
-/

@[expose] public section

open Theory.AlgebraicGroup
namespace Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight
noncomputable section
variable {K : Type*} [Field K] [IsAlgClosed K]

def diagonalSL (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1) :
    Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.diagonal (fun i => (d i : K)), by
    rw [Matrix.det_diagonal]
    exact (map_prod (Units.coeHom K) d Finset.univ).symm.trans (congrArg Units.val hd)⟩

def slPointMulEquiv : Variety.Point (slVariety K 3) ≃*
    Matrix.SpecialLinearGroup (Fin 3) K where
  __ := slPointEquiv 3
  map_mul' _ _ := rfl

def blockClosedSubgroup (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1) :
    ClosedSubgroup (slVariety K 3) :=
  ClosedSubgroup.ofSubgroup (Subgroup.centralizer {slPointMulEquiv.symm (diagonalSL d hd)}) (by
    have h := Variety.Morphism.isZariskiClosed_equalizer
      (leftMulMorphism (slVariety K 3) (slPointMulEquiv.symm (diagonalSL d hd)))
      (rightMulMorphism (slVariety K 3) (slPointMulEquiv.symm (diagonalSL d hd)))
    convert h using 1
    ext x
    change x ∈ Subgroup.centralizer {slPointMulEquiv.symm (diagonalSL d hd)} ↔ _
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact eq_comm)

abbrev blockVariety (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1) : Variety K :=
  (blockClosedSubgroup d hd).carrierVariety

instance (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1) : AlgebraicGroup (blockVariety d hd) :=
  (blockClosedSubgroup d hd).carrierAlgebraicGroup

def blockPointEquiv (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1) :
    Variety.Point (blockVariety d hd) ≃*
      Subgroup.centralizer ({diagonalSL d hd} : Set (Matrix.SpecialLinearGroup (Fin 3) K)) where
  toFun p := ⟨slPointMulEquiv ((blockClosedSubgroup d hd).pointEquiv p).val, by
    have h := ((blockClosedSubgroup d hd).pointEquiv p).property
    change _ ∈ Subgroup.centralizer {slPointMulEquiv.symm (diagonalSL d hd)} at h
    rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg slPointMulEquiv h⟩
  invFun z := (blockClosedSubgroup d hd).pointEquiv.symm
    ⟨slPointMulEquiv.symm z.val, by
      change slPointMulEquiv.symm z.val ∈
        Subgroup.centralizer {slPointMulEquiv.symm (diagonalSL d hd)}
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply slPointMulEquiv.injective
      simpa only [map_mul, MulEquiv.apply_symm_apply] using
        Subgroup.mem_centralizer_singleton_iff.mp z.property⟩
  left_inv p := by
    apply (blockClosedSubgroup d hd).pointEquiv.injective
    apply Subtype.ext
    exact slPointMulEquiv.symm_apply_apply _
  right_inv z := by
    apply Subtype.ext
    exact slPointMulEquiv.apply_symm_apply _
  map_mul' p q := by
    apply Subtype.ext
    exact slPointMulEquiv.map_mul _ _

theorem blockPointEquiv_entry (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1)
    (p : Variety.Point (blockVariety d hd)) (i j : Fin 3) :
    ((blockPointEquiv d hd p).val : Matrix (Fin 3) (Fin 3) K) i j =
      p.val (ULift.up (i,j)) := rfl

omit [IsAlgClosed K] in
theorem mem_diagonalSL_centralizer_iff (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1)
    (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    A ∈ Subgroup.centralizer ({diagonalSL d hd} : Set (Matrix.SpecialLinearGroup (Fin 3) K)) ↔
      ∀ i j, (d i : K) * A.1 i j = (d j : K) * A.1 i j := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h i j
    have h' := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 3) K => M.1 i j) h
    change (A.1 * Matrix.diagonal (fun i => (d i : K))) i j =
      (Matrix.diagonal (fun i => (d i : K)) * A.1) i j at h'
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm] using h'.symm
  · intro h
    apply Subtype.ext
    ext i j
    change (A.1 * Matrix.diagonal (fun i => (d i : K))) i j =
      (Matrix.diagonal (fun i => (d i : K)) * A.1) i j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm] using (h i j).symm


end
end Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight
