module
public import Theory.AlgebraicGroup.RootSystems.SymplecticElementaryGeneration
import all Theory.AlgebraicGroup.RootSystems.SymplecticElementaryGeneration

/-!
# Matrix points of the standard symplectic variety

The concrete symplectic matrix group is exactly the point group of the connected standard symplectic carrier. Matrix entries are its standard coordinates and the inverse-determinant coordinate is constantly one. This bridge supports the polynomial exceptional B₂ endomorphism used in Steinberg–Lang descent.

The intentional internal import of SymplecticElementaryGeneration exposes its proved matrix realization only inside these proofs; clients receive the matrix equivalence and coordinate equations. No existing carrier or generation module is changed.
-/

noncomputable section
namespace Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

public def symplecticMatrixPointEquiv (m : ℕ) :
    Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety ≃*
      Matrix.symplecticGroup (Fin m) k := by
  let f : Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety →*
      Matrix.symplecticGroup (Fin m) k := MonoidHom.mk'
        (fun x => ⟨symplecticClosedPointMatrix m x,symplecticClosedPointMatrix_mem m x⟩)
        (fun x y => Subtype.ext (symplecticClosedPointMatrix_mul m x y))
  apply MulEquiv.ofBijective f
  constructor
  · intro x y hxy
    exact symplecticClosedPointMatrix_injective m (congrArg Subtype.val hxy)
  · intro g
    obtain ⟨x,_,hx⟩ := isElementaryMatrix_of_symplectic g.val g.property
    exact ⟨x,Subtype.ext hx⟩

public theorem symplecticMatrixPointEquiv_val (m : ℕ)
    (x : Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety) :
    (symplecticMatrixPointEquiv m x).val = symplecticClosedPointMatrix m x := by rfl

public theorem symplecticMatrixPointEquiv_entry (m : ℕ)
    (x : Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety)
    (i j : Fin m ⊕ Fin m) :
    (symplecticMatrixPointEquiv m x).val i j =
      x.val (Sum.inl (symplecticStandardIndexEquiv (k := k) m i,
        symplecticStandardIndexEquiv (k := k) m j)) :=
  symplecticClosedPointMatrix_entry m x i j

public theorem symplecticPoint_scalar (m : ℕ)
    (x : Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety) :
    x.val (Sum.inr PUnit.unit) = 1 := by
  let y := (standardSymplecticClosedSubgroup (k := k) m).inclusion.onPoints x
  have hd : (glMatrixOfPoint _ y).det = 1 := by
    have he : glMatrixOfPoint _ y =
        Matrix.reindex (symplecticStandardIndexEquiv (k := k) m)
          (symplecticStandardIndexEquiv (k := k) m) (symplecticMatrixPointEquiv m x).val := by
      ext i j
      change x.val (Sum.inl (i,j)) = _
      simpa only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.apply_symm_apply] using
        (symplecticMatrixPointEquiv_entry m x
          ((symplecticStandardIndexEquiv (k := k) m).symm i)
          ((symplecticStandardIndexEquiv (k := k) m).symm j)).symm
    rw [he,Matrix.det_reindex_self]
    exact SymplecticGroup.det_eq_one (symplecticMatrixPointEquiv m x).property
  have hh := glPoint_det_mul_scalar _ y
  rw [hd,one_mul] at hh
  exact hh
end Theory.AlgebraicGroup
