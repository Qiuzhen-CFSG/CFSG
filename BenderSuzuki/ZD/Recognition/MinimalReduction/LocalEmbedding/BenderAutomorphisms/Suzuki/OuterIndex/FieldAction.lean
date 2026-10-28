module

public import BenderSuzuki.MatrixGroups.Suzuki

/-!
# Field automorphisms of the concrete Suzuki group

An automorphism of `GF(2^(2m+1))` over its prime field acts entrywise on the
Suzuki matrices. It preserves each family of root and torus generators and
fixes the Weyl matrix, so it restricts to a group automorphism. Root entries
make this action faithful. Finite Galois theory gives the field automorphism
group order `2m+1`.

This constructs the field subgroup occurring in GLS, Volume 3,
Theorem 2.5.12(d), and Volume 4, Chapter 4, Lemma 3.1(a). It does not assert
that this subgroup covers the outer automorphism group; that requires the
separate classification of arbitrary automorphisms.
-/

namespace BenderSuzuki.MatrixGroups

open PFAppendixIII

private theorem field_map_root (m : ℕ)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1))
    (a b : BinaryGaloisField (2 * m + 1)) :
    Matrix.GeneralLinearGroup.map σ.toRingHom (SuzukiRootGL m a b) =
      SuzukiRootGL m (σ a) (σ b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map_apply, SuzukiRootGL, SuzukiRootMatrix]

private theorem field_map_torus (m : ℕ)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1))
    (x : (BinaryGaloisField (2 * m + 1))ˣ) :
    Matrix.GeneralLinearGroup.map σ.toRingHom (SuzukiTorusGL m x) =
      SuzukiTorusGL m (Units.map σ.toRingHom x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map_apply, SuzukiTorusGL, SuzukiTorusMatrix]

private theorem field_map_weyl (m : ℕ)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1)) :
    Matrix.GeneralLinearGroup.map σ.toRingHom (SuzukiWeylGL m) =
      SuzukiWeylGL m := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map_apply, SuzukiWeylGL, SuzukiWeylMatrix]

private theorem field_map_generator (m : ℕ)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1))
    (A : GL (Fin 4) (BinaryGaloisField (2 * m + 1)))
    (hA : A ∈ SuzukiMatrixGeneratorSet m) :
    Matrix.GeneralLinearGroup.map σ.toRingHom A ∈ SuzukiMatrixGeneratorSet m := by
  change (∃ a b, A = SuzukiRootGL m a b) ∨
    (∃ x, A = SuzukiTorusGL m x) ∨ A = SuzukiWeylGL m at hA
  change (∃ a b, Matrix.GeneralLinearGroup.map σ.toRingHom A = SuzukiRootGL m a b) ∨
    (∃ x, Matrix.GeneralLinearGroup.map σ.toRingHom A = SuzukiTorusGL m x) ∨
    Matrix.GeneralLinearGroup.map σ.toRingHom A = SuzukiWeylGL m
  rcases hA with ⟨a, b, rfl⟩ | ⟨x, rfl⟩ | rfl
  · left
    exact ⟨σ a, σ b, field_map_root m σ a b⟩
  · right; left
    refine ⟨Units.map σ.toRingHom x, ?_⟩
    exact field_map_torus m σ x
  · right; right
    exact field_map_weyl m σ

private theorem field_map_mem (m : ℕ)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1))
    (A : GL (Fin 4) (BinaryGaloisField (2 * m + 1)))
    (hA : A ∈ SuzukiMatrixSubgroup m) :
    Matrix.GeneralLinearGroup.map σ.toRingHom A ∈ SuzukiMatrixSubgroup m := by
  let f := Matrix.GeneralLinearGroup.map (n := Fin 4) σ.toRingHom
  have hle : SuzukiMatrixSubgroup m ≤ (SuzukiMatrixSubgroup m).comap f := by
    rw [SuzukiMatrixSubgroup, Subgroup.closure_le]
    intro B hB
    change f B ∈ SuzukiMatrixSubgroup m
    exact Subgroup.subset_closure (field_map_generator m σ B hB)
  exact hle hA

/-- Apply a defining-field automorphism to every matrix entry. -/
public noncomputable def suzukiFieldAut (m : ℕ)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1)) :
    MulAut (SuzukiMatrixGroup m) where
  toFun g := ⟨Matrix.GeneralLinearGroup.map σ.toRingHom g.val,
    field_map_mem m σ g.val g.property⟩
  invFun g := ⟨Matrix.GeneralLinearGroup.map σ.symm.toRingHom g.val,
    field_map_mem m σ.symm g.val g.property⟩
  left_inv g := by
    apply Subtype.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.map_apply]
  right_inv g := by
    apply Subtype.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.map_apply]
  map_mul' g h := Subtype.ext (map_mul _ _ _)

/-- The field action is the literal entrywise action on the concrete model. -/
public theorem suzukiFieldAut_apply_entry (m : ℕ)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1))
    (g : SuzukiMatrixGroup m) (i j : Fin 4) :
    ((suzukiFieldAut m σ g).val : Matrix (Fin 4) (Fin 4)
      (BinaryGaloisField (2 * m + 1))) i j = σ (g.val i j) := by
  rfl

/-- Field automorphisms act homomorphically on the Suzuki group. -/
public noncomputable def suzukiFieldAutHom (m : ℕ) :
    (BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1)) →*
      MulAut (SuzukiMatrixGroup m) where
  toFun := suzukiFieldAut m
  map_one' := by
    ext g i j
    simp [suzukiFieldAut_apply_entry]
  map_mul' σ τ := by
    ext g i j
    simp [suzukiFieldAut_apply_entry, MulAut.mul_apply]

public theorem suzukiFieldAutHom_apply (m : ℕ)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1)) :
    suzukiFieldAutHom m σ = suzukiFieldAut m σ := by rfl

/-- Root entries detect every field parameter, so the field action is faithful. -/
public theorem suzukiFieldAutHom_injective (m : ℕ) :
    Function.Injective (suzukiFieldAutHom m) := by
  intro σ τ h
  ext a
  let g : SuzukiMatrixGroup m :=
    ⟨SuzukiRootGL m a 0, Subgroup.subset_closure (Or.inl ⟨a, 0, rfl⟩)⟩
  have hentry := congrArg
    (fun α : MulAut (SuzukiMatrixGroup m) => (α g).val (0 : Fin 4) (1 : Fin 4)) h
  simpa [suzukiFieldAutHom_apply, suzukiFieldAut_apply_entry,
    g, SuzukiRootGL, SuzukiRootMatrix] using hentry

/-- The defining field has exactly `2m+1` automorphisms over its prime field. -/
public theorem suzukiFieldAut_card (m : ℕ) :
    Nat.card (BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2]
      BinaryGaloisField (2 * m + 1)) = 2 * m + 1 := by
  rw [IsGalois.card_aut_eq_finrank]
  exact GaloisField.finrank 2 (by omega)

end BenderSuzuki.MatrixGroups
