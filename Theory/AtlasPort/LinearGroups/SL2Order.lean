module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.Index

/-!
# Order of the special linear group in dimension two

The determinant map GL₂ → Fˣ is onto, and its kernel is SL₂. The known
GL₂ count and cancellation of q − 1 therefore give q(q² − 1).
Adapted from `BenderSuzuki.External.huppert614_card_specialLinearGroup` in
`BenderSuzuki/External/Huppert/II/theorem_6_14.lean`; this standalone proof
has no dependency on the Bender–Suzuki layer. The public name preserves
`Atlas/LinearGroups/SL2Order.lean` from ATLAS revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917 (LICENSES/ATLAS.txt).
-/

@[expose] public section
namespace Atlas
universe u

theorem card_sl_two
    {F : Type u} [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hdet_range_top :
      (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)).range = ⊤ := by
    ext u
    constructor
    · intro _
      simp
    · intro _
      let diagonalGL : GL (Fin 2) F :=
        Matrix.GeneralLinearGroup.mkOfDetNeZero
          (Matrix.diagonal ![(u : F), 1]) (by
            simp [Matrix.det_diagonal, Fin.prod_univ_two])
      refine ⟨diagonalGL, ?_⟩
      ext
      simp [diagonalGL, Matrix.det_diagonal, Fin.prod_univ_two]
  have hGL :
      Nat.card (GL (Fin 2) F) =
        (Nat.card F ^ 2 - 1) * (Nat.card F ^ 2 - Nat.card F) := by
    simpa [Fin.prod_univ_two] using
      (Matrix.card_GL_field (𝔽 := F) 2)
  let detHom := Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)
  have hRange : Nat.card detHom.range = Nat.card F - 1 := by
    rw [hdet_range_top]
    simpa using (Fintype.card_units (α := F))
  have hmul :
      Nat.card detHom.range * Nat.card detHom.ker =
        Nat.card (GL (Fin 2) F) := by
    rw [← Subgroup.index_ker detHom]
    exact detHom.ker.index_mul_card
  have hker :
      Nat.card detHom.ker = Nat.card F * (Nat.card F ^ 2 - 1) := by
    have hdiff :
        Nat.card F ^ 2 - Nat.card F = Nat.card F * (Nat.card F - 1) := by
      rw [pow_two]
      calc
        Nat.card F * Nat.card F - Nat.card F =
            Nat.card F * Nat.card F - Nat.card F * 1 := by simp
        _ = Nat.card F * (Nat.card F - 1) :=
          (Nat.mul_sub_left_distrib _ _ _).symm
    have hcancel :
        (Nat.card F - 1) * Nat.card detHom.ker =
          (Nat.card F - 1) * (Nat.card F * (Nat.card F ^ 2 - 1)) := by
      calc
        (Nat.card F - 1) * Nat.card detHom.ker =
            Nat.card (GL (Fin 2) F) := by
          rw [hRange] at hmul
          exact hmul
        _ = (Nat.card F ^ 2 - 1) *
            (Nat.card F ^ 2 - Nat.card F) := hGL
        _ = (Nat.card F - 1) *
            (Nat.card F * (Nat.card F ^ 2 - 1)) := by
          rw [hdiff]
          ring
    exact Nat.eq_of_mul_eq_mul_left
      (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := F))) hcancel
  calc
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
        Nat.card detHom.ker := by
      let slEquivDetKer :
          Matrix.SpecialLinearGroup (Fin 2) F ≃ detHom.ker := by
        refine Equiv.ofBijective
          (fun A => ⟨Matrix.SpecialLinearGroup.toGL A, by
            exact Matrix.SpecialLinearGroup.coeToGL_det A⟩) ?_
        constructor
        · intro A B h
          apply Matrix.SpecialLinearGroup.toGL_injective
          exact congrArg Subtype.val h
        · intro A
          refine ⟨⟨(A : GL (Fin 2) F), ?_⟩, ?_⟩
          · have hmem := A.property
            change Matrix.GeneralLinearGroup.det (A : GL (Fin 2) F) = 1 at hmem
            exact Units.ext_iff.mp hmem
          · apply Subtype.ext
            apply Matrix.GeneralLinearGroup.ext
            intro i j
            rfl
      exact Nat.card_congr slEquivDetKer
    _ = Nat.card F * (Nat.card F ^ 2 - 1) := hker

end Atlas
