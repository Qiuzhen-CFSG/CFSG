module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.SplitNormalForm.CellSeparation.Height
public import Theory.AlgebraicGroup.RootSystems.IntegralRootCurveSimpleGeneration

/-!
# Root columns of the supplied split Weyl representatives

The literal matrix of `D.lift w` sends each root basis vector to the basis
vector indexed by `w.val r`. Thus its root columns have a single entry one,
including zero entries in every Cartan row. In particular the entry used to
separate the Borel from the Weyl subgroup is nonzero.

The simple case specializes the integral Tits action: its root-string sign
becomes one in characteristic two. `Inputs.simple` identifies these actual
matrix words with the supplied representatives, and subgroup induction extends
the action through products and inverses. Only the supplied Weyl equivalence
and its generator correspondence enter this argument.

Source: GLS3 2.3.4–5 and §2.4, `refs/KGroup/GLS3/chapter2.tex`, with the
integral Tits action proved in `IntegralGeckConstruction`.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Matrix
namespace Triality.Standard.ConcreteBruhat.SplitNormalForm.CellSeparation
noncomputable section
open Parabolics Parabolics.RankOneMatrices
attribute [local instance] matrixLatticeDecidableEq

/-- The actual simple Weyl word is the scalar extension of the integral Tits lift. -/
lemma matrix_weylWord_one (P : Parameters) (i : Fin 4) :
    matrix P (weylWord P i 1) =
      specializeMatrix (titsLift (typeDRootPairing_baseEquiv 2 i)) := by
  have h := rootCurveTitsWord_cons
    (S := ExtensionField P) (typeDRootPairing_baseEquiv 2 i) []
  rw [rootCurveTitsWord_nil, mul_one] at h
  have hv := congrArg Units.val h
  change specializeMatrix (titsLift (typeDRootPairing_baseEquiv 2 i) * 1) = _ at hv
  rw [mul_one] at hv
  change (RootPairing.SimpleGeckGroup.positiveUnit _ 1 *
    RootPairing.SimpleGeckGroup.negativeUnit _ (-(1 : ExtensionField P)⁻¹) *
    RootPairing.SimpleGeckGroup.positiveUnit _ 1).val = _
  rw [inv_one]
  exact hv.symm

/-- All entries of a simple Weyl root column; the integral sign disappears. -/
lemma matrix_weylWord_one_root_column (P : Parameters) (hp : P.prime = 2)
    (i : Fin 4) (r : TypeDRootIndex 4) (j : LatticeIndex) :
    matrix P (weylWord P i 1) j (.inr r) =
      if j = .inr (rootReflection i r) then 1 else 0 := by
  let := rankOneExtensionCharTwo P hp
  rw [matrix_weylWord_one]
  have h := congrFun (titsLift_mulVec_v (typeDRootPairing_baseEquiv 2 i) r) j
  simp only [v, Matrix.mulVec_single_one, Matrix.col_apply,
    typeDRootPairing_baseEquiv_val] at h
  change ((titsLift _ j (.inr r) : ℤ) : ExtensionField P) = _
  rw [h]
  simp only [Pi.single_apply, Pi.smul_apply, zsmul_eq_mul, Int.cast_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one, CharTwo.neg_eq, one_pow, one_mul,
    rootReflection]
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero]
  rfl

private lemma matrixHom_inv_mulVec {G R I : Type*} [Group G] [CommRing R]
    [Fintype I] [DecidableEq I] (f : G →* Matrix I I R) (g : G)
    (v u : I → R) (h : f g *ᵥ v = u) : f g⁻¹ *ᵥ u = v := by
  rw [← h, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]

/-- Every supplied Weyl representative permutes the root basis vectors literally. -/
lemma matrix_lift_mulVec_root (P : Parameters) (hp : P.prime = 2)
    (D : Inputs P) (w : rootWeylGroup) :
    ∀ r : TypeDRootIndex 4,
      matrix P (D.lift w) *ᵥ Pi.single (.inr r) 1 =
        Pi.single (.inr (w.val r)) 1 := by
  rcases w with ⟨w, hw⟩
  change w ∈ Subgroup.closure (Set.range rootReflection) at hw
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      intro r
      change matrix P (D.lift (rootWeylGenerator i)) *ᵥ _ = _
      rw [D.lift_simple, Matrix.mulVec_single_one]
      ext j
      simpa only [Matrix.col_apply, Pi.single_apply] using
        matrix_weylWord_one_root_column P hp i r j
  | one =>
      intro r
      change matrix P (D.lift 1) *ᵥ _ = _
      simp only [map_one, Matrix.one_mulVec]
      rfl
  | mul x y hx hy ihx ihy =>
      intro r
      change matrix P (D.lift (⟨x, hx⟩ * ⟨y, hy⟩)) *ᵥ _ = _
      rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ihy, ihx]
      rfl
  | inv x hx ih =>
      intro r
      change matrix P (D.lift ((⟨x, hx⟩ : rootWeylGroup)⁻¹)) *ᵥ
        Pi.single (.inr r) 1 = Pi.single (.inr (x⁻¹ r)) 1
      have h := matrixHom_inv_mulVec ((matrix P).comp D.lift)
        (⟨x, hx⟩ : rootWeylGroup) _ _ (ih (x⁻¹ r))
      simpa only [MonoidHom.comp_apply, Subgroup.coe_mk,
        Equiv.Perm.inv_def, Equiv.apply_symm_apply] using h

/-- The full root column, for every positive binary exponent, including `n = 1`. -/
lemma matrix_lift_root_column (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (w : rootWeylGroup)
    (r : TypeDRootIndex 4) (j : LatticeIndex) :
    matrix _ (D.lift w) j (.inr r) = if j = .inr (w.val r) then 1 else 0 := by
  have h := congrFun (matrix_lift_mulVec_root (binaryParameters n hn) rfl D w r) j
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] using h

/-- The Weyl permutation position in each root column has coefficient one. -/
lemma matrix_lift_root_pivot (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (w : rootWeylGroup)
    (r : TypeDRootIndex 4) :
    matrix _ (D.lift w) (.inr (w.val r)) (.inr r) = 1 := by
  rw [matrix_lift_root_column, if_pos rfl]

/-- The precise pivot premise of `borel_inf_normalizer_of_matrix_entries`. -/
lemma matrix_lift_root_pivot_ne_zero (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (w : rootWeylGroup)
    (r : TypeDRootIndex 4) :
    matrix _ (D.lift w) (.inr (w.val r)) (.inr r) ≠ 0 := by
  rw [matrix_lift_root_pivot]
  exact one_ne_zero

end
end Triality.Standard.ConcreteBruhat.SplitNormalForm.CellSeparation
