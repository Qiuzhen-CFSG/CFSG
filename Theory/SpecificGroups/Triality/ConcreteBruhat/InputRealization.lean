module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl
public import Theory.SpecificGroups.Triality.ConcreteBruhat.SplitNormalForm

/-!
# Discharging the concrete split Bruhat inputs

The actual matrix/root Weyl equivalence and faithful coroot coordinates satisfy
all inputs of the split normal-form theorem. Integral divided-power homogeneity
proves the torus action on every canonical root curve, including negative roots.
The character is transported through the proved four-coordinate torus
isomorphism. Thus the normal form now applies without any matrix-realization or
Borel-factorization assumptions, also at q = 2.

Source: GLS3 2.3.4–8 and the coroot relations of §2.4,
`refs/KGroup/GLS3/chapter2.tex`. The left-conjugation convention agrees with the
original word h(t) = n(t)n(-1).
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.ConcreteBruhat.InputRealization
open Parabolics Parabolics.RankOneMatrices TorusCoordinates SplitNormalForm
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
local instance inputMatrixDecidableEq : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

private lemma weight_support (i : Fin 4) (r : TypeDRootIndex 4) (n : ℕ)
    (a b : LatticeIndex)
    (hab : rootDividedPower (b := typeDRootPairing_base 2) r n a b ≠ 0) :
    corootWeight i a = n * (typeDRootPairing 2).pairingIn ℤ
      r (typeDSimpleRootIndex 2 i) + corootWeight i b := by
  have h := rootDividedPower_isChevalleyHomogeneous
    (b := typeDRootPairing_base 2) r n a b hab (typeDSimpleRootIndex 2 i)
  have hw (k : LatticeIndex) : corootWeight i k =
      chevalleyBasisWeight (P := typeDRootPairing 2) k (typeDSimpleRootIndex 2 i) := by
    cases k <;> rfl
  simp only [← hw] at h
  omega

private lemma diagonal_term (P : Parameters) (i : Fin 4) (t : (ExtensionField P)ˣ)
    (r : TypeDRootIndex 4) (n : ℕ) (s : ExtensionField P) :
    corootDiagonal P i t *
      (s ^ n • specializeMatrix (rootDividedPower (b := typeDRootPairing_base 2)
        r n)) =
      ((t.val ^ ((typeDRootPairing 2).pairingIn ℤ
        r (typeDSimpleRootIndex 2 i)) * s) ^ n •
        specializeMatrix (rootDividedPower (b := typeDRootPairing_base 2)
          r n)) * corootDiagonal P i t := by
  ext a b
  simp only [corootDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.smul_apply, smul_eq_mul, specializeMatrix, Matrix.map_apply]
  by_cases h : rootDividedPower (b := typeDRootPairing_base 2)
      r n a b = 0
  · simp [h]
  · rw [weight_support i r n a b h, zpow_add₀ t.ne_zero,
      mul_comm (n : ℤ), zpow_mul, zpow_natCast, mul_pow]
    ring

private lemma diagonal_curve (P : Parameters) (i : Fin 4) (t : (ExtensionField P)ˣ)
    (r : TypeDRootIndex 4) (s : ExtensionField P) :
    corootDiagonal P i t * (rootCurve P r s).val.val =
      (rootCurve P r (t.val ^ ((typeDRootPairing 2).pairingIn ℤ
        r (typeDSimpleRootIndex 2 i)) * s)).val.val *
          corootDiagonal P i t := by
  change corootDiagonal P i t * (1 + s • _ + s ^ 2 • _ + s ^ 3 • _) =
    (1 + _ • _ + _ ^ 2 • _ + _ ^ 3 • _) * corootDiagonal P i t
  simp only [mul_add, add_mul, mul_one, one_mul]
  dsimp only [integralChevalleyRootOperators]
  rw [diagonal_term P i t r 2, diagonal_term P i t r 3]
  have h1 := diagonal_term P i t r 1 s
  simp only [pow_one] at h1
  rw [h1]

/-- Every canonical root curve has the specified coroot weight. -/
theorem coroot_conjugate (P : Parameters)
    (hdiag : ∀ i t, (Parabolics.torusWord P i t).val.val = corootDiagonal P i t)
    (i : Fin 4) (t : (ExtensionField P)ˣ) (r : TypeDRootIndex 4) (s : ExtensionField P) :
    Parabolics.torusWord P i t * rootCurve P r s *
      (Parabolics.torusWord P i t)⁻¹ =
        rootCurve P r (t.val ^ ((typeDRootPairing 2).pairingIn ℤ
          r (typeDSimpleRootIndex 2 i)) * s) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  apply Units.ext
  change (Parabolics.torusWord P i t).val.val * _ = _ * (Parabolics.torusWord P i t).val.val
  rw [hdiag]
  exact diagonal_curve P i t r s



/-- Root character on the faithful four-coroot coordinates. -/
def coordinateCharacter (P : Parameters) (r : TypeDRootIndex 4) :
    TorusCoordinates.Coordinates P →* (ExtensionField P)ˣ where
  toFun a := a 0 ^ ((typeDRootPairing 2).pairingIn ℤ r (typeDSimpleRootIndex 2 0)) *
    a 2 ^ ((typeDRootPairing 2).pairingIn ℤ r (typeDSimpleRootIndex 2 2)) *
    a 3 ^ ((typeDRootPairing 2).pairingIn ℤ r (typeDSimpleRootIndex 2 3)) *
    a 1 ^ ((typeDRootPairing 2).pairingIn ℤ r (typeDSimpleRootIndex 2 1))
  map_one' := by simp
  map_mul' a b := by
    simp only [Pi.mul_apply, mul_zpow]
    ac_rfl

/-- The character of the actual generated matrix torus. -/
def rootCharacter (P : Parameters) (hp : P.prime = 2) (r : TypeDRootIndex 4) :
    splitTorus P →* (ExtensionField P)ˣ :=
  (coordinateCharacter P r).comp (splitTorusMulEquiv P hp).symm.toMonoidHom

theorem rootCharacter_simple (P : Parameters) (hp : P.prime = 2)
    (r : TypeDRootIndex 4) (i : Fin 4) (t : (ExtensionField P)ˣ) :
    rootCharacter P hp r ⟨torusWord P i t, Subgroup.subset_closure ⟨i, t, rfl⟩⟩ =
      t ^ ((typeDRootPairing 2).pairingIn ℤ r (typeDSimpleRootIndex 2 i)) := by
  have he : (⟨torusWord P i t, Subgroup.subset_closure ⟨i, t, rfl⟩⟩ : splitTorus P) =
      splitTorusMulEquiv P hp (Function.update 1 i t) :=
    Subtype.ext (product_single P hp i t).symm
  calc
    _ = coordinateCharacter P r ((splitTorusMulEquiv P hp).symm
        (splitTorusMulEquiv P hp (Function.update 1 i t))) :=
      congrArg (rootCharacter P hp r) he
    _ = coordinateCharacter P r (Function.update 1 i t) :=
      congrArg (coordinateCharacter P r) ((splitTorusMulEquiv P hp).symm_apply_apply _)
    _ = _ := by fin_cases i <;> simp [coordinateCharacter]

private lemma conjugate_product {G K : Type*} [Group G] [CommMonoid K]
    (x : K → G) (g h : G) (a b : K)
    (hg : ∀ t, g * x t * g⁻¹ = x (a * t))
    (hh : ∀ t, h * x t * h⁻¹ = x (b * t)) (t : K) :
    (g * h) * x t * (g * h)⁻¹ = x ((a * b) * t) := by
  calc
    _ = g * (h * x t * h⁻¹) * g⁻¹ := by group
    _ = _ := by rw [hh, hg, mul_assoc]

theorem product_conjugate (P : Parameters) (hp : P.prime = 2)
    (a : TorusCoordinates.Coordinates P) (r : TypeDRootIndex 4) (t : ExtensionField P) :
    product P a * rootCurve P r t * (product P a)⁻¹ =
      rootCurve P r ((coordinateCharacter P r a : ExtensionField P) * t) := by
  simpa only [product, coordinateCharacter, MonoidHom.coe_mk, OneHom.coe_mk,
    Units.val_mul, Units.val_zpow_eq_zpow_val] using
    conjugate_product (rootCurve P r) _ _ _ _
    (conjugate_product (rootCurve P r) _ _ _ _
      (conjugate_product (rootCurve P r) _ _ _ _
        (coroot_conjugate P (torusWord_val P hp) 0 (a 0) r)
        (coroot_conjugate P (torusWord_val P hp) 2 (a 2) r))
      (coroot_conjugate P (torusWord_val P hp) 3 (a 3) r))
    (coroot_conjugate P (torusWord_val P hp) 1 (a 1) r) t

/-- Conjugation on positive and negative canonical curves, with no sign restriction. -/
theorem torus_conjugate (P : Parameters) (hp : P.prime = 2)
    (h : splitTorus P) (r : TypeDRootIndex 4) (t : ExtensionField P) :
    h.val * rootCurve P r t * h.val⁻¹ =
      rootCurve P r ((rootCharacter P hp r h : ExtensionField P) * t) := by
  let a := (splitTorusMulEquiv P hp).symm h
  have he : product P a = h.val :=
    congrArg Subtype.val ((splitTorusMulEquiv P hp).apply_symm_apply h)
  exact (congrArg (fun g : SplitGroup P => g * rootCurve P r t * g⁻¹) he).symm.trans
    (product_conjugate P hp a r t)

/-- All inputs of the split Bruhat theorem, proved for the literal matrices. -/
def inputs (P : Parameters) (hp : P.prime = 2) : SplitNormalForm.Inputs P where
  weylEquiv := splitWeylEquiv P hp
  simple := splitWeylEquiv_generator P hp
  conjugate_root w r t := by
    apply Subtype.ext
    exact (splitWeyl_rootCurveUnit_conjugation P hp
      ((splitWeylEquiv P hp).symm w) r t).trans (by
        rw [MulEquiv.apply_symm_apply]
        rfl)
  graphField_index := splitWeylEquiv_graphField_index P hp
  weyl_normalizes_torus := splitWeylSubgroup_le_normalizer_splitTorus P hp
  torus_normalizes_positive := splitTorus_le_normalizer_positiveSubgroup P hp
  positive_disjoint_torus := disjoint_positiveSubgroup_splitTorus P hp
  rootCharacter := rootCharacter P hp
  character_simple := rootCharacter_simple P hp
  torus_conjugate_root := torus_conjugate P hp

end Triality.Standard.ConcreteBruhat.InputRealization
