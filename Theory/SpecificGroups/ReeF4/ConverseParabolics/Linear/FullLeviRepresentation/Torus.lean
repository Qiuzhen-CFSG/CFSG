module
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.FixedProducts
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FixedTorus
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.TorusCharacters

/-!
# Coordinates on the full fixed Ree torus

The inverse diagonal matrix with simple-root characters
`b, c, theta(c), theta(b)` is an actual element of the Ree fixed group.
These elements form an injective homomorphism from two copies of the field
units and exhaust the fixed intersection of the full coroot torus.

For coverage, twist the conjugation formula at root parameter one. Root-curve
injectivity forces the exceptional compatibility equations; the inverse F₄
Cartan matrix then recovers the torus from its four simple-root characters.
The parameter-injectivity argument also occurs in
`SubfieldOvergroups/FieldGeometry/Torus.lean`; it is used here under the
narrow root-group imports, without importing subfield geometry.

Source: GLS3 §§2.4 and 2.6, especially Theorem 2.6.5(f),
`refs/KGroup/GLS3/chapter2.tex`. This retains the full torus in the linear
local calculation underlying Aschbacher–Smith F.1.12(I)(5), printed p.263.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction Subgroup
namespace ReeF4.ConverseParabolics.FullLeviRepresentation
open Parabolics LargeLocalSeeds
open LocalBlockInput.PairRigidity LocalBlockInput.PairRigidity.BlockParameters
open BlockParameters.FieldRecovery
variable {m : ℕ}

theorem simpleScales_injective :
    Function.Injective (fun u : TorusParameter m =>
      fun i : Fin 4 => rootScale u (typeF4SimpleRootIndex i)) := by
  let F : TorusParameter m → TorusParameter m := fun u q =>
    rootScale u (typeF4SimpleRootIndex (typeF4RootPairing_baseEquiv.symm q))
  have hsurj : Function.Surjective F := by
    intro c
    refine ⟨torusParametersOfSimpleScales (fun i => c (typeF4RootPairing_baseEquiv i)), ?_⟩
    funext q
    dsimp [F]
    rw [rootScale_torusParametersOfSimpleScales, Equiv.apply_symm_apply]
  intro u v huv
  apply (Finite.injective_iff_surjective.mpr hsurj)
  funext q
  exact congrFun huv (typeF4RootPairing_baseEquiv.symm q)

theorem torusMatrix_root_entry (u : TorusParameter m) (r : F4Chevalley.Root) :
    (torusMatrix u).val (.inr r) (.inr r) =
      ((rootScale u r)⁻¹ : (CoefficientField m)ˣ) := by
  change (Matrix.diagonal fun a =>
    (chevalleyBasisTorusUnit (P := typeF4RootPairing) u a : CoefficientField m)) _ _ = _
  simp [chevalleyBasisTorusUnit, chevalleyBasisWeight, rootScale,
    integralChevalleyRootScale]

theorem torusMatrix_injective : Function.Injective (torusMatrix (m := m)) := by
  intro u v huv
  apply simpleScales_injective
  funext i
  apply inv_injective
  apply Units.ext
  simpa only [torusMatrix_root_entry] using
    congrArg (fun z : MatrixUnits m => z.val
      (.inr (typeF4SimpleRootIndex i)) (.inr (typeF4SimpleRootIndex i))) huv

theorem blockTorus_simple (b c : (CoefficientField m)ˣ) (i : Fin 4) :
    rootScale (blockTorus b c) (typeF4SimpleRootIndex i) =
      ![b, c, Units.map (theta m) c, Units.map (theta m) b] i :=
  rootScale_torusParametersOfSimpleScales _ i

theorem rootScale_mul (u v : TorusParameter m) (r : F4Chevalley.Root) :
    rootScale (u * v) r = rootScale u r * rootScale v r := by
  simp only [rootScale, integralChevalleyRootScale, Pi.mul_apply, mul_zpow,
    Finset.prod_mul_distrib]

private theorem blockTorus_one : blockTorus (1 : (CoefficientField m)ˣ) 1 = 1 := by
  apply simpleScales_injective
  funext i
  dsimp only
  rw [blockTorus_simple]
  fin_cases i <;> simp [rootScale, integralChevalleyRootScale]

private theorem blockTorus_mul (b c d e : (CoefficientField m)ˣ) :
    blockTorus (b * d) (c * e) = blockTorus b c * blockTorus d e := by
  apply simpleScales_injective
  funext i
  dsimp only
  rw [rootScale_mul, blockTorus_simple, blockTorus_simple, blockTorus_simple]
  fin_cases i <;> simp

/-- The actual fixed torus element whose two long simple-root characters are b and c.
Its matrix is the inverse diagonal matrix, matching the conjugation convention. -/
def torusElement (b c : (CoefficientField m)ˣ) : Model m :=
  let d := canonicalLocalBlockInput m
  let u := blockTorus b c
  let h : SplitGroup m := ⟨torusMatrix u, torusMatrix_mem_splitGroup u⟩
  d.modelEquiv ⟨h⁻¹, by
    change d.twist h⁻¹ = h⁻¹
    rw [map_inv, twist_torusMatrix d u (blockTorus_twistCompatible b c) h rfl]⟩

theorem torusElement_matrix (b c : (CoefficientField m)ˣ) :
    (toSplitGroup m (torusElement b c)).val = (torusMatrix (blockTorus b c))⁻¹ := by
  simp only [toSplitGroup_apply, torusElement, LocalBlockInput.modelEquiv_coe,
    Subgroup.coe_inv]

theorem torusElement_mem (b c : (CoefficientField m)ˣ) :
    torusElement b c ∈ fixedTorus m := by
  change toSplitGroup m (torusElement b c) ∈ splitTorus m
  rw [splitTorus_eq_diagonalTorus]
  refine ⟨(blockTorus b c)⁻¹, ?_⟩
  change diagonalTorusHom m (blockTorus b c)⁻¹ = (toSplitGroup m (torusElement b c)).val
  rw [map_inv, torusElement_matrix]
  rfl

/-- Multiplication of the two root characters gives multiplication in the actual torus. -/
def torusHom (m : ℕ) : (CoefficientField m)ˣ × (CoefficientField m)ˣ →* Model m where
  toFun bc := torusElement bc.1 bc.2
  map_one' := by
    apply toSplitGroup_injective m
    rw [map_one]
    apply Subtype.ext
    change (toSplitGroup m (torusElement 1 1)).val = (1 : MatrixUnits m)
    rw [torusElement_matrix, blockTorus_one]
    change (diagonalTorusHom m 1)⁻¹ = (1 : MatrixUnits m)
    rw [map_one, inv_one]
  map_mul' x y := by
    apply toSplitGroup_injective m
    rw [map_mul]
    apply Subtype.ext
    change (toSplitGroup m (torusElement (x.1 * y.1) (x.2 * y.2))).val =
      (toSplitGroup m (torusElement x.1 x.2)).val *
        (toSplitGroup m (torusElement y.1 y.2)).val
    rw [torusElement_matrix, torusElement_matrix, torusElement_matrix, blockTorus_mul]
    change (diagonalTorusHom m (_ * _))⁻¹ =
      (diagonalTorusHom m _)⁻¹ * (diagonalTorusHom m _)⁻¹
    rw [← map_inv, ← map_inv, ← map_inv, ← map_mul]
    congr 1
    exact mul_inv _ _

theorem torusHom_injective (m : ℕ) : Function.Injective (torusHom m) := by
  intro x y h
  have he := congrArg (fun z : Model m => (toSplitGroup m z).val) h
  change (toSplitGroup m (torusElement x.1 x.2)).val =
    (toSplitGroup m (torusElement y.1 y.2)).val at he
  rw [torusElement_matrix, torusElement_matrix] at he
  have hp := torusMatrix_injective (inv_injective he)
  apply Prod.ext
  · simpa only [blockTorus_simple, Matrix.cons_val_zero] using
      congrArg (fun u => rootScale u (typeF4SimpleRootIndex 0)) hp
  · simpa only [blockTorus_simple, Matrix.cons_val_one, Matrix.cons_val_zero] using
      congrArg (fun u => rootScale u (typeF4SimpleRootIndex 1)) hp


private theorem rootGenerator_injective (r : F4Chevalley.Root) :
    Function.Injective (rootGeneratorInGroup m r) := by
  intro s t h
  apply rootElement_injective (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) (k := CoefficientField m) r
  simp only [rootElement, rootMorphismFamily, rootMorphism_apply]
  congr 1
  change Matrix.GeneralLinearGroup.toLin (F4Chevalley.rootCurve r s) =
    Matrix.GeneralLinearGroup.toLin (F4Chevalley.rootCurve r t)
  exact congrArg Matrix.GeneralLinearGroup.toLin (congrArg Subtype.val h)

private theorem torus_conjugation (u : TorusParameters m)
    (h : SplitGroup m) (hh : h.val = torusMatrix u)
    (r : F4Chevalley.Root) (t : CoefficientField m) :
    h⁻¹ * rootGeneratorInGroup m r t * h =
      rootGeneratorInGroup m r ((rootScale u r : CoefficientField m) * t) := by
  apply Subtype.ext
  change h.val⁻¹ * F4Chevalley.rootCurve r t * h.val = _
  rw [hh]
  exact torusMatrix_conjugation u r t

/-- A fixed diagonal matrix has the exceptional-twist compatible characters. -/
theorem twistCompatible_of_fixed (u : TorusParameters m) (h : SplitGroup m)
    (hh : h.val = torusMatrix u) (hfix : (canonicalLocalBlockInput m).twist h = h) :
    TwistCompatible u := by
  intro r
  let d := canonicalLocalBlockInput m
  change d.twist h = h at hfix
  have he := congrArg d.twist (torus_conjugation u h hh r 1)
  simp only [map_mul, map_inv, d.twist_root, ← rootFieldEnd_apply, map_one, hfix] at he
  rw [torus_conjugation u h hh, mul_one, mul_one] at he
  rw [← rootFieldEnd_apply]
  exact (rootGenerator_injective _ he).symm

/-- The two long simple-root characters determine every twist-compatible diagonal parameter. -/
theorem compatible_eq_blockTorus (u : TorusParameters m) (hu : TwistCompatible u) :
    u = blockTorus (rootScale u (typeF4SimpleRootIndex 0))
      (rootScale u (typeF4SimpleRootIndex 1)) := by
  have h0 : rootScale u (typeF4SimpleRootIndex 3) =
      Units.map (theta m) (rootScale u (typeF4SimpleRootIndex 0)) := by
    apply Units.ext
    have hr : IsLongRoot (typeF4SimpleRootIndex 0) :=
      (typeF4SimpleRootIndex_mem_pair_iff 0).mpr (by decide)
    have he := hu (typeF4SimpleRootIndex 0)
    rw [exceptionalRootPermutation_simple,
      show Fin.revPerm (0 : Fin 4) = 3 by decide, exceptionalParameter_of_long hr] at he
    simpa only [Units.coe_map, MonoidHom.coe_coe, theta_apply] using he.symm
  have h1 : rootScale u (typeF4SimpleRootIndex 2) =
      Units.map (theta m) (rootScale u (typeF4SimpleRootIndex 1)) := by
    apply Units.ext
    have hr : IsLongRoot (typeF4SimpleRootIndex 1) :=
      (typeF4SimpleRootIndex_mem_pair_iff 1).mpr (by decide)
    have he := hu (typeF4SimpleRootIndex 1)
    rw [exceptionalRootPermutation_simple,
      show Fin.revPerm (1 : Fin 4) = 2 by decide, exceptionalParameter_of_long hr] at he
    simpa only [Units.coe_map, MonoidHom.coe_coe, theta_apply] using he.symm
  apply simpleScales_injective
  funext i
  dsimp only
  rw [blockTorus_simple]
  fin_cases i
  · rfl
  · rfl
  · exact h1
  · exact h0

/-- The two-parameter construction covers the actual fixed intersection of the full split torus. -/
theorem exists_torusElement (x : Model m) (hx : x ∈ fixedTorus m) :
    ∃ b c, torusElement b c = x := by
  have hxinv := (fixedTorus m).inv_mem hx
  change toSplitGroup m x⁻¹ ∈ splitTorus m at hxinv
  rw [splitTorus_eq_diagonalTorus] at hxinv
  obtain ⟨u, hu⟩ := hxinv
  change torusMatrix u = (toSplitGroup m x⁻¹).val at hu
  have hfix : (canonicalLocalBlockInput m).twist (toSplitGroup m x⁻¹) =
      toSplitGroup m x⁻¹ := by
    rw [LocalBlockInput.twist_eq_reeAutomorphism, reeAutomorphism_apply]
    exact reeTwist_toSplitGroup m x⁻¹
  have he := compatible_eq_blockTorus u (twistCompatible_of_fixed u _ hu.symm hfix)
  refine ⟨rootScale u (typeF4SimpleRootIndex 0), rootScale u (typeF4SimpleRootIndex 1), ?_⟩
  apply toSplitGroup_injective m
  apply Subtype.ext
  rw [torusElement_matrix, ← he, hu]
  simp only [map_inv, Subgroup.coe_inv, inv_inv]

theorem torusHom_range (m : ℕ) : (torusHom m).range = fixedTorus m := by
  apply le_antisymm
  · rintro x ⟨bc, rfl⟩
    exact torusElement_mem bc.1 bc.2
  · intro x hx
    obtain ⟨b, c, rfl⟩ := exists_torusElement x hx
    exact ⟨(b, c), rfl⟩

end ReeF4.ConverseParabolics.FullLeviRepresentation
