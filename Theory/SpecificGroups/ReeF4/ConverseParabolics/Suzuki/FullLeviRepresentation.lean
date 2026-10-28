module

public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki.FullLeviRepresentation.Splitting
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.ThreeSylowContainment.RootCapture.Generation
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.SuzukiCoordinates
public import BenderSuzuki.External.Huppert.XI.theorem_3_6

/-!
# A faithful Suzuki-times-torus representation of the full Ree Levi

The actual complementary torus centralizes both signed Suzuki root blocks,
hence the full fixed middle-node subsystem. The faithful four-dimensional
identification of that subsystem with the concrete Suzuki group, together
with its trivial center for `m ≥ 1`, separates it from the complement.
The proved fixed factorization and torus splitting show that their commuting
product is exactly `SuzukiLevi.fullLevi m`.

This constructs a direct-product isomorphism, and hence the faithful
homomorphism consumed by the full-parabolic radical retraction. The domain
retains the complete complementary torus. Neither fixed factorization nor
the actual Suzuki matrix comparison is assumed.

Source: GLS3, Theorem 2.6.5(f,g), `refs/KGroup/GLS3/chapter2.tex`, and the
Suzuki local factor of Aschbacher–Smith F.1.12(I)(5), printed p.263.
-/

@[expose] public noncomputable section

namespace ReeF4.ConverseParabolics.SuzukiFullLeviRepresentation
open Subgroup Parabolics LargeLocalSeeds FullLeviRepresentation BenderSuzuki.MatrixGroups
open LocalBlockInput.PairRigidity BlockParameters BlockParameters.FieldRecovery
open FixedCollection.SeedGeneration
open SuzukiLevi (fullLevi)
variable {m : ℕ}

private def matrixHom (m : ℕ) : Model m →* MatrixUnits m :=
  (SplitGroup m).subtype.comp (toSplitGroup m)

private theorem matrixHom_injective (m : ℕ) : Function.Injective (matrixHom m) :=
  Subtype.val_injective.comp (toSplitGroup_injective m)

private theorem matrixHom_torus (b c : (CoefficientField m)ˣ) :
    matrixHom m (torusElement b c) = (torusMatrix (blockTorus b c))⁻¹ :=
  torusElement_matrix b c

private theorem matrixHom_modelEquiv (d : LocalBlockInput m) (x : d.fixedGroup) :
    matrixHom m (d.modelEquiv x) = x.val.val := by
  change (toSplitGroup m (d.modelEquiv x)).val = _
  rw [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe]

/-- The complementary torus centralizes both full signed Suzuki blocks. -/
theorem complement_commutes_block (b : (CoefficientField m)ˣ) (p : Bool)
    (y : (canonicalLocalBlockInput m).fixedGroup)
    (hy : y ∈ simpleBlock (canonicalLocalBlockInput m) .suzuki p) :
    Commute ((canonicalLocalBlockInput m).modelEquiv y) (complementHom m b) := by
  let d := canonicalLocalBlockInput m
  obtain ⟨t, u, he⟩ := (suzukiCoordinates d).suzuki_cover p y hy
  have h : torusElement b 1 * d.modelEquiv y * (torusElement b 1)⁻¹ =
      d.modelEquiv y := by
    apply matrixHom_injective m
    simp only [map_mul, map_inv, matrixHom_torus, matrixHom_modelEquiv, ← he, inv_inv]
    have hs : signedScale (1 : (CoefficientField m)ˣ) p = 1 := by
      cases p <;> simp [signedScale]
    simpa only [matrixTorusConj_apply, centralScale, map_one, one_pow, one_mul, hs, Units.val_one] using
      blockTorus_suzukiWord b 1 p t u
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

/-- Generation by both signed fixed blocks extends centralization to the whole subsystem. -/
theorem seed_commutes_complement
    (x : fixedLevi (canonicalLocalBlockInput m) .suzuki) (b : (CoefficientField m)ˣ) :
    Commute (seedLeviHom m x) (complementHom m b) := by
  let d := canonicalLocalBlockInput m
  let C := (centralizer {complementHom m b}).comap d.modelEquiv.toMonoidHom
  have hblock (p : Bool) : simpleBlock d .suzuki p ≤ C := by
    intro y hy
    exact mem_centralizer_singleton_iff.mpr (complement_commutes_block b p y hy)
  have hx : x.val ∈ C :=
    (sup_le (hblock true) (hblock false))
      (Parabolics.ThreeSylowContainment.RootCapture.suzuki_fixedLevi_le_signed d x.property)
  exact mem_centralizer_singleton_iff.mp hx

private theorem suzuki_center_eq_bot (hm : 1 ≤ m) : center (SuzukiMatrixGroup m) = ⊥ := by
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  rcases (inferInstance : (center (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    apply BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm
    apply Group.isSolvable_of_comm
    intro x y
    have hx : x ∈ center (SuzukiMatrixGroup m) := by rw [h]; trivial
    exact (mem_center_iff.mp hx y).symm

private theorem factors_disjoint (hm : 1 ≤ m) :
    Disjoint (seedLeviHom m).range (complementHom m).range := by
  apply Subgroup.disjoint_def.mpr
  rintro g ⟨x, rfl⟩ ⟨c, hc⟩
  let e := SuzukiLeviProjection.fixedLeviEquivSuzuki (canonicalLocalBlockInput m)
  have hx : e x ∈ center (SuzukiMatrixGroup m) := by
    rw [mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := e.surjective z
    rw [← map_mul, ← map_mul]
    congr 1
    apply seedLeviHom_injective m
    simp only [map_mul]
    rw [← hc]
    exact (seed_commutes_complement y c).eq
  have hx1 : e x = 1 := by
    simpa only [suzuki_center_eq_bot hm, mem_bot] using hx
  have he : x = 1 := e.injective (hx1.trans e.map_one.symm)
  rw [he, map_one]

/-- Multiplication of the actual commuting subsystem and complement. -/
def productHom (m : ℕ) :
    fixedLevi (canonicalLocalBlockInput m) .suzuki × (CoefficientField m)ˣ →* Model m :=
  (seedLeviHom m).noncommCoprod (complementHom m) seed_commutes_complement

theorem productHom_injective (hm : 1 ≤ m) : Function.Injective (productHom m) :=
  (MonoidHom.noncommCoprod_injective _ _ _).mpr
    ⟨seedLeviHom_injective m, complementHom_injective m, factors_disjoint hm⟩

theorem productHom_range (m : ℕ) : (productHom m).range = fullLevi m := by
  rw [productHom, MonoidHom.noncommCoprod_range, fullLevi_eq_seed_sup_complement]

/-- The full fixed Levi is the actual product of its subsystem and the complementary field torus. -/
def fullLeviProductEquiv (hm : 1 ≤ m) :
    fullLevi m ≃* fixedLevi (canonicalLocalBlockInput m) .suzuki × (CoefficientField m)ˣ :=
  (MulEquiv.ofBijective ((productHom m).codRestrict (fullLevi m)
      (fun x => (productHom_range m) ▸ (show productHom m x ∈ (productHom m).range from ⟨x, rfl⟩))) (by
    constructor
    · intro x y h
      exact productHom_injective hm (congrArg Subtype.val h)
    · intro x
      have hx : x.val ∈ (productHom m).range := by
        rw [productHom_range]
        exact x.property
      obtain ⟨y, hy⟩ := hx
      exact ⟨y, Subtype.ext hy⟩)).symm

/-- The inverse equivalence multiplies the two actual subgroups in the Ree model. -/
@[simp] theorem fullLeviProductEquiv_symm_coe (hm : 1 ≤ m)
    (x : fixedLevi (canonicalLocalBlockInput m) .suzuki) (b : (CoefficientField m)ˣ) :
    ((fullLeviProductEquiv hm).symm (x, b)).val =
      seedLeviHom m x * complementHom m b := rfl

end ReeF4.ConverseParabolics.SuzukiFullLeviRepresentation

namespace ReeF4.ConverseParabolics
open SuzukiFullLeviRepresentation
open SuzukiLevi (fullLevi)

/-- The full Suzuki-side Ree Levi, retaining its complementary torus, is Suzuki matrices times the field units. -/
def suzukiFullLeviEquiv {m : ℕ} (hm : 1 ≤ m) :
    fullLevi m ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m × (CoefficientField m)ˣ :=
  (fullLeviProductEquiv hm).trans
    (MulEquiv.prodCongr (LargeLocalSeeds.SuzukiLeviProjection.fixedLeviEquivSuzuki
      (canonicalLocalBlockInput m)) (MulEquiv.refl _))

/-- A faithful representation of the actual full fixed Levi. -/
def suzukiFullLeviEmbedding {m : ℕ} (hm : 1 ≤ m) :
    fullLevi m →* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m × (CoefficientField m)ˣ :=
  (suzukiFullLeviEquiv hm).toMonoidHom

theorem suzukiFullLeviEmbedding_injective {m : ℕ} (hm : 1 ≤ m) :
    Function.Injective (suzukiFullLeviEmbedding hm) := (suzukiFullLeviEquiv hm).injective

theorem suzukiFullLeviEmbedding_surjective {m : ℕ} (hm : 1 ≤ m) :
    Function.Surjective (suzukiFullLeviEmbedding hm) := (suzukiFullLeviEquiv hm).surjective

/-- The representation needed by the full-parabolic radical retraction. -/
theorem exists_suzukiFullLeviEmbedding {m : ℕ} (hm : 1 ≤ m) :
    ∃ ρ : fullLevi m →*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m × (CoefficientField m)ˣ,
      Function.Injective ρ :=
  ⟨suzukiFullLeviEmbedding hm, suzukiFullLeviEmbedding_injective hm⟩

end ReeF4.ConverseParabolics
