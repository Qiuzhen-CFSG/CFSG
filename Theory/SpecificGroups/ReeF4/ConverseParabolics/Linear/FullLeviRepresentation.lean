module

public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear.FullLeviRepresentation.Splitting

/-!
# A faithful SL₂-times-torus representation of the full linear Ree Levi

The actual complementary torus constructed by diagonal matrices centralizes
both signed linear root groups, hence the full fixed end-node subsystem.
The subsystem is SL₂ over the same coefficient field. Its center is trivial
in characteristic two, so the subsystem and complement intersect trivially.
The proved fixed factorization and torus splitting show that their commuting
product is exactly `SectionGeometry.LinearRadical.fullLevi m`.

This constructs a direct-product isomorphism and, in particular, the faithful
homomorphism consumed by the full-parabolic radical retraction. The domain
is the fixed intersection of the subsystem joined with the complete coroot
torus; the complementary torus is retained throughout.

Source: GLS3, Theorem 2.6.5(f,g), `refs/KGroup/GLS3/chapter2.tex`, and the
linear local factor of Aschbacher–Smith F.1.12(I)(5), printed p.263.
-/

@[expose] public noncomputable section

namespace ReeF4.ConverseParabolics.FullLeviRepresentation
open Subgroup Parabolics LargeLocalSeeds
open LocalBlockInput.PairRigidity BlockParameters BlockParameters.FieldRecovery
open FixedCollection.SeedGeneration
open SectionGeometry.LinearRadical (fullLevi)
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

/-- The concrete torus conjugates both signed linear curves by its first character. -/
theorem torusElement_conj_linear (b c : (CoefficientField m)ˣ) (p : Bool)
    (t : CoefficientField m) :
    torusElement b c * (canonicalLocalBlockInput m).modelEquiv
        (linearElement (canonicalLocalBlockInput m) p t) * (torusElement b c)⁻¹ =
      (canonicalLocalBlockInput m).modelEquiv
        (linearElement (canonicalLocalBlockInput m) p ((signedScale b p : CoefficientField m) * t)) := by
  apply matrixHom_injective m
  simp only [map_mul, map_inv, matrixHom_torus, matrixHom_modelEquiv,
    linearElement_word, inv_inv]
  exact blockTorus_linearWord b c p t

/-- The complement centralizes the entire fixed subsystem, by its two signed generators. -/
theorem seed_commutes_complement (hm : 1 ≤ m)
    (x : fixedLevi (canonicalLocalBlockInput m) .linear) (c : (CoefficientField m)ˣ) :
    Commute (seedLeviHom m x) (complementHom m c) := by
  let d := canonicalLocalBlockInput m
  let C := (centralizer {complementHom m c}).comap d.modelEquiv.toMonoidHom
  have hblock (p : Bool) : simpleBlock d .linear p ≤ C := by
    intro y hy
    obtain ⟨t, rfl⟩ := linearElement_surjective d p hy
    apply mem_centralizer_singleton_iff.mpr
    have h := torusElement_conj_linear (m := m) 1 c p t
    have hs : (signedScale (1 : (CoefficientField m)ˣ) p : CoefficientField m) = 1 := by
      cases p <;> simp [signedScale]
    rw [hs, one_mul] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  have hx : x.val ∈ C :=
    (sup_le (hblock true) (hblock false))
      (fixedLevi_linear_le_signed_of_longRootMap d (linearLongRootMap m hm) x.property)
  exact mem_centralizer_singleton_iff.mp hx

private theorem factors_disjoint (hm : 1 ≤ m) :
    Disjoint (seedLeviHom m).range (complementHom m).range := by
  apply Subgroup.disjoint_def.mpr
  rintro g ⟨x, rfl⟩ ⟨c, hc⟩
  let e := LinearProjection.fixedLeviEquivSL hm (canonicalLocalBlockInput m)
  have hx : e x ∈ center (LinearSL m) := by
    rw [mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := e.surjective z
    rw [← map_mul, ← map_mul]
    congr 1
    apply seedLeviHom_injective m
    simp only [map_mul]
    rw [← hc]
    exact (seed_commutes_complement hm y c).eq
  have hx1 : e x = 1 := by
    simpa only [Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot, mem_bot] using hx
  have he : x = 1 := e.injective (hx1.trans e.map_one.symm)
  rw [he, map_one]

/-- Multiplication of the actual commuting subsystem and complement. -/
def productHom (hm : 1 ≤ m) :
    fixedLevi (canonicalLocalBlockInput m) .linear × (CoefficientField m)ˣ →* Model m :=
  (seedLeviHom m).noncommCoprod (complementHom m) (seed_commutes_complement hm)

theorem productHom_injective (hm : 1 ≤ m) : Function.Injective (productHom hm) :=
  (MonoidHom.noncommCoprod_injective _ _ _).mpr
    ⟨seedLeviHom_injective m, complementHom_injective m, factors_disjoint hm⟩

theorem productHom_range (hm : 1 ≤ m) : (productHom hm).range = fullLevi m := by
  rw [productHom, MonoidHom.noncommCoprod_range, fullLevi_eq_seed_sup_complement]

/-- The full fixed Levi is the actual product of its subsystem and the complementary field torus. -/
def fullLeviProductEquiv (hm : 1 ≤ m) :
    fullLevi m ≃* fixedLevi (canonicalLocalBlockInput m) .linear × (CoefficientField m)ˣ :=
  (MulEquiv.ofBijective ((productHom hm).codRestrict (fullLevi m)
      (fun x => (productHom_range hm) ▸ (show productHom hm x ∈ (productHom hm).range from ⟨x, rfl⟩))) (by
    constructor
    · intro x y h
      exact productHom_injective hm (congrArg Subtype.val h)
    · intro x
      have hx : x.val ∈ (productHom hm).range := by
        rw [productHom_range]
        exact x.property
      obtain ⟨y, hy⟩ := hx
      exact ⟨y, Subtype.ext hy⟩)).symm

end ReeF4.ConverseParabolics.FullLeviRepresentation

namespace ReeF4.ConverseParabolics
open FullLeviRepresentation
open SectionGeometry.LinearRadical (fullLevi)

/-- The full linear Ree Levi, retaining its complementary torus, is SL₂ times the field units. -/
def linearFullLeviEquiv {m : ℕ} (hm : 1 ≤ m) :
    fullLevi m ≃* Matrix.SpecialLinearGroup (Fin 2) (CoefficientField m) × (CoefficientField m)ˣ :=
  (fullLeviProductEquiv hm).trans
    (MulEquiv.prodCongr (LargeLocalSeeds.LinearProjection.fixedLeviEquivSL hm
      (canonicalLocalBlockInput m)) (MulEquiv.refl _))

/-- A faithful representation of the actual full fixed Levi. -/
def linearFullLeviEmbedding {m : ℕ} (hm : 1 ≤ m) :
    fullLevi m →* Matrix.SpecialLinearGroup (Fin 2) (CoefficientField m) × (CoefficientField m)ˣ :=
  (linearFullLeviEquiv hm).toMonoidHom

theorem linearFullLeviEmbedding_injective {m : ℕ} (hm : 1 ≤ m) :
    Function.Injective (linearFullLeviEmbedding hm) := (linearFullLeviEquiv hm).injective

/-- The representation needed by the full-parabolic radical retraction. -/
theorem exists_linearFullLeviEmbedding {m : ℕ} (hm : 1 ≤ m) :
    ∃ ρ : fullLevi m →*
      Matrix.SpecialLinearGroup (Fin 2) (CoefficientField m) × (CoefficientField m)ˣ,
      Function.Injective ρ :=
  ⟨linearFullLeviEmbedding hm, linearFullLeviEmbedding_injective hm⟩

end ReeF4.ConverseParabolics
