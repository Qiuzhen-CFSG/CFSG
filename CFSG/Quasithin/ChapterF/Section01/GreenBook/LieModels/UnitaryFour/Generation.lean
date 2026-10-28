module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourGeneration

/-!
# Generation in the concrete projective unitary-four amalgam

The two parabolics in the existing GF(2^(2n)) model generate its actual
projective group. The matrix elimination theorem supplies the generation
clause of Aschbacher--Smith Definition F.1.6, printed p.261, for the U₄(q)
amalgam of F.1.12(I)(6), printed p.263. The existing overlap and injectivity
theorems retain the same three embeddings. Both flag stabilizers are proper
and their whole intersection is proper in each.

Maximality, Sylow and local-factor conclusions are separate assertions.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary

variable (n : ℕ) (hn : 1 ≤ n)

theorem matrix_parabolics_generate :
    pointParabolicMatrix n hn ⊔ planeParabolicMatrix n hn = ⊤ :=
  UnitaryFourGeneration.parabolics_sup_eq_top (MatrixField n)
    (fieldConj n) (fieldConj_involutive n hn)

/-- The generation requirement for the literal projective subgroup amalgam. -/
theorem parabolics_generate : pointParabolic n hn ⊔ planeParabolic n hn = ⊤ :=
  UnitaryFourGeneration.projective_parabolics_sup_eq_top (MatrixField n)
    (fieldConj n) (fieldConj_involutive n hn)

theorem parabolics_incomparable :
    ¬ pointParabolic n hn ≤ planeParabolic n hn ∧
      ¬ planeParabolic n hn ≤ pointParabolic n hn := by
  have h := UnitaryFourGeneration.parabolics_incomparable (MatrixField n)
    (fieldConj n) (fieldConj_involutive n hn)
  constructor
  · intro hle
    apply h.1
    exact (Subgroup.map_le_map_iff_of_injective (projection_injective n hn)).mp hle
  · intro hle
    apply h.2
    exact (Subgroup.map_le_map_iff_of_injective (projection_injective n hn)).mp hle

theorem pointParabolic_ne_top : pointParabolic n hn ≠ ⊤ := by
  intro h
  exact (parabolics_incomparable n hn).2 (h ▸ le_top)

theorem planeParabolic_ne_top : planeParabolic n hn ≠ ⊤ := by
  intro h
  exact (parabolics_incomparable n hn).1 (h ▸ le_top)

theorem overlap_lt_pointParabolic : overlap n hn < pointParabolic n hn := by
  exact (Subgroup.map_lt_map_iff_of_injective (projection_injective n hn)).mpr
    (UnitaryFourGeneration.borel_lt_point (MatrixField n)
      (fieldConj n) (fieldConj_involutive n hn))

theorem overlap_lt_planeParabolic : overlap n hn < planeParabolic n hn := by
  exact (Subgroup.map_lt_map_iff_of_injective (projection_injective n hn)).mpr
    (UnitaryFourGeneration.borel_lt_plane (MatrixField n)
      (fieldConj n) (fieldConj_involutive n hn))

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
