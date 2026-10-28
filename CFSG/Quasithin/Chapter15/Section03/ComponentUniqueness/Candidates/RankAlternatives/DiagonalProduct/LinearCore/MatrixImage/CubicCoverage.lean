module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.MatrixImage.LocalSetup
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.MatrixImage.CubicCoverage.LocalRank
public import Theory.SpecificGroups.PSL3.StandardCubicFixedNine

/-!
# Cubic coverage from the local three-rank bound

The local rank calculation excludes a fixed inner elementary abelian
nine-group for any outer cubic actor. The concrete semilinear descent theorem
constructs such a subgroup for every non-inner-diagonal standard cubic actor.
Together these give coverage of all cubic actors of Y₊ by the actual GL₃
conjugation image.

Simplicity and nonsolvability of the model are inherited from the actual
component, and both linear alternatives give an even field exponent. The
descent theorem handles mixed field-diagonal actors without assuming that
their extensions split. The original field and quotient coordinates are
preserved, including the central two-cover case. Standard automorphism
coverage remains an explicit premise for the parent image assembly to supply.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), A.3.16--18,
printed pp.50--53, and the final paragraph of 15.3.37, printed p.1135.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.MatrixImage.CubicCoverage

variable {G : Type*} [Group G] [Finite G]

/-- The local source inputs exclude all non-diagonal cubic actors once the
concrete standard cubic fixed-subgroup calculation is supplied. The field,
quotient equivalence, and actor are unchanged. -/
theorem cubic_coverage_of_fixed_nine {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (h : SourceSetup d I L)
    (hn : d.Yplus ≤ normalizer (L : Set G))
    {F : Type*} [Field F] (e : (L ⧸ pCore 2 L) ≃* PSL(3,F))
    (hstandard : Matrix.PSL3.OuterSolvable.standard F = ⊤)
    (hfixed : ∀ a : MulAut PSL(3,F),
      a ∈ Matrix.PSL3.OuterSolvable.standard F → orderOf a = 3 →
      a ∉ Matrix.PSL3.OuterSolvable.innerDiagonal F →
      ∃ E : Subgroup (MulAut PSL(3,F)), IsElementaryAbelian 3 E ∧
        E ≤ MulAut.innerSubgroup PSL(3,F) ∧ Nat.card E = 9 ∧
        E ≤ centralizer ({a} : Set (MulAut PSL(3,F)))) :
    ∀ x : d.Yplus, orderOf x = 3 →
      quotientAction hn e x ∈ Matrix.PSL3.OuterSolvable.innerDiagonal F := by
  intro x hx
  by_contra ho
  have ha : orderOf (quotientAction hn e x) = 3 := by
    apply orderOf_eq_prime
    · have hx3 : x ^ 3 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
      rw [← map_pow, hx3, map_one]
    · exact fun he => ho (he.symm ▸ (Matrix.PSL3.OuterSolvable.innerDiagonal F).one_mem)
  obtain ⟨E, hE, hinner, hcard, hfix⟩ :=
    hfixed _ (hstandard ▸ mem_top _) ha ho
  let := hE
  exact quotientAction_no_fixed_nine h hn e x hx
    (fun hi => ho (Matrix.PSL3.OuterSolvable.inner_le_innerDiagonal F hi))
    E hinner hcard hfix

/-- Every cubic actor is inner-diagonal in the supplied coordinates. The
fixed-nine calculation is discharged using the actual component's model
properties; only standard automorphism coverage remains explicit. The
distinguished actor's order is not needed for this coverage conclusion. -/
theorem cubic_coverage {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (h : SourceSetup d I L)
    (hn : d.Yplus ≤ normalizer (L : Set G)) {y : d.Yplus}
    {F : Type*} [Field F] [Finite F] (hcase : LinearCase L (Nat.card F))
    (w : DiagonalCoordinates L (y : G) F)
    (hstandard : Matrix.PSL3.OuterSolvable.standard F = ⊤) :
    ∀ x : d.Yplus, orderOf x = 3 →
      quotientAction hn w.e x ∈ Matrix.PSL3.OuterSolvable.innerDiagonal F := by
  obtain ⟨n, _, heven, hcard⟩ := hcase.even_card
  obtain ⟨hsimple, _, hns⟩ := h.model_properties w.e
  let := hsimple
  exact cubic_coverage_of_fixed_nine h hn w.e hstandard
    (Matrix.PSL3.StandardCubicFixedNine.exists_fixed_inner_nine hns hcard heven)

/-- Application to the original image calculation: cubic coverage is now
proved from the source inputs and standard coverage, in exactly the supplied
coordinates. Borel placement and cubic Borel generation are the separate
remaining inputs of the parent image assembly. -/
theorem image_le_of_source_borel_of_standard {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (h : SourceSetup d I L)
    (hn : d.Yplus ≤ normalizer (L : Set G))
    (y : d.Yplus) (hy : orderOf y = 3)
    {F : Type*} [Field F] [Finite F] (hcase : LinearCase L (Nat.card F))
    (w : DiagonalCoordinates L (y : G) F)
    (b : BorelPlacement d.Yplus d.S d.M L hn w.e)
    (hstandard : Matrix.PSL3.OuterSolvable.standard F = ⊤)
    (hmodel : CubicBorelGeneration F) :
    (quotientAction hn w.e).range ≤
      ((componentPart d.Yplus L).subgroupOf d.Yplus).map (quotientAction hn w.e) ⊔
        zpowers (quotientAction hn w.e y) :=
  image_le_of_source_borel h hn y hy w b
    (cubic_coverage h hn hcase w hstandard) hmodel

end CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.MatrixImage.CubicCoverage
