module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesChief
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesChiefNatural

/-!
# The natural chief contribution in the original cubic obstruction

An actual natural L-subgroup in the original Sylow contributes at least
three noncentral cubic factors together with the quotient Sylow. The
previous chief-count identity converts this to rank(A*)>1 for the same
opposite subgroup and the same faithful projection. With middle-layer
fixedness, the literal D.2.13 application then centralizes the Fitting
subgroup of the original three-prime kernel image.

The existence of that natural subgroup and middle-layer fixedness remain
source obligations. These results do not prove the abelian-span assertion.
Source: Aschbacher--Smith 5.1.22--23, printed pp.645--646,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C N : Subgroup G} {n : ℕ} {z : G}

/-- The natural subgroup supplies the strict rank bound on the already
constructed opposite image, without choosing a new constituent. -/
theorem linear_cubic_nonabelian_rank_gt_one_of_natural_subgroup
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G))))
    (hn : 1 < n) (hnat : IsNaturalModule L N n) (hNT : N ≤ (T : Subgroup G))
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
    1 < rank (((conjugate (S.W g) g).subgroupOf S.H).map
      (SpanAction.projection (linear_cubic_centralizer_setup h d))) := by
  have hlower := natural_cubic_sylow_length_ge_three hnat hNT
    D.sylow_normalizes_component hn c.cubic_card
    (c.cubic_le.trans (c.left_le.trans inf_le_left))
    (c.cubic_le.trans (c.left_le.trans inf_le_right))
  rw [linear_cubic_nonabelian_sylow_length D h hpsl c d hne g hg hgn] at hlower
  dsimp only at hlower ⊢
  omega

/-- Discharge the chief-count premise of the literal D.2.13 consumer.
Only natural recognition and middle-layer fixedness remain explicit here. -/
theorem linear_cubic_fitting_of_natural_subgroup
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G))))
    (hn : 1 < n) (hnat : IsNaturalModule L N n) (hNT : N ≤ (T : Subgroup G))
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G))
    (hfix : let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
      ⁅conjugate (S.W g) g,S.S₂ g⁆ ≤ zpowers z) :
    let s := linear_cubic_centralizer_setup h d
    let i := inclusion (point_centralizer_le_residual_normalizer
      h.simpleQTKE hH.1.1 hK hnf d.point_mem d.point_ne)
    let C₁ := ((linearResidualAction H).comp i).ker
    let N₁ := C₁.map (SpanAction.projection s)
    ∃ E : Subgroup (SpanAction.Actor s),
      E ≤ ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))).map
        (SpanAction.projection s) ∧
      E ∈ ChapterD.QhatStar (SpanAction.representation s) ∧
      (fittingSubgroup N₁).map N₁.subtype ≤ centralizer (E : Set (SpanAction.Actor s)) := by
  exact linear_cubic_fitting_of_opposite_geometry D h hH hK hnf hlinear hpsl c d hne
    g hg hgn hfix
    (linear_cubic_nonabelian_rank_gt_one_of_natural_subgroup D h hpsl c d hne
      hn hnat hNT g hg hgn)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
