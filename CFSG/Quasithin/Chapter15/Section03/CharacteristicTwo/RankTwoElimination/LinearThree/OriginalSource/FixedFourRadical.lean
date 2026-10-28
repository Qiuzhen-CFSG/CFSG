module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Geometry.SourceAssembly
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.SourceCases.FixedFour
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.OrthogonalImage.FixedVectors
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Source
public import Theory.GroupTheory.FourGroupTwoGroupFixedLine

/-!
# The original radical fixes a normalized four-group

In the first-choice rank-two configuration, the original residual has no
fixed vector on V. A nontrivial R-action on a normalized four-group H in S
would give an R-fixed line. Both S and the residual normalize this line,
so fix it pointwise. Source 15.3.8 places the line in V, a contradiction.

For the intrinsic fixed factor C_[O₂(L),L](L), component normalization
supplies all the required invariance. This proves the action of the
original R, not the potentially larger O₂(LS), and does not identify the
Sylow subgroups of LR and LS.

Source: Aschbacher--Smith 15.3.8, 15.3.12 and the residual paragraph in
15.3.23, printed pp.1123--1129.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open CoreActions Extension.SourceCases
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
variable {G : Type*} [Group G] [Finite G]

/-- The original R centralizes every residual-and-S-invariant four-group
contained in S, once the original residual image is the full odd residual. -/
theorem radical_centralizes_normalized_four (d : LocalData G)
    (hfirst : d.Yplus = d.Y)
    (himage : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (H : Subgroup G) [IsElementaryAbelian 2 H] (hcard : Nat.card H = 4)
    (hHS : H ≤ d.S) (hH : d.Yplus ⊔ d.S ≤ normalizer (H : Set G)) :
    d.R ≤ centralizer (H : Set G) := by
  let : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour H := ⟨hcard, IsElementaryAbelian.exponent_eq_prime⟩
  by_contra hmove
  have hRnorm : d.Yplus ⊔ d.S ≤ normalizer (d.R : Set G) :=
    (d.Yplus ⊔ d.S).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (d.Yplus ⊔ d.S)
        (pCore 2 (d.Yplus ⊔ d.S : Subgroup G)))
  have hRH : d.R ≤ normalizer (H : Set G) :=
    ((d.Yplus ⊔ d.S).pCoreIn_le 2).trans hH
  let A := H ⊓ centralizer (d.R : Set G)
  have hA : Nat.card A = 2 := four_twoGroup_fixed_card_two H d.R
    ((d.Yplus ⊔ d.S).isPGroup_pCoreIn 2) hRH hmove
  have hfix : d.Yplus ⊔ d.S ≤ centralizer (A : Set G) :=
    (le_inf hH hRnorm).trans (four_twoGroup_common_normalizer_fixes H d.R
      ((d.Yplus ⊔ d.S).isPGroup_pCoreIn 2) hRH hmove)
  have hAS : A ≤ centralizer (d.S : Set G) :=
    le_centralizer_iff.mp (le_sup_right.trans hfix)
  have hAY : A ≤ centralizer (d.Yplus : Set G) :=
    le_centralizer_iff.mp (le_sup_left.trans hfix)
  have hAO : A ≤ centralOmegaIn d.S := by
    change A ≤ Stellmacher.omegaOneCenterAmbient d.S
    intro a ha
    exact (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hHS ha.1, elemPow_eq_one_of_isElementaryAbelian a ha.1, hAS ha⟩
  have hAV : A ≤ d.V := by
    rw [← (source_lemma_15_3_8 d.T d.action d.sylow_le 1).1] at hAO
    exact hAO.trans inf_le_left
  have hzero : fixedPlane d.V d.Yplus = ⊥ := by
    rw [hfirst]
    exact d.action.fixedPlane_eq_bot_of_residual_image
      (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) himage
  have hb : A = ⊥ := le_bot_iff.mp (hzero ▸ le_inf hAV hAY)
  rw [hb, card_bot] at hA
  omega

/-- The actual component fixed factor is normalized by both source actors;
the original radical therefore fixes it. The elementary-four structure is
the precise remaining large-distance module input. -/
theorem radical_centralizes_coreFixed (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    [IsElementaryAbelian 2 (coreFixed L)] (hcard : Nat.card (coreFixed L) = 4) :
    d.R ≤ centralizer (coreFixed L : Set G) := by
  apply radical_centralizes_normalized_four d hg.first_choice h.image
    (coreFixed L) hcard
  · exact inf_le_left.trans (commutatorCore_le_S d L h.core_le h.radical)
  · exact (sup_le h.normalizes_component hg.component_normalized).trans
      (Extension.SourceCases.FixedFour.coreFixed_normalized L)

/-- The actual fixed factor is central in the original LR once its
elementary-four structure is known. This supplies the original-ambient
centrality clause without transporting centrality from a replacement. -/
theorem coreFixed_central_in_radical_join (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    [IsElementaryAbelian 2 (coreFixed L)] (hcard : Nat.card (coreFixed L) = 4) :
    (coreFixed L).subgroupOf (L ⊔ d.R) ≤ center (L ⊔ d.R : Subgroup G) := by
  have hcentral : coreFixed L ≤ centralizer ((L ⊔ d.R : Subgroup G) : Set G) := by
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp inf_le_right)
      (radical_centralizes_coreFixed d L e h hg hcard)
  intro x hx
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (hcentral hx y y.property)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
