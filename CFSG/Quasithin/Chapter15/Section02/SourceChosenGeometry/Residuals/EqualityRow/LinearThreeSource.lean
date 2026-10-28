module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.ParabolicReduction
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.LinearThreeDegree
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.LinearThreeComplement
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.LinearThreeSeed
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.Centralizer

/-!
# Direct residual-input exclusion for the natural L₃ rows

The selected component, its marked parabolic and the original Omega action are
all retained literally.  The binary model supplies the complementary cubic
factor, while the actual `ResidualInput` supplies the three-prime centralizer
and the canonical seed then gives the contradiction.  No partner residual
identity or `PlaneUniquenessPreceding` packet is used.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 PlaneUniquenessPreceding ComponentCatalogue
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}

include hsource
private theorem selected_linearThree_escapes
    (r : ResidualInput hsource H B)
    (he : partnerSpan H Mc = residual H)
    {F : Type} [Field F] [Finite F]
    (selection : Normalized H M I X)
    (h : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X)
    (estar : starImage X ((M ⊓ I).pCoreIn 2) X ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (hF : Nat.card F = 2) : ¬ X ≤ Mc := by
  let XI := X.subgroupOf I
  let exi : XI ≃* X := subgroupOfEquivOfLe selection.component.1
  let eq : (XI ⧸ pCore 2 XI) ≃* (X ⧸ pCore 2 X) :=
    QuotientGroup.congr _ _ exi (pCore_map_iso 2 exi)
  let := Fintype.ofFinite F
  let ef : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let ePSL := eq.trans (linearThreeCoreEquiv h estar)
    |>.trans (Atlas.fieldEquivSL 3 ef)
    |>.trans Matrix.PSL3Two.equiv
  intro hXM
  apply r.linear_three_component_not_le_partner_of_eq he
    (X := X.subgroupOf I) selection.component.2 ePSL
  simpa only [XI, map_subgroupOf_eq_of_le selection.component.1] using hXM

include hsource
/-- The direct residual-input natural/doubled-natural L₃ endpoint. -/
theorem ResidualInput.normalized_component_linearThree_false_of_core_model
    (r : ResidualInput hsource H B)
    (he : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hfit : generalizedFitting I = pCore 2 I)
    (selection : Normalized H M I X)
    {n : ℕ} {F : Type} [Field F] [Finite F]
    (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hp : IsLinearMaximalParabolic
      ((starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
        (starImage X ((M ⊓ I).pCoreIn 2) X)) 3 F)
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I) : False := by
  let hcore := r.intersection_core_eq_of_not_le_partner hI hNI
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  have hdeg : n = 1 :=
    r.linearThree_degree_eq_one_of_star_parabolic hI
      h n F hn hF hp
  subst n
  let estar := hp.choose
  have hout : ¬ X ≤ Mc := by
    apply selected_linearThree_escapes r he selection h estar
    exact by simpa using hF
  let b : PlaneUniquenessPreceding.LinearThree.ModelOnly.Branch M I X 1 F :=
    ⟨h, by decide, hF, hp, ⟨linearThreeCoreEquiv h estar⟩⟩
  let := hsource.prepared.elementary
  have ho := r.omega_of_escape_not_le_partner hI hNI
  obtain ⟨hi⟩ := r.exists_planeInverter
  obtain ⟨eNI⟩ := r.intersection_image_equiv_of_omega hI hNI ho hi
  obtain ⟨f,hf,hker⟩ := OmegaAction.exists_symmetricThree_action_of_image_equiv eNI
  have hnorm : I ≤ normalizer (X : Set G) :=
    b.binary_normal_of_action_of_residual r hI hout f hker
  have hC := r.centralizer_threePrime_of_eq he
  obtain ⟨eAction⟩ := ho.2.2.2.1
  obtain ⟨E,hEK,hpE,hcard,hSE,hKE,hgen,hcomm⟩ :=
    b.binary_complementary_factor_of_residual r hI hout
      hnorm
  have hE : E ∈ normalCubicResiduals (smallActionK H) :=
    ⟨hEK,(normal_subgroupOf_iff_le_normalizer hEK).mpr hKE,hpE,hcard⟩
  exact r.canonical_seed_exclusion_any_factor hI hfit eAction hC
    (b.binary_source_residual_quotient_of_residual r hI hout f hker hC)
    hE hSE (b.binary_commutator_of_action_of_residual r hI hout f hker hC
      hSE hpE hcomm)

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
