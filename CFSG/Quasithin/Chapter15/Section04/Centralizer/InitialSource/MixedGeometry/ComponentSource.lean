module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.ModelLifting.FullSourceModels
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.MixedGeometry.ComponentContradiction

/-!
# The mixed fitting conclusion from genuine source classifications

Apply full corrected F.6.18 to the literal I/O_{3'}(I) and its preserved
Goldschmidt triple. Original unequal local cores exclude row one. Every other
source row gives an intrinsic model of the actual simple component image;
the checked central-kernel lift and full ABC recover the original component.
Its source action and the post-A4 factor commutation then give the rank
contradiction. Thus F*(I)=O2(I) follows for the original mixed configuration.

Only full universal ABC and corrected F-source classification remain earlier
inputs. No component model, local action, factor commutation or old restricted
F618Universal is assumed. The characteristic-two FF branch of 15.4.18 remains
a separate step.

Source: Aschbacher--Smith, proof of 15.4.18, pp.1162--1163.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.ModelLifting.FullSource
open MixedLocal AlternatingLocals.RawQuotient FFBranch.ClassificationComparison
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G]

/-- All full source rows identify the actual simple star component. -/
theorem mixed_star_intrinsicModel {κ : GroupClass.{u}}
    (source : FSource.SourceClassificationInput κ)
    (T : Sylow 2 G) {Y X M₂ : Subgroup G} {F : Bool → Subgroup G}
    (c : Configuration κ T Y X M₂ F)
    (hodd : pPrimeCore 2 (generated T Y F) = ⊥)
    (L : Subgroup (generated T Y F)) (hL : IsComponent (generated T Y F) L) :
    IntrinsicComponentModel (starImage L) := by
  let I := generated T Y F
  let A := (firstGroup T Y F).subgroupOf I
  let B := (secondGroup T F).subgroupOf I
  have hk : IsPGroup 2 I.subtype.ker := by
    rw [ker_subtype]
    exact IsPGroup.of_bot
  have hne : A.pCoreIn 2 ≠ B.pCoreIn 2 := by
    intro he
    apply c.different_cores
    have h := congrArg (map I.subtype) he
    rw [map_pCoreIn_of_ker_isPGroup I.subtype hk,
      map_pCoreIn_of_ker_isPGroup I.subtype hk,
      map_subgroupOf_eq_of_le (show firstGroup T Y F ≤ I from le_sup_left),
      map_subgroupOf_eq_of_le (show secondGroup T F ≤ I from le_sup_right)] at h
    exact h
  obtain ⟨_,hsol,hpres⟩ := apply_F611_of_different_cores f611Universal_of_elementary A B c.goldschmidt hne
  have hnone : ¬ (pCore 2 (threePrimeImage A) = ⊥ ∧ pCore 2 (threePrimeImage B) = ⊥) := by
    intro hs
    exact hne (original_local_cores_eq_of_trivial_images A B c.goldschmidt hpres hs.1 hs.2)
  have hquot : ThreePrimeSQTKQuotient κ (I ⧸ pPrimeCore 3 I) :=
    { Cover := I, sqtk := c.sqtk, equiv := MulEquiv.refl _ }
  obtain ⟨S,_,hs⟩ := source (I ⧸ pPrimeCore 3 I) (threePrimeImage A) (threePrimeImage B)
    hpres.triple hquot
  obtain ⟨hcomp,hsimple⟩ := star_isComponent_and_simple L hL hodd hsol
  let := hsimple
  rcases hs with hs | hs
  · exact (component_model_of_source_alternative hcomp hs).resolve_left hnone
  · exact (component_model_of_source_alternative hcomp hs).resolve_left (fun hs => hnone hs.symm)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.ModelLifting.FullSource

namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
open FamilySource FamilySource.ModuleStructure LocalSetup LocalSetup.SourceWitnesses
open LocalSetup.TwoFactors LocalSetup.TwoFactors.MixedLocal LocalSetup.TwoFactors.ComponentBranch
open LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.RawQuotient
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original source pair and full earlier classifications force the fitting conclusion. -/
theorem source_mixed_generalizedFitting {κ : GroupClass.{u}}
    (hABC : ∀ (A : Type u) [Group A] [Finite A], ChapterA.Section02.TheoremsABC κ A)
    (sourceF : FSource.SourceClassificationInput κ)
    {T : Sylow 2 G} {M₁ M₂ Y X : Subgroup G}
    (hY : Input κ T M₁ Y 1) (hX : Input κ T M₂ X 2) (p : Pair T M₂ X)
    (d : RealizedFactors T Y X M₁ M₂ p.quotient.factor)
    (c : Configuration κ T Y X M₂ p.quotient.factor)
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4) :
    generalizedFitting (generated T Y p.quotient.factor) =
      pCore 2 (generated T Y p.quotient.factor) := by
  obtain ⟨hodd,hc,hinputs⟩ := source_mixed_component_inputs hABC hY c
  by_contra hne
  obtain ⟨L,hL⟩ := exists_component_of_generalizedFitting_ne hodd hne
  obtain ⟨⟨hn,hfaithful⟩,h115⟩ := hinputs L hL
  have hs := ModelLifting.FullSource.mixed_star_intrinsicModel sourceF T c hodd L hL
  have hm := ModelLifting.mixed_intrinsicModel_of_star_model T d c hZ hodd L hL hn hfaithful hc h115 hs
  exact source_component_model_contradiction hABC hY hX p d c hZ L hL hm

end CFSG.Quasithin.Chapter15.Section04.InitialSource
