module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointFittingEscape
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryClosure
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedFixedModule
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels

/-!
# The original source alternatives at an escaping triple-six point

The original C.2.8 producer and the proved exclusion of the contained
Fitting case select an actual escaping component. In the ordinary branch
it is the literal H-closure of Lt, with t in its two-group center. In the
constrained branch its unchanged star action has the full proved catalogue,
and the whole original U lies in its core-fixed moved module.

This records the actual source input to the remaining C.3/C.4 analysis in
12.7.5, printed p.840. The constrained module restriction and the ordinary
PSL3(4) identification are not asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The genuine source selects an ordinary literal closure or a constrained
component with its full star model and original module placement. -/
theorem original_tripleSix_point_source_alternative_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬ centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    let H := centralizer ({(t : G)} : Set G)
    let Mt := normalizer (K : Set G) ⊓ H
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let Q := (K ⊔ (T : Subgroup G)).pCoreIn 2
    let B := conjugateSpanBy Lt H
    (IsComponent H (B.subgroupOf H) ∧ (t : G) ∈ centerIn B ∧
      centerIn B = B.pCoreIn 2) ∨
    ∃ J : Subgroup H, J.IsCComponent ∧ IsQuasisimple (J ⧸ pCore 2 J) ∧
      ¬ J ≤ Mt.subgroupOf H ∧ generalizedFitting J = pCore 2 J ∧
      Lt ≤ normalizer (J.map H.subtype : Set G) ∧
      Q ≤ normalizer (J.map H.subtype : Set G) ∧
      ChapterC.C27Source.StarModels.Model (starImage (J.map H.subtype) Q (J.map H.subtype)) ∧
      U ≤ (starV (J.map H.subtype) Q).map (J.map H.subtype ⊔ Q).subtype ∧
      U ≤ ⁅(starV (J.map H.subtype) Q).map (J.map H.subtype ⊔ Q).subtype ⊓
        centralizer (Lt.pCoreIn 2 : Set G),Lt⁆ := by
  let H := centralizer ({(t : G)} : Set G)
  let Mt := normalizer (K : Set G) ⊓ H
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let Q := (K ⊔ (T : Subgroup G)).pCoreIn 2
  have hstrict : Mt < H := lt_of_le_not_ge inf_le_right (fun hm => hout (hm.trans inf_le_left))
  have h28 := original_tripleSix_pushingUp_at h structural D a t ht heven
  have hf := original_tripleSix_point_fitting_escape_at h structural D a t ht heven hstrict
  obtain ⟨J,hJ,hq,houtJ,hn,hcases⟩ := h28.ordinary_or_constrained_escape hf
  rcases hcases with hordinary | hconstrained
  · exact Or.inl (original_tripleSix_point_ordinary_closure_at h structural D a t ht heven
      J hordinary).2
  · right
    have hspan : conjugateSpanBy Lt Mt = Lt :=
      (tripleSixPointResidual_component D a t ht heven).2.2.2
    refine ⟨J,hJ,hq,houtJ,hconstrained,?_,
      h28.constrained_radical_normalizes J hJ hq houtJ hconstrained,
      ChapterC.C27Source.star_model_from_source
        (h28.constrained_source_input J hJ hq houtJ hconstrained),
      h28.constrained_module_le_starV J hJ hq houtJ hconstrained,?_⟩
    · exact (le_conjugateSpanBy Lt Mt).trans hn
    · have hm := (h28.constrained_module_fixed_moved J hJ hq houtJ hconstrained).1
      change U ≤ ⁅(starV (J.map H.subtype) Q).map (J.map H.subtype ⊔ Q).subtype ⊓
        centralizer ((conjugateSpanBy Lt Mt).pCoreIn 2 : Set G),conjugateSpanBy Lt Mt⁆ at hm
      rwa [hspan] at hm

end CFSG.Quasithin.Chapter12.Section07
