module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.FullCatalogue
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.Sections
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M22.OuterActions
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Displacement.Involutions
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.TripleCover.Identification


/-!
# The two sporadic rows left by the small-ratio catalogue

The complete B.4.5 table leaves two genuine Mathieu possibilities at quadratic
ratio at most two: the ten-dimensional M₂₂ code module and the twelve-dimensional
genuine `3.M₂₂` module.  This file excludes both on the actual faithful action
image.  The code argument uses the marked pair-stabilizer extension, so an
involution outside the component is included.  The triple-cover argument uses
the center, quotient and dimension data to identify the component action and
then the checked matrix normalizer to include outer actors.

The final chief-section application keeps the selected `D`, `K`, quotient maps,
and marked element visible.  Its action-image and ambient intertwining inputs
are intentionally explicit: a row action and its dimension do not identify an
ambient representation by themselves.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), B.4.5 and
13.5.21, printed pp.86--87 and 923--924 (PDF pp.97--98 and 940--941).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open Sporadic.Mathieu
open CFSG.Quasithin.Chapter13.Section08.Source
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source

namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue

universe u v

variable {E : Type u} [Group E]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

theorem m22_code_row_contradiction
    (ρ : Representation (ZMod 2) E V) (L : Subgroup E) [L.Normal]
    (e : L ≃* M22)
    (hfaith : Function.Injective ρ)
    (ambient : Representation.Equiv ρ
      (simpleCodeAmbientRepresentation L e inferInstance))
    (t : E) (ht : t ^ 2 = 1)
    (hdisp : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) = 2) : False := by
  let q := simpleAmbientPairHom L e (inferInstance : L.Normal)
  have hqt : (q t) ^ 2 = 1 := by
    rw [← map_pow, ht, map_one]
  have hdisp_ne : t ≠ 1 := by
    intro ht1
    have hz := hdisp
    rw [ht1, map_one, sub_self, LinearMap.range_zero, finrank_bot] at hz
    omega
  have hqne : q t ≠ 1 := by
    intro hq
    apply hdisp_ne
    apply hfaith
    apply LinearMap.ext
    intro v
    have hh := LinearMap.congr_fun (ambient.isIntertwining' t) v
    change ambient (ρ t v) =
      MathieuCode.m22OuterCodeRepresentation (q t) (ambient v) at hh
    rw [hq] at hh
    simpa using hh
  have hqo : orderOf (q t) = 2 := orderOf_eq_prime hqt hqne
  have hmodel := MathieuCode.m22Outer_involution_displacement_ge_three (q t) hqo
  have htransport := Representation.RankTwo.finrank_movedSpace_transport ρ
    (simpleCodeAmbientRepresentation L e inferInstance)
    (MulEquiv.refl E) ambient.toLinearEquiv
    (fun g v => LinearMap.congr_fun (ambient.isIntertwining' g) v) t
  change Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) =
    Module.finrank (ZMod 2)
      (LinearMap.range ((simpleCodeAmbientRepresentation L e inferInstance) t - 1))
    at htransport
  have hmodel_eq := htransport.symm.trans hdisp
  change Module.finrank (ZMod 2)
      (LinearMap.range (MathieuCode.m22OuterCodeRepresentation (q t) - 1)) = 2
    at hmodel_eq
  have hmodel_ge : 3 ≤ Module.finrank (ZMod 2)
      (LinearMap.range (MathieuCode.m22OuterCodeRepresentation (q t) - 1)) := by
    calc
      3 ≤ fixedCodim MathieuCode.m22OuterCodeRepresentation (Subgroup.zpowers (q t)) := hmodel.1
      _ = Module.finrank (ZMod 2)
        (LinearMap.range (MathieuCode.m22OuterCodeRepresentation (q t) - 1)) :=
        fixedCodim_zpowers_eq_displacement_rank _ _
  have hcontra : (3 : Nat) ≤ 2 := hmodel_eq ▸ hmodel_ge
  omega

theorem triple_m22_row_contradiction
    (ρ : Representation (ZMod 2) E V) (L : Subgroup E) [L.Normal]
    [Finite L] [IsQuasisimple L]
    (e : L ≃* M22TripleCover)
    [Representation.IsIrreducible (ρ.comp L.subtype)]
    (hfaith : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 12)
    (t : E) (ht : t ^ 2 = 1)
    (hdisp : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) = 2) : False := by
  obtain ⟨ambient⟩ := Representation.RankTwo.TripleCover.component_equiv
    ρ L e hfaith hd
  have hn := Representation.RankTwo.TripleCover.no_rank_two_of_component_equiv
    ρ L e ambient t ht
  apply hn
  exact hdisp


end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
