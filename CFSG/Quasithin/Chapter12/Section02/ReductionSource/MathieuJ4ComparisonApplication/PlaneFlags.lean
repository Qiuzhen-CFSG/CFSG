module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.PlaneFlags
public import Theory.GroupTheory.Recognition.JankoFour.ModelHypotheses

/-!
# Original marked Mathieu application of the plane flag comparison

Retain the complete original Mathieu telescope and its IsTypeJ4 witness.
The earlier source and native Section 4 data construct a plane isomorphism
carrying both literal flag overlaps, with one design conjugator. Its
six-cover restriction records the correcting normalizer actor, preserving
both central attachments. For every actual plane element, hence the t
supplied by the unchanged source Input, both local edge stabilizers are
transported on ambient left cosets. This discharges the local plane-map
part of AS91 (8.3), pp.606–607, for the original Chapter12 branch.

Overlap automorphism control, agreement with the point map, and conjugation
on the full edge fixer remain with the Section 8 assembly.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode GraphUniquenessSystem
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
open Recognition.JankoFour SourceComparison SourceRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Both plane flags and the local edges for the unchanged Mathieu branch. -/
theorem sourceOrbit_m24_plane_flag_comparison
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))
    (data : SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot))
    (cubic : CubicNormalizerData data)
    (native : SourceIncidence.LocalData model_isTypeJ4)
    (nativeCubic : CubicNormalizerData native) :
    ∃ (g : m22DesignAut)
      (φ : cubicCentralizerInH data.e data.X ≃* cubicCentralizerInH native.e native.X)
      (n : cubicNormalizerInH native.e native.X) (Φ : Recognition.JankoFour.centralizer (z : G) ≃* Recognition.JankoFour.centralizer Janko4.a),
      g • data.P.hexad = native.P.hexad ∧ g • data.L.pair = native.L.pair ∧
      (∀ c, cubicNativeProjection model_isTypeJ4 native.e native.X (φ c) = cubicNativeProjection (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot) data.e data.X c) ∧
      Φ planeMarker = planeMarker ∧
      (∀ c : cubicCentralizerInH data.e data.X,
        Φ c.val = (cubicNormalizerAction native.e native.X n (φ c)).val) ∧
      (core (z : G)).map Φ.toMonoidHom = core Janko4.a ∧
      (cubicSylowImage data.e data.X).map Φ.toMonoidHom = cubicSylowImage native.e native.X ∧
      (cubicNormalizerInH data.e data.X).map Φ.toMonoidHom = cubicNormalizerInH native.e native.X ∧
      (∀ x, native.designProjection (Φ x) = g * data.designProjection x * g⁻¹) ∧
      (data.P.M.subgroupOf (Recognition.JankoFour.centralizer (z : G))).map Φ.toMonoidHom =
        native.P.M.subgroupOf (Recognition.JankoFour.centralizer Janko4.a) ∧
      (data.L.G₂.subgroupOf (Recognition.JankoFour.centralizer (z : G))).map Φ.toMonoidHom =
        native.L.G₂.subgroupOf (Recognition.JankoFour.centralizer Janko4.a) ∧
      ((data.P.M ⊓ data.L.G₂).subgroupOf (Recognition.JankoFour.centralizer (z : G))).map Φ.toMonoidHom =
        (native.P.M ⊓ native.L.G₂).subgroupOf (Recognition.JankoFour.centralizer Janko4.a) ∧
      (∀ t : Recognition.JankoFour.centralizer (z : G),
        ((edgeFixer G (Cosets.vertex data.P.M 1) (Cosets.vertex data.P.M (t : G))).subgroupOf
          (Recognition.JankoFour.centralizer (z : G))).map Φ.toMonoidHom =
          (edgeFixer Janko4.Model (Cosets.vertex native.P.M 1) (Cosets.vertex native.P.M (Φ t : Janko4.Model))).subgroupOf
            (Recognition.JankoFour.centralizer Janko4.a) ∧
        ((edgeStabilizer G (Cosets.vertex data.P.M 1) (Cosets.vertex data.P.M (t : G))).subgroupOf
          (Recognition.JankoFour.centralizer (z : G))).map Φ.toMonoidHom =
          (edgeStabilizer Janko4.Model (Cosets.vertex native.P.M 1) (Cosets.vertex native.P.M (Φ t : Janko4.Model))).subgroupOf
            (Recognition.JankoFour.centralizer Janko4.a)) := by
  exact exists_plane_flag_equiv data native cubic nativeCubic

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
