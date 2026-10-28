module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.SourceGeometry
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.Native.LocalData
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.LocalAgreement

/-!
# Original and native local-data comparison

The original Mathieu source geometry and the literal native cocode geometry
are constructed independently, then fed to the checked source-comparison
alignment.  The theorem retains the original Sylow, quotient, Todd markings,
cycle base and all local comparison equations.  It is an adapter only: the
remaining edge-reversal and ambient recognition arguments are proved by their
respective source modules.

Source: Aschbacher--Segev, *The uniqueness of groups of type J4*, Invent.
Math. 105 (1991), (4.8)--(4.9), (8.2)--(8.4), pp.598--599,606--607,
DOI 10.1007/BF01232280.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
open Recognition.JankoFour.SourceRecognition
open Recognition.JankoFour.LocalGeometry Recognition.JankoFour.LocalGeometry.LocalSubgroups
open Sporadic.Mathieu.M24LocalGeometry Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
attribute [local instance] ThreeSpaceData.R_normal_in_S_intrinsic
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
variable (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
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

include D h hmany hV hq hnon a E hE z hz hne hquot

/-- The original source inputs construct both local geometries and the
actual point/plane maps agreeing on their literal intersection. -/
theorem sourceOrbit_m24_native_local_comparison :
    let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    ∃ (data : Recognition.JankoFour.SourceIncidence.LocalData ht)
      (g : centralizer ({(z : G)} : Set G))
      (native : Recognition.JankoFour.SourceIncidence.LocalData Recognition.JankoFour.model_isTypeJ4),
      (T : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom = (data.T : Subgroup G) ∧
      data.P.E = D.sourceOrbit.map (MulAut.conj (g : G)).toMonoidHom ∧
      data.P.M = L.map (MulAut.conj (g : G)).toMonoidHom ∧
      centralizer ({(z : G)} : Set G) ⊔ data.P.M = ⊤ ∧
      (D.sourceOrbit_m24_source_input h hmany hV hq hnon a E hE z hz hne hquot data).system.IsBase ∧
      Recognition.JankoFour.centralizer Janko4.a ⊔ native.P.M = ⊤ ∧
      ∃ (C : Recognition.JankoFour.SourceComparison.cubicCentralizerInH data.e data.X ≃*
          Recognition.JankoFour.SourceComparison.cubicCentralizerInH native.e native.X)
        (n : Recognition.JankoFour.SourceComparison.cubicNormalizerInH native.e native.X)
        (b : M24) (φM : data.P.M ≃* native.P.M)
        (φH : Recognition.JankoFour.centralizer (z : G) ≃*
          Recognition.JankoFour.centralizer Janko4.a),
        (∀ c, Recognition.JankoFour.SourceComparison.cubicNativeProjection
          Recognition.JankoFour.model_isTypeJ4 native.e native.X (C c) =
          Recognition.JankoFour.SourceComparison.cubicNativeProjection ht data.e data.X c) ∧
        φH Recognition.JankoFour.SourceComparison.planeMarker =
          Recognition.JankoFour.SourceComparison.planeMarker ∧
        (∀ c : Recognition.JankoFour.SourceComparison.cubicCentralizerInH data.e data.X,
          φH c.val = (Recognition.JankoFour.SourceComparison.cubicNormalizerAction
            native.e native.X n (C c)).val) ∧
        (Recognition.JankoFour.core (z : G)).map φH.toMonoidHom =
          Recognition.JankoFour.core Janko4.a ∧
        (Recognition.JankoFour.SourceRecognition.cubicSylowImage data.e data.X).map
          φH.toMonoidHom =
          Recognition.JankoFour.SourceRecognition.cubicSylowImage native.e native.X ∧
        (∀ m, native.P.projection (φM m) = b * data.P.projection m * b⁻¹) ∧
        (∀ (k : G) (hkM : k ∈ data.P.M)
            (hkH : k ∈ Recognition.JankoFour.centralizer (z : G)),
          (φM ⟨k, hkM⟩ : Janko4.Model) = (φH ⟨k, hkH⟩ : Janko4.Model)) := by
  obtain ⟨data, g, hT, hE, hM, ⟨cubic⟩, hgen, hbase⟩ :=
    D.sourceOrbit_m24_source_geometry h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨native, hngen, ⟨nativeCubic⟩⟩ :=
    NativeCocode.exists_first_local_geometry
  exact ⟨data, g, native, hT, hE, hM, hgen, hbase, hngen,
    Recognition.JankoFour.SourceComparison.exists_compatible_local_equivs
      data native cubic nativeCubic⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
