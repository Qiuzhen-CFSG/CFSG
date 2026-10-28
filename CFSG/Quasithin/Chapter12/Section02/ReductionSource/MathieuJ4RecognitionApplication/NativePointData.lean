module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.SourceGeometry
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.Native.PointData
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.PlaneGroup

/-!
# Constructed native point data and the original Mathieu plane comparison

The unchanged original Mathieu inputs construct their source geometry and
cycle base. The native cocode construction supplies PointData at the literal
matrix generator a, with the same selected cubic quotient and with ambient
generation. Native full cubic-centralizer perfectness and the involutory
normalizer splitting discharge both original-H inputs of the existing
AS91 plane comparison, for every selected native cubic Sylow.

The resulting isomorphism is between the actual involution centralizers.
It preserves the central marker, extraspecial core, scalar cubic subgroup,
full cubic normalizer and the six-cover restriction. No native LocalData,
splitting or perfectness premise is added to the original source arguments.
Compatible native LineData and the remaining section 8 overlap alignment
are still required for ambient recognition.

Source: Aschbacher--Segev, The uniqueness of groups of type J4, Invent.
Math. 105 (1991), (4.8)--(4.9), sections 5--7 and (8.3), pp.598--606,
DOI 10.1007/BF01232280; original Aschbacher--Smith 8.2.12--14.
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

/-- The original source geometry and a constructed native point group, with
its full plane comparison for every native cubic marking and Sylow choice.
No native LocalData or original-H premise is assumed. -/
theorem sourceOrbit_m24_native_point_plane :
    let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    ∃ (data : Recognition.JankoFour.SourceIncidence.LocalData ht)
      (g : centralizer ({(z : G)} : Set G)),
      (T : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom = (data.T : Subgroup G) ∧
      data.P.E = D.sourceOrbit.map (MulAut.conj (g : G)).toMonoidHom ∧
      data.P.M = L.map (MulAut.conj (g : G)).toMonoidHom ∧
      Nonempty (Recognition.JankoFour.SourceComparison.CubicNormalizerData data) ∧
      centralizer ({(z : G)} : Set G) ⊔ data.P.M = ⊤ ∧
      (D.sourceOrbit_m24_source_input h hmany hV hq hnon a E hE z hz hne hquot data).system.IsBase ∧
      ∀ cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (Recognition.JankoFour.centralizer Janko4.a ⧸ Recognition.JankoFour.core Janko4.a),
        ∃ native : PointData Janko4.a,
          native.cubic = cubic ∧ native.E = NativeCocode.firstKernel ∧
          native.M = normalizer (NativeCocode.firstKernel : Set Janko4.Model) ∧
          Recognition.JankoFour.centralizer Janko4.a ⊔ native.M = ⊤ ∧
          ∀ X : Sylow 3 (CubicLift.subgroup cubic),
            ∃ (φ : Recognition.JankoFour.SourceComparison.cubicCentralizerInH data.e data.X ≃*
                Recognition.JankoFour.SourceComparison.cubicCentralizerInH cubic X)
              (Φ : Recognition.JankoFour.centralizer (z : G) ≃*
                Recognition.JankoFour.centralizer Janko4.a),
              (∀ c, Recognition.JankoFour.SourceComparison.cubicNativeProjection Recognition.JankoFour.model_isTypeJ4
                cubic X (φ c) = Recognition.JankoFour.SourceComparison.cubicNativeProjection ht data.e data.X c) ∧
              Φ Recognition.JankoFour.SourceComparison.planeMarker = Recognition.JankoFour.SourceComparison.planeMarker ∧
              (∀ c : Recognition.JankoFour.SourceComparison.cubicCentralizerInH data.e data.X, Φ c.val = (φ c).val) ∧
              (Recognition.JankoFour.core (z : G)).map Φ.toMonoidHom =
                Recognition.JankoFour.core Janko4.a ∧
              (cubicSylowImage data.e data.X).map Φ.toMonoidHom = cubicSylowImage cubic X ∧
              (Recognition.JankoFour.SourceComparison.cubicNormalizerInH data.e data.X).map Φ.toMonoidHom =
                Recognition.JankoFour.SourceComparison.cubicNormalizerInH cubic X := by
  obtain ⟨data,g,hT,hPE,hPM,hC,hgen,hbase⟩ :=
    D.sourceOrbit_m24_source_geometry h hmany hV hq hnon a E hE z hz hne hquot
  refine ⟨data,g,hT,hPE,hPM,hC,hgen,hbase,?_⟩
  intro cubic
  obtain ⟨native,hc,hNE,hm,hgen⟩ := NativeCocode.first_pointData_generation cubic
  refine ⟨native,hc,hNE,hm,hgen,?_⟩
  intro X
  obtain ⟨c⟩ := hC
  obtain ⟨s,hs,hout,_⟩ := NativeCocode.first_fullCubic_split cubic X
  have hs2 : s * s = 1 := by
    simpa only [pow_two] using (hs ▸ pow_orderOf_eq_one s : s ^ 2 = 1)
  have hsval : s.val * s.val = 1 :=
    congrArg (fun t : fullCubicNormalizer cubic X => t.val) hs2
  exact Recognition.JankoFour.SourceComparison.exists_plane_equiv_marked
    (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot)
    data.e data.X Recognition.JankoFour.model_isTypeJ4 cubic X
    c.perfect (NativeCocode.first_fullCubic_perfect cubic X)
    ⟨c.s,c.s_mem⟩ (Subtype.ext c.s_sq) c.s_not_mem
    ⟨s.val,s.property⟩ (Subtype.ext hsval) hout

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
