module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.SourceGeometry
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.PointEdge
public import Theory.GroupTheory.Recognition.JankoFour.ModelHypotheses
/-!
# The original Mathieu application of the full point-side edge comparison

The published original LocalData constructor supplies the source point,
line, cubic and Todd markings, and its original-H perfectness and splitting
supply CubicNormalizerData. The independent local comparisons then carry
the full source edge fixer to the edge defined by φH(c.t), retaining the
literal original Sylow conjugator, cocode embedding, scalar and center.
Only the native earlier-source LocalData and CubicNormalizerData remain
explicit inputs. Agreement of these edge-preserving maps and the full
edge-reversal equation are not asserted by this intermediate result.

Keeping this constructor-dependent application in a leaf preserves the
existing comparison facade's import context.
Source: Aschbacher--Segev (1991), (8.3)--(8.4), pp.606--607, applied to the
original Aschbacher--Smith 8.2.12--14 inputs, pp.722--723.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
open Recognition.JankoFour
open SourceComparison SourceRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
/-- Construct the source local data and independent local edge maps on the
unchanged original Mathieu inputs. The target edge uses exactly φH(c.t). -/
theorem sourceOrbit_m24_local_edge_comparison
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
    (native : SourceIncidence.LocalData model_isTypeJ4)
    (nativeCubic : CubicNormalizerData native) :
    let hJ := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    ∃ (data : SourceIncidence.LocalData hJ)
      (q : centralizer ({(z : G)} : Set G)),
      (T : Subgroup G).map (MulAut.conj (q : G)).toMonoidHom=(data.T : Subgroup G) ∧
      data.P.E=D.sourceOrbit.map (MulAut.conj (q : G)).toMonoidHom ∧
      data.P.M=L.map (MulAut.conj (q : G)).toMonoidHom ∧
      (∀ w : D.sourceOrbit, data.P.vectorEmbedding (Multiplicative.ofAdd (E (Additive.ofMul w))) =
        MulAut.conj (q : G) w.val) ∧
      let c := D.sourceOrbit_m24_source_input h hmany hV hq hnon a E hE z hz hne hquot data
      ∃ (C : cubicCentralizerInH data.e data.X ≃* cubicCentralizerInH native.e native.X)
        (n : cubicNormalizerInH native.e native.X) (g : M24)
        (φM : data.P.M ≃* native.P.M)
        (φH : Recognition.JankoFour.centralizer (z : G) ≃* Recognition.JankoFour.centralizer Janko4.a),
        (∀ u, cubicNativeProjection model_isTypeJ4 native.e native.X (C u)=
          cubicNativeProjection hJ data.e data.X u) ∧
        φH planeMarker=planeMarker ∧
        (∀ u : cubicCentralizerInH data.e data.X,
          φH u.val=(cubicNormalizerAction native.e native.X n (C u)).val) ∧
        (core (z : G)).map φH.toMonoidHom=core Janko4.a ∧
        (cubicSylowImage data.e data.X).map φH.toMonoidHom=cubicSylowImage native.e native.X ∧
        (data.P.M.subgroupOf (Recognition.JankoFour.centralizer (z : G))).map φH.toMonoidHom=
          native.P.M.subgroupOf (Recognition.JankoFour.centralizer Janko4.a) ∧
        (data.L.G₂.subgroupOf (Recognition.JankoFour.centralizer (z : G))).map φH.toMonoidHom=
          native.L.G₂.subgroupOf (Recognition.JankoFour.centralizer Janko4.a) ∧
        (φM ⟨(z : G),marker_mem_point data⟩ : Janko4.Model)=Janko4.a ∧
        (∀ m, native.P.projection (φM m)=g*data.P.projection m*g⁻¹) ∧
        ((Recognition.JankoFour.centralizer (z : G)).subgroupOf data.P.M).map φM.toMonoidHom=
          (Recognition.JankoFour.centralizer Janko4.a).subgroupOf native.P.M ∧
        (data.L.G₂.subgroupOf data.P.M).map φM.toMonoidHom=native.L.G₂.subgroupOf native.P.M ∧
        (c.system.edgeGroup.subgroupOf data.P.M).map φM.toMonoidHom=
          (lineEdgeGroup native (φH ⟨c.t,c.t_plane⟩)).subgroupOf native.P.M := by
  obtain ⟨data,q,hT,hPE,hPM,hvec,_⟩ :=
    D.sourceOrbit_m24_localData h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨cubic⟩ := D.sourceOrbit_m24_cubicNormalizerData h hmany hV hq hnon a E hE
    z hz hne hquot data
  refine ⟨data,q,hT,hPE,hPM,hvec,?_⟩
  let c := D.sourceOrbit_m24_source_input h hmany hV hq hnon a E hE z hz hne hquot data
  have hedge : c.system.edgeGroup=lineEdgeGroup data c.t :=
    LocalGeometry.edgeGroup_eq (z : G) c.P.M c.t c.t_plane c.t_not_point c.t_sq
      c.faithful c.generate c.vertex_maximal c.plane_maximal c.edge_fixer
  change ∃ (C : cubicCentralizerInH data.e data.X ≃* cubicCentralizerInH native.e native.X)
    (n : cubicNormalizerInH native.e native.X) (g : M24)
    (φM : data.P.M ≃* native.P.M)
    (φH : Recognition.JankoFour.centralizer (z : G) ≃* Recognition.JankoFour.centralizer Janko4.a), _
  rw [hedge]
  exact exists_local_edge_equivs data native cubic nativeCubic ⟨c.t,c.t_plane⟩ c.t_line c.t_not_point

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
