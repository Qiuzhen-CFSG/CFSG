module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.SourceGeometry
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.Recognition
public import Theory.GroupTheory.Recognition.JankoFour.ModelHypotheses
/-!
# Source-base recognition for the original marked Mathieu branch

The original Mathieu hypotheses construct their literal LocalData, original-H
cubic perfectness and splitting, and the source cycle base. Section 8 now
constructs agreeing local isomorphisms and proves the entire edge-reversal
equation. The direct local-homomorphism extension is surjective by native
generation and injective by original source simplicity.

The explicit native premises remain earlier-source LocalData, its original
cubic-normalizer clauses and the actual embedded generation equality. No
native simplicity or cycle base is used. The original Sylow conjugator,
cocode embedding, point group, marker and both local restrictions are retained.
This conditional application does not discharge the native earlier-source
construction or use the final no-J4 exclusion.

Source: Aschbacher--Segev (1991), section 8, pp.605--607, applied to the
original Aschbacher--Smith 8.2.12--14 Mathieu inputs, pp.722--723.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
open Recognition.JankoFour SourceComparison SourceRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
variable
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
    (nativeCubic : CubicNormalizerData native)
    (nativeGenerate : Recognition.JankoFour.centralizer Janko4.a ⊔ native.P.M=⊤)
include D h hmany hV hq hnon a E hE z hz hne hquot native nativeCubic nativeGenerate

/-- The original branch is recognized with its original marking and both
local restriction equations. Only the specified native earlier data remain. -/
theorem sourceOrbit_m24_comparison_recognition_marked :
    let hJ := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    ∃ (data : SourceIncidence.LocalData hJ)
      (q : centralizer ({(z : G)} : Set G))
      (M : data.P.M ≃* native.P.M)
      (H : Recognition.JankoFour.centralizer (z : G) ≃* Recognition.JankoFour.centralizer Janko4.a)
      (F : G ≃* Janko4.Model),
      (T : Subgroup G).map (MulAut.conj (q : G)).toMonoidHom=(data.T : Subgroup G) ∧
      data.P.E=D.sourceOrbit.map (MulAut.conj (q : G)).toMonoidHom ∧
      data.P.M=L.map (MulAut.conj (q : G)).toMonoidHom ∧
      (∀ w : D.sourceOrbit, data.P.vectorEmbedding (Multiplicative.ofAdd (E (Additive.ofMul w))) =
        MulAut.conj (q : G) w.val) ∧
      (∀ m : data.P.M, F m=(M m : Janko4.Model)) ∧
      (∀ k : Recognition.JankoFour.centralizer (z : G), F k=(H k : Janko4.Model)) ∧
      F z=Janko4.a := by
  let : IsSimpleGroup G := h.simpleQTKE.simple
  obtain ⟨data,q,hT,hPE,hPM,hvec,_⟩ :=
    D.sourceOrbit_m24_localData h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨cubic⟩ := D.sourceOrbit_m24_cubicNormalizerData h hmany hV hq hnon a E hE
    z hz hne hquot data
  obtain ⟨_,_,_,M,H,F,_,_,_,_,_,_,_,_,_,hfM,hfH,hzF⟩ :=
    exists_recognition_equiv data native cubic nativeCubic nativeGenerate
  exact ⟨data,q,M,H,F,hT,hPE,hPM,hvec,hfM,hfH,hzF⟩

/-- Conditional original Mathieu recognition, without the no-J4 exclusion. -/
theorem sourceOrbit_m24_comparison_recognition : Nonempty (G ≃* Janko4.Model) := by
  obtain ⟨_,_,_,_,F,_⟩ := D.sourceOrbit_m24_comparison_recognition_marked
    h hmany hV hq hnon a E hE z hz hne hquot native nativeCubic nativeGenerate
  exact ⟨F⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
