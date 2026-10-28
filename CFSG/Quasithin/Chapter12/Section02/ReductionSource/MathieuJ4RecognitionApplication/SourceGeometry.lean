module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.LocalData
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4IncidenceApplication.Input
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.Defs

/-!
# The original Mathieu geometry and ambient cycle base

The original marked Mathieu inputs now construct all earlier LocalData.
The already proved full cubic-centralizer perfectness and involutory
normalizer splitting apply to its exact cubic quotient and Sylow, giving
both original-H clauses of AS91 (4.9). The completed incidence construction
then supplies every unchanged section 7 input and its ambient cycle base.
The point and line groups, original Sylow conjugator and cocode subgroup
are retained throughout; no local-data or geometric premise is added.

This completes these source-side inputs for the original marked Mathieu
branch. Compatible native local data and the section 8 comparison are still
needed for ambient recognition. In particular, this module does not assert
unconditional type-J4 recognition or the final quasithin classification.

Source: Aschbacher--Segev, The uniqueness of groups of type J4,
Invent. Math. 105 (1991), (4.9) and sections 5--7, pp.599--605,
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

/-- Both original-H clauses of AS91 (4.9), on the SAME constructed local data. -/
theorem sourceOrbit_m24_cubicNormalizerData
    (data : Recognition.JankoFour.SourceIncidence.LocalData
      (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot)) :
    Nonempty (Recognition.JankoFour.SourceComparison.CubicNormalizerData data) := by
  have hp := (D.sourceOrbit_m24_full_cubic_perfect h hmany hV hq hnon a E hE
    z hz hne hquot data.e data.X).2.1
  obtain ⟨v,hv,hout,_⟩ := D.sourceOrbit_m24_full_cubic_split h hmany hV hq hnon a E hE
    z hz hne hquot data.e data.X
  exact ⟨{
    perfect := hp
    s := v.val
    s_mem := v.property
    s_sq := by
      have hh : v ^ 2 = 1 := hv ▸ pow_orderOf_eq_one v
      exact congrArg Subtype.val (by simpa only [pow_two] using hh)
    s_not_mem := hout }⟩

/-- The original Mathieu inputs construct the local geometry, its ambient
cycle base and the original cubic normalizer input, without assumed local data. -/
theorem sourceOrbit_m24_source_geometry :
    let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    ∃ (data : Recognition.JankoFour.SourceIncidence.LocalData ht)
      (g : centralizer ({(z : G)} : Set G)),
      (T : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom = (data.T : Subgroup G) ∧
      data.P.E = D.sourceOrbit.map (MulAut.conj (g : G)).toMonoidHom ∧
      data.P.M = L.map (MulAut.conj (g : G)).toMonoidHom ∧
      Nonempty (Recognition.JankoFour.SourceComparison.CubicNormalizerData data) ∧
      centralizer ({(z : G)} : Set G) ⊔ data.P.M = ⊤ ∧
      (D.sourceOrbit_m24_source_input h hmany hV hq hnon a E hE z hz hne hquot data).system.IsBase := by
  obtain ⟨data,g,hT,hPE,hPM,_⟩ :=
    D.sourceOrbit_m24_localData h hmany hV hq hnon a E hE z hz hne hquot
  exact ⟨data,g,hT,hPE,hPM,
    D.sourceOrbit_m24_cubicNormalizerData h hmany hV hq hnon a E hE z hz hne hquot data,
    data.generate,
    D.sourceOrbit_m24_source_isBase h hmany hV hq hnon a E hE z hz hne hquot data⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
