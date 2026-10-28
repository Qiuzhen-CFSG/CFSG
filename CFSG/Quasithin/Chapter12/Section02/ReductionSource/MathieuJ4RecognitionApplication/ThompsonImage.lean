module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.ThompsonContainment
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.ThompsonImage

/-!
# The original Mathieu Thompson subgroup in the marked alternating quotient

The same common Sylow U and conjugator fixing z from the cocode containment
construction give A=J(U). Its original three-space, K-normalization and rank
eleven discharge the tensor intersection calculation: |A intersect R|=2^9
and the image in R/Z has order 2^6. The actual image under the original
S/R marking is a Sylow subgroup of its alternating group.

All existing quotient and cocode coordinates are retained in the SAME
witness package. This supplies the E_quotient clause used by
SourceIncidence.LocalData without adding a premise to the original Mathieu
inputs. A compatible split Todd group and the other geometry clauses still
require their source constructions.

Source: Aschbacher--Segev, *The uniqueness of groups of type J4*, Invent.
Math. 105 (1991), (4.7), printed p.598, DOI 10.1007/BF01232280;
original Aschbacher--Smith 8.2.12--14 marked Mathieu application.
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
open Recognition.JankoFour.SourceRecognition
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

include D h hmany hV hq hnon a E hE

include z hz hne hquot

/-- The same original witnesses have the literal A5 Sylow image required by the source geometry. -/
theorem sourceOrbit_m24_three_space_thompson_alternating_sylow :
    let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    ∃ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic))
      (d : ThreeSpaceData (z : G) cubic X)
      (U : Sylow 2 G) (g : centralizer ({(z : G)} : Set G))
      (P : Sylow 2 (alternatingGroup (Fin 5))),
      (U : Subgroup G) ≤ centralizer ({(z : G)} : Set G) ⊓ normalizer (d.space : Set G) ∧
      d.R ≤ (U : Subgroup G) ∧
      (T : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom = (U : Subgroup G) ∧
      D.sourceOrbit.map (MulAut.conj (g : G)).toMonoidHom = elementaryAbelianMaxJ (U : Subgroup G) ∧
      d.space ≤ elementaryAbelianMaxJ (U : Subgroup G) ∧
      elementaryAbelianMaxJ (U : Subgroup G) ≤ d.S ∧
      IsElementaryAbelian 2 (elementaryAbelianMaxJ (U : Subgroup G)) ∧
      Nat.card (elementaryAbelianMaxJ (U : Subgroup G)) = 2048 ∧
      centralizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G) =
        elementaryAbelianMaxJ (U : Subgroup G) ∧
      normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G) =
        L.map (MulAut.conj (g : G)).toMonoidHom ∧
      d.K ⊔ (U : Subgroup G) ≤ normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G) ∧
      Nat.card (elementaryAbelianMaxJ (U : Subgroup G) ⊓ d.R : Subgroup G) = 512 ∧
      Nat.card (d.radicalIntersectionImage (elementaryAbelianMaxJ (U : Subgroup G))) = 64 ∧
      ((elementaryAbelianMaxJ (U : Subgroup G)).subgroupOf d.S).map
        ((d.SQuotientEquiv ht).toMonoidHom.comp (QuotientGroup.mk' (d.R.subgroupOf d.S))) =
          (P : Subgroup (alternatingGroup (Fin 5))).map (alternatingGroup (Fin 5)).subtype ∧
      let W := D.sourceOrbit.map (MulAut.conj (g : G)).toMonoidHom
      letI : IsElementaryAbelian 2 W := IsElementaryAbelian.map (MulAut.conj (g : G)).toMonoidHom
      let a' := (automizerMapEquiv D.sourceOrbit (MulAut.conj (g : G))).symm.trans a
      let E' := (automizerModuleEquiv D.sourceOrbit (MulAut.conj (g : G))).symm.trans E
      (∀ b v, E' (automizerRepresentation W b v) = cocodeRepresentation (a' b) (E' v)) ∧
      ∃ e : (normalizer (W : Set G) ⧸ W.subgroupOf (normalizer (W : Set G))) ≃* M24,
        (∀ n : normalizer (W : Set G),
          e (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) n) =
            a' (W.normalizerMonoidHom.rangeRestrict n)) ∧
        ∃ P : Sylow 2 M24,
          ((U : Subgroup G).subgroupOf (normalizer (W : Set G))).map
            (e.toMonoidHom.comp (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))))) =
              (P : Subgroup M24) := by
  let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨cubic,X,d,U,g,hU,hR,hT,hJ,hZA,hAS,he,hc,hCJ,hN,hKA,htail⟩ :=
    sourceOrbit_m24_three_space_thompson_overlap D h hmany hV hq hnon a E hE z hz hne hquot
  let := he
  have hK : d.K ≤ normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G) :=
    le_sup_left.trans hKA
  obtain ⟨_,himage,hinter,_⟩ := d.elementary_eleven_symmetric_image ht
    (elementaryAbelianMaxJ (U : Subgroup G)) hc hZA hAS hK
  obtain ⟨P,hP⟩ := d.elementary_eleven_alternating_sylow ht
    (elementaryAbelianMaxJ (U : Subgroup G)) hc hZA hAS hK
  exact ⟨cubic,X,d,U,g,P,hU,hR,hT,hJ,hZA,hAS,he,hc,hCJ,hN,hKA,hinter,himage,hP,htail⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
