module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.ThompsonImage
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.PointLine

/-!
# The literal point-line intersection for the original Mathieu inputs

The same original three-space, common Sylow U and conjugator fixing z
supply M=N_G(J(U)). Thompson weak closure lifts the normalizer of its
marked alternating four-group to the exact intersection N_G(Z) intersect M.
Its index in N_G(Z) is five; its whole two-core is J(U)R, of order 2^17,
and its quotient is L3(2) times S3. K lies normally in this intersection.

This constructs the point-line core, core-order, linear-containment,
relative-normality and quotient clauses of the later LineData interface.
It adds no hypothesis to the original Mathieu inputs. The split Todd
group, compatible plane overlaps, general/native LocalData and final
recognition still require their source constructions.

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

/-- The original marked Mathieu inputs construct the literal point-line intersection,
its whole two-core and its L3(2) times S3 quotient, with the same Sylow and conjugator. -/
theorem sourceOrbit_m24_three_space_point_line :
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
      normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G) =
        L.map (MulAut.conj (g : G)).toMonoidHom ∧
      d.symmetricImage ht (elementaryAbelianMaxJ (U : Subgroup G)) =
        AlternatingSylowNormalizer.image P ∧
      d.K ≤ d.pointLineGroup (U : Subgroup G) ∧
      (d.K.subgroupOf (d.pointLineGroup (U : Subgroup G))).Normal ∧
      (d.pointLineGroup (U : Subgroup G)).relIndex (normalizer (d.space : Set G)) = 5 ∧
      Nat.card (d.pointLineGroup (U : Subgroup G)) = 132120576 ∧
      (pCore 2 (d.pointLineGroup (U : Subgroup G))).map (d.pointLineGroup (U : Subgroup G)).subtype =
        elementaryAbelianMaxJ (U : Subgroup G) ⊔ d.R ∧
      Nat.card (pCore 2 (d.pointLineGroup (U : Subgroup G))) = 2^17 ∧
      Nonempty ((d.pointLineGroup (U : Subgroup G) ⧸ pCore 2 (d.pointLineGroup (U : Subgroup G))) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) × Equiv.Perm (Fin 3)) := by
  let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨cubic,X,d,U,g,P,hU,hR,hT,hJ,hZA,hAS,he,hc,_,hN,hKA,hi,_,hP,_⟩ :=
    sourceOrbit_m24_three_space_thompson_alternating_sylow D h hmany hV hq hnon
      a E hE z hz hne hquot
  have hK : d.K ≤ normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G) :=
    le_sup_left.trans hKA
  exact ⟨cubic,X,d,U,g,P,hU,hR,hT,hJ,hZA,hAS,he,hc,hN,hP,
    d.K_le_pointLineGroup _ hK,d.K_normal_in_pointLineGroup _,
    d.pointLineGroup_index ht _ hR hAS hK P hP,
    d.pointLineGroup_card ht _ hR hAS hK P hP,
    d.pointLineGroup_twoCore_ambient ht U hR hAS hK hc hi P hP,
    d.pointLineGroup_twoCore_card ht _ hR hAS hK P hP,
    d.pointLineGroup_core_quotient ht _ hR hAS hK P hP⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
