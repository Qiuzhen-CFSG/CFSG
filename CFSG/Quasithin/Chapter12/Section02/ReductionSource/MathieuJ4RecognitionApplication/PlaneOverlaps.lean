module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.MarkedOverlaps
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.PlaneOverlaps

/-!
# The compatible plane flag for the original Mathieu inputs

Keep the original common Sylow, conjugator fixing z, cocode coordinates,
trio and sextet from MarkedOverlaps. The new native recognition identifies
both literal images under the same cubic projection as pair and hexad
stabilizers. Their preimages are the original plane-line and point-plane
groups, including the entire cubic lift. The pair lies in that hexad.

Every hypothesis is discharged from the original marked Mathieu data and
hquot. This supplies the overlap clauses of PointData and LineData, without
assuming either record. The Todd splitting, general/native constructors,
original-H (4.9) and unconditional recognition remain separate obligations.

Source: Aschbacher--Segev, The uniqueness of groups of type J4,
Invent. Math. 105 (1991), (4.6)--(4.8) and section 5, pp.598--600,
DOI 10.1007/BF01232280; original Aschbacher--Smith 8.2.12--14.
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
open Recognition.JankoFour.SourceRecognition
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

include D h hmany hV hq hnon a E hE

include z hz hne hquot

/-- The original inputs give simultaneous trio-sextet and pair-hexad flags,
with every quotient marking and full cubic preimage retained. -/
theorem sourceOrbit_m24_three_space_plane_flag :
    ∃ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic))
      (d : ThreeSpaceData (z : G) cubic X)
      (U : Sylow 2 G) (g : centralizer ({(z : G)} : Set G))
      (trio : Trio) (sextet : Sextet) (pair hexad : Finset (Fin 22)),
      (U : Subgroup G) ≤ centralizer ({(z : G)} : Set G) ⊓ normalizer (d.space : Set G) ∧
      d.R ≤ (U : Subgroup G) ∧
      (T : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom = (U : Subgroup G) ∧
      D.sourceOrbit.map (MulAut.conj (g : G)).toMonoidHom = elementaryAbelianMaxJ (U : Subgroup G) ∧
      d.space ≤ elementaryAbelianMaxJ (U : Subgroup G) ∧
      elementaryAbelianMaxJ (U : Subgroup G) ≤ d.S ∧
      normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G) =
        L.map (MulAut.conj (g : G)).toMonoidHom ∧
      (∃ P : Sylow 2 (alternatingGroup (Fin 5)),
        d.symmetricImage (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot)
          (elementaryAbelianMaxJ (U : Subgroup G)) = AlternatingSylowNormalizer.image P) ∧
      Nat.card (normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G) ⊓
        centralizer ({(z : G)} : Set G) : Subgroup G) = 283115520 ∧
      Nat.card (centralizer ({(z : G)} : Set G) ⊓ d.pointLineGroup (U : Subgroup G) : Subgroup G) =
        18874368 ∧
      (normalizer (d.space : Set G)).relIndex
        (normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G) ⊓
          centralizer ({(z : G)} : Set G)) = 15 ∧
      (normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G)).relIndex
        (centralizer ({(z : G)} : Set G) ⊓ normalizer (d.space : Set G)) = 5 ∧
      Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic ≤
        (normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G)).subgroupOf
          (centralizer ({(z : G)} : Set G)) ∧
      Nat.card (((normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G)).subgroupOf
        (centralizer ({(z : G)} : Set G))).map
          (Recognition.JankoFour.LocalGeometry.CubicLift.projection cubic)) = 11520 ∧
      ((((normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G)).subgroupOf
        (centralizer ({(z : G)} : Set G))).map
          (Recognition.JankoFour.LocalGeometry.CubicLift.projection cubic)).comap
          (Recognition.JankoFour.LocalGeometry.CubicLift.projection cubic) =
        (normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G)).subgroupOf
          (centralizer ({(z : G)} : Set G))) ∧
      Recognition.JankoFour.SourceCycleBase.Native.Incident trio sextet ∧
      pair.card = 2 ∧ hexad ∈ m22Blocks ∧ pair ⊆ hexad ∧
      ((normalizer (d.space : Set G)).subgroupOf (centralizer ({(z : G)} : Set G))).map
        (Recognition.JankoFour.LocalGeometry.CubicLift.projection cubic) =
          Recognition.JankoFour.LocalGeometry.LocalSubgroups.designStabilizer pair ∧
      (normalizer (d.space : Set G)).subgroupOf (centralizer ({(z : G)} : Set G)) =
        (Recognition.JankoFour.LocalGeometry.LocalSubgroups.designStabilizer pair).comap
          (Recognition.JankoFour.LocalGeometry.CubicLift.projection cubic) ∧
      ((normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G)).subgroupOf
        (centralizer ({(z : G)} : Set G))).map
          (Recognition.JankoFour.LocalGeometry.CubicLift.projection cubic) =
            Recognition.JankoFour.LocalGeometry.LocalSubgroups.designStabilizer hexad ∧
      (normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G)).subgroupOf
        (centralizer ({(z : G)} : Set G)) =
          (Recognition.JankoFour.LocalGeometry.LocalSubgroups.designStabilizer hexad).comap
            (Recognition.JankoFour.LocalGeometry.CubicLift.projection cubic) ∧
      let W := D.sourceOrbit.map (MulAut.conj (g : G)).toMonoidHom
      letI : IsElementaryAbelian 2 W := IsElementaryAbelian.map (MulAut.conj (g : G)).toMonoidHom
      let a' := (automizerMapEquiv D.sourceOrbit (MulAut.conj (g : G))).symm.trans a
      let F := (automizerModuleEquiv D.sourceOrbit (MulAut.conj (g : G))).symm.trans E
      let f := a'.toMonoidHom.comp W.normalizerMonoidHom.rangeRestrict
      Function.Surjective f ∧ f.ker = W.subgroupOf (normalizer (W : Set G)) ∧
      (∀ n v, F (Additive.ofMul (W.normalizerMonoidHom n v)) =
        cocodeRepresentation (f n) (F (Additive.ofMul v))) ∧
      ((normalizer (d.space : Set G)).subgroupOf (normalizer (W : Set G))).map f =
        trioStabilizer trio ∧
      (trioStabilizer trio).comap f =
        (normalizer (d.space : Set G)).subgroupOf (normalizer (W : Set G)) ∧
      ((centralizer ({(z : G)} : Set G)).subgroupOf (normalizer (W : Set G))).map f =
        sextetStabilizer sextet ∧
      (sextetStabilizer sextet).comap f =
        (centralizer ({(z : G)} : Set G)).subgroupOf (normalizer (W : Set G)) ∧
      ∃ w : W, (w : G) = (z : G) ∧ F (Additive.ofMul w) = sextetVector sextet := by
  obtain ⟨cubic,X,d,U,g,trio,sextet,hU,hR,hT,hJ,hZA,hAS,hN,hP,hplane,htriple,
    hpi,hli,hcubic,hc,hpre,hflag,htail⟩ :=
    D.sourceOrbit_m24_three_space_marked_overlaps h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨pair,hexad,hpair,hhex,hsub,hpairImage,hpairPre,hhexImage,hhexPre⟩ :=
    d.plane_flag (D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot)
      (normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G)) hplane hpi
  exact ⟨cubic,X,d,U,g,trio,sextet,pair,hexad,hU,hR,hT,hJ,hZA,hAS,hN,hP,hplane,htriple,
    hpi,hli,hcubic,hc,hpre,hflag,hpair,hhex,hsub,hpairImage,hpairPre,hhexImage,hhexPre,htail⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
