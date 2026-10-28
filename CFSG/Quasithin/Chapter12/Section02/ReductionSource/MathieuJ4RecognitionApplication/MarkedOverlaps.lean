module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.PointLine
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.MarkedOverlaps
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.OverlapIndices
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.FlagIncidence
import all CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF

/-!
# Compatible native overlap markings for the original Mathieu inputs

For the same three-space Z, common Sylow U, conjugator fixing z and
Thompson subgroup W=J(U), the original cocode quotient identifies the
point-line overlap with an actual trio stabilizer. The point-plane overlap
is the stabilizer of the original marker vector, hence maps onto an actual
sextet stabilizer in those same coordinates. Both preimage equalities are
proved, and the original S/R marking of the alternating Sylow is retained.

K acts transitively on the seven nonidentity points of Z inside the
point-line overlap. Counting its marker stabilizer gives the literal
triple-intersection order and the two flag indices fifteen and five.
The incidence owner's native index-fifteen theorem then makes the chosen
trio and sextet incident. The point-plane index 77 also forces the whole
original cubic lift into the overlap; the retained cubic projection has
image of order 11520 and recovers precisely that overlap by preimage.

All inputs are the original marked Mathieu arguments and hquot. This
constructs native overlap markings needed for LocalData, without assuming
a Todd complement or LocalData. Compatible splitting, identification of
the cubic image with a hexad stabilizer, the general/native constructors,
original-H (4.9) and unconditional recognition remain separate obligations.

The internal import of AutomizerFF is used only to verify that its existing
transport equivalence sends the original marker to its conjugate; its
public definitions and boundary are unchanged.

Source: Aschbacher--Segev, The uniqueness of groups of type J4, Invent.
Math. 105 (1991), (4.6)--(4.8), pp.598--599, and section 5,
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

/-- The original markings identify the two overlap images as actual native
trio and sextet stabilizers, with the same cocode coordinates and marker. -/
theorem sourceOrbit_m24_three_space_marked_overlaps :
    ∃ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic))
      (d : ThreeSpaceData (z : G) cubic X)
      (U : Sylow 2 G) (g : centralizer ({(z : G)} : Set G))
      (trio : Trio) (sextet : Sextet),
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
  let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨cubic,X,d,U,g,P,hU,hR,hT,hJ,hZA,hAS,he,hc,hN,hP,hKB,_,_,hBc,_,hQc,_⟩ :=
    sourceOrbit_m24_three_space_point_line D h hmany hV hq hnon a E hE z hz hne hquot
  let W := D.sourceOrbit.map (MulAut.conj (g : G)).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map (MulAut.conj (g : G)).toMonoidHom
  let a' := (automizerMapEquiv D.sourceOrbit (MulAut.conj (g : G))).symm.trans a
  let F := (automizerModuleEquiv D.sourceOrbit (MulAut.conj (g : G))).symm.trans E
  let f := a'.toMonoidHom.comp W.normalizerMonoidHom.rangeRestrict
  have hf : Function.Surjective f := a'.surjective.comp W.normalizerMonoidHom.rangeRestrict_surjective
  have hCW : centralizer (W : Set G) = W :=
    sourceOrbit_m24_conjugate_selfCentralizing D h hmany hV hq hnon a E hE z hz hne hquot g
  have hk : f.ker = W.subgroupOf (normalizer (W : Set G)) := by
    rw [MonoidHom.ker_comp_of_injective _ _ a'.injective,
      MonoidHom.ker_rangeRestrict,normalizerMonoidHom_ker,hCW]
  have hF : ∀ n v, F (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (F (Additive.ofMul v)) := by
    intro n v
    exact sourceOrbit_m24_conjugate_cocode D a E hE g
      (W.normalizerMonoidHom.rangeRestrict n) (Additive.ofMul v)
  have hWA : W = elementaryAbelianMaxJ (U : Subgroup G) := hJ
  have hWB : W ≤ d.pointLineGroup (U : Subgroup G) := by
    rw [hWA]
    exact le_inf (hAS.trans (Subgroup.centralizer_le_normalizer _))
      (elementaryAbelianMaxJ (U : Subgroup G)).le_normalizer
  have hBN : d.pointLineGroup (U : Subgroup G) ≤ normalizer (W : Set G) := by
    rw [hWA]
    exact inf_le_right
  have hUB : (U : Subgroup G) ≤ d.pointLineGroup (U : Subgroup G) :=
    le_inf (hU.trans inf_le_right) ((U : Subgroup G).le_normalizer.trans
      (normalizer_le_normalizer_elementaryAbelianMaxJ _))
  obtain ⟨trio,htrio,hpre⟩ := marked_overlap_trio W (d.pointLineGroup (U : Subgroup G))
    hWB hBN f hf hk (IsElementaryAbelian.isPGroup 2 W) (hWA.symm ▸ hc) U hUB hBc hQc
  have hrel : (d.pointLineGroup (U : Subgroup G)).subgroupOf (normalizer (W : Set G)) =
      (normalizer (d.space : Set G)).subgroupOf (normalizer (W : Set G)) := by
    ext n
    change (n.val ∈ normalizer (d.space : Set G) ∧
      n.val ∈ normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G)) ↔ _
    exact and_iff_left (hWA ▸ n.property)
  rw [hrel] at htrio hpre
  obtain ⟨sextet,hs⟩ := D.sourceOrbit_m24_central_sextet h hmany hV hq hnon a E hE z hz hne
  let w : W := (MulAut.conj (g : G)).subgroupMap D.sourceOrbit z
  have hw : (w : G) = (z : G) :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp g.property)
  have hws : F (Additive.ofMul w) = sextetVector sextet := by
    have hew : Additive.ofMul w = automizerModuleEquiv D.sourceOrbit
        (MulAut.conj (g : G)) (Additive.ofMul z) := rfl
    rw [hew]
    exact (LinearEquiv.symm_apply_apply _ _ |> congrArg E).trans hs
  have hp := marked_cocode_plane_preimage W f F hF w sextet hws
  have hi := marked_cocode_plane_image W f hf F hF w sextet hws
  rw [hw] at hp hi
  have hK : d.K ≤ normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G) :=
    hKB.trans inf_le_right
  have hplane := marked_cocode_plane_card W f hf hk (hWA.symm ▸ hc) F hF w sextet hws
  rw [hw,hWA] at hplane
  have hlineker : f.ker ≤ (normalizer (d.space : Set G)).subgroupOf (normalizer (W : Set G)) := by
    rw [hk]
    exact fun n hn => (hWB hn).1
  have hplaneker : f.ker ≤ (centralizer ({(z : G)} : Set G)).subgroupOf (normalizer (W : Set G)) := by
    rw [hk]
    intro n hn
    apply mem_centralizer_singleton_iff.mpr
    rw [←hw]
    exact ((Commute.all (⟨n.val,hn⟩ : W) w).map W.subtype).eq
  have hflagindex : (trioStabilizer trio).relIndex (sextetStabilizer sextet) = 15 := by
    rw [←htrio,←hi,relIndex_map_map,sup_of_le_left hlineker,sup_of_le_left hplaneker]
    change ((normalizer (d.space : Set G)).comap (normalizer (W : Set G)).subtype).relIndex
      ((centralizer ({(z : G)} : Set G)).subgroupOf (normalizer (W : Set G))) = 15
    rw [relIndex_comap,subgroupOf_map_subtype]
    simpa only [inf_comm,hWA] using d.pointPlane_line_index ht _ hK hBc hplane
  have hcubic := marked_pointPlane_contains_cubic ht cubic
    (normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G)) hplane
  have hprojection := marked_pointPlane_cubic_image ht cubic
    (normalizer (elementaryAbelianMaxJ (U : Subgroup G) : Set G)) hplane
  have hflag := Recognition.JankoFour.SourceIncidence.NativeFlags.incident_of_index trio sextet hflagindex
  exact ⟨cubic,X,d,U,g,trio,sextet,hU,hR,hT,hJ,hZA,hAS,hN,⟨P,hP⟩,
    hplane,d.pointLine_plane_card ht _ hK hBc,d.pointPlane_line_index ht _ hK hBc hplane,
    d.planeLine_point_index ht _ hK hBc,hcubic,hprojection.1,hprojection.2,hflag,hf,hk,hF,htrio,hpre,hi,hp.symm,w,hw,hws⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
