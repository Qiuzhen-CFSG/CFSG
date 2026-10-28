module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.PointData
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.PlaneOverlaps
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.LineData
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Defs
import all CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF

/-!
# Constructing all original Mathieu local data

The earlier three-space and its common Sylow have Thompson subgroup equal
to a conjugate of the original cocode subgroup. Conjugating the constructed
Todd splitting by that same element aligns its vector inclusion and its
M24 projection with the existing trio and sextet markings. The proved
pair--hexad preimages retain the original cubic quotient, so the line-data
constructor supplies the compatible line group with its original K and S.
The four-dimensional natural action uses the same S/R marking throughout.

Every field of SourceIncidence.LocalData is thereby constructed from the
original marked Mathieu hypotheses and hquot. No PointData, LineData,
local geometry, splitting or incidence premise is added. The conclusion
also retains the original Sylow conjugator and both transported Todd
markings for subsequent source comparison. Native and general type-J4
local-data construction and full recognition remain separate obligations.

Source: Aschbacher--Segev, The uniqueness of groups of type J4,
Invent. Math. 105 (1991), (4.4)--(4.8), pp.597--599,
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

/-- The complete earlier local algebra, retaining both original Todd markings. -/
theorem sourceOrbit_m24_localData :
    let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    ∃ (data : Recognition.JankoFour.SourceIncidence.LocalData ht)
      (g : centralizer ({(z : G)} : Set G)),
      (T : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom = (data.T : Subgroup G) ∧
      data.P.E = D.sourceOrbit.map (MulAut.conj (g : G)).toMonoidHom ∧
      data.P.M = L.map (MulAut.conj (g : G)).toMonoidHom ∧
      (∀ w : D.sourceOrbit, data.P.vectorEmbedding
        (Multiplicative.ofAdd (E (Additive.ofMul w))) = MulAut.conj (g : G) w.val) ∧
      let W := D.sourceOrbit.map (MulAut.conj (g : G)).toMonoidHom
      let a' := (automizerMapEquiv D.sourceOrbit (MulAut.conj (g : G))).symm.trans a
      ∃ hm : data.P.M = normalizer (W : Set G),
        ∀ n : data.P.M, data.P.projection n = a' (W.normalizerMonoidHom.rangeRestrict
          (MulEquiv.subgroupCongr hm n)) := by
  let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨cubic,X,d,U,g,trio,sextet,pair,hexad,hU,hR,hT,hJ,hZE,hES,hN,hA,
    hplane,htriple,hpi,hli,hcubic,hc,hpre,hflag,hpair,hhex,hsub,hpairImage,
    hpairPre,hhexImage,hhexPre,htail⟩ :=
    D.sourceOrbit_m24_three_space_plane_flag h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨P0,hP0c,hP0E,hP0M,hP0q,hP0v⟩ :=
    D.sourceOrbit_m24_pointData h hmany hV hq hnon a E hE z hz hne hquot cubic
  let c := MulAut.conj (g : G)
  let W := D.sourceOrbit.map c.toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map c.toMonoidHom
  let a' := (automizerMapEquiv D.sourceOrbit c).symm.trans a
  let F := (automizerModuleEquiv D.sourceOrbit c).symm.trans E
  let f := a'.toMonoidHom.comp W.normalizerMonoidHom.rangeRestrict
  obtain ⟨hf,hker,hF,htrio,_,hsextet,_,w,hw,hws⟩ := htail
  have hM : P0.M.map c.toMonoidHom = normalizer (W : Set G) := by
    rw [hP0M, map_equiv_normalizer_eq]
  let t : ToddGroup ≃* normalizer (W : Set G) :=
    P0.toddEquiv.trans ((c.subgroupMap P0.M).trans (MulEquiv.subgroupCongr hM))
  let P : PointData (z : G) := {
    cubic := cubic
    M := normalizer (W : Set G)
    toddEquiv := t
    hexad := hexad
    hexad_mem := hhex
    overlap := by
      rw [show W = elementaryAbelianMaxJ (U : Subgroup G) from hJ]
      exact hhexPre }
  have hvec (w0 : D.sourceOrbit) : P.vectorEmbedding
      (Multiplicative.ofAdd (E (Additive.ofMul w0))) = c w0.val := by
    change c ((P0.toddEquiv (SemidirectProduct.inl
      (Multiplicative.ofAdd (E (Additive.ofMul w0))))).val) = c w0.val
    rw [hP0v w0]
  have hPE : P.E = W := by
    have hembed : P.vectorEmbedding = c.toMonoidHom.comp P0.vectorEmbedding := rfl
    rw [PointData.E, hembed, MonoidHom.range_comp]
    change P0.E.map c.toMonoidHom = W
    rw [hP0E]
  have htq (x : ToddGroup) : f (t x) = x.right := by
    let n : normalizer (D.sourceOrbit : Set G) :=
      MulEquiv.subgroupCongr hP0M (P0.toddEquiv x)
    have hauto : automizerMapEquiv D.sourceOrbit c
        (D.sourceOrbit.normalizerMonoidHom.rangeRestrict n) =
          W.normalizerMonoidHom.rangeRestrict (t x) := by
      apply Subtype.ext
      apply MulEquiv.ext
      intro v
      obtain ⟨v0,rfl⟩ := (c.subgroupMap D.sourceOrbit).surjective v
      rw [automizerMapEquiv_apply]
      apply Subtype.ext
      change c (n.val * v0.val * n.val⁻¹) =
        c (P0.toddEquiv x).val * c v0.val * (c (P0.toddEquiv x).val)⁻¹
      simp only [map_mul, map_inv]
      rfl
    change a ((automizerMapEquiv D.sourceOrbit c).symm
      (W.normalizerMonoidHom.rangeRestrict (t x))) = x.right
    rw [←hauto, MulEquiv.symm_apply_apply]
    exact hP0q x
  have hproj : P.projection = f := by
    apply MonoidHom.ext
    intro n
    obtain ⟨x,rfl⟩ := t.surjective n
    change (t.symm (t x)).right = f (t x)
    rw [t.symm_apply_apply, htq]
  have hmarked (v : W) : P.vectorEmbedding
      (Multiplicative.ofAdd (F (Additive.ofMul v))) = v.val := by
    obtain ⟨v0,rfl⟩ := (c.subgroupMap D.sourceOrbit).surjective v
    have hew : F (Additive.ofMul (c.subgroupMap D.sourceOrbit v0)) =
        E (Additive.ofMul v0) :=
      congrArg E ((automizerModuleEquiv D.sourceOrbit c).symm_apply_apply (Additive.ofMul v0))
    exact (congrArg (fun v : Cocode => P.vectorEmbedding (Multiplicative.ofAdd v)) hew).trans (hvec v0)
  have hPM : P.M = normalizer (P.E : Set G) := by
    rw [hPE]
  have hEU : P.E = elementaryAbelianMaxJ (U : Subgroup G) := hPE.trans hJ
  have hZP : d.space ≤ P.E := hEU.symm ▸ hZE
  have hPS : P.E ≤ d.S := hEU.symm ▸ hES
  have hK : d.K ≤ P.M := by
    obtain ⟨_,_,hKN⟩ := D.sourceOrbit_m24_common_thompson_contains_space h hmany hV hq hnon
      a E hE z hz hne hquot d U (g : G) (hU.trans inf_le_right)
      ((d.space_le_R ht).trans hR) hJ
    change d.K ≤ normalizer (W : Set G)
    rw [show W = elementaryAbelianMaxJ (U : Subgroup G) from hJ]
    exact hKN
  obtain ⟨A,hA⟩ := hA
  have hAP : d.symmetricImage ht P.E = AlternatingSylowNormalizer.image A := hEU.symm ▸ hA
  have hpiP : (normalizer (d.space : Set G)).relIndex
      (P.M ⊓ Recognition.JankoFour.centralizer (z : G)) = 15 := by
    change (normalizer (d.space : Set G)).relIndex (normalizer (W : Set G) ⊓ _) = _
    rw [show W = elementaryAbelianMaxJ (U : Subgroup G) from hJ]
    exact hpi
  obtain ⟨line,hLN,hLK,hLS⟩ := d.exists_lineData P ht U hPM hEU hR hZP hPS hK A hAP hpiP
  let := d.multiplicitySpace_elementary ht
  obtain ⟨natA,natF,hnat⟩ := d.exists_multiplicity_natural_equiv ht
  have hUM : (U : Subgroup G) ≤ P.M := by
    rw [hPM,hEU]
    exact (U : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _)
  let data : Recognition.JankoFour.SourceIncidence.LocalData ht := {
    e := cubic
    X := X
    d := d
    P := P
    cubic_eq := rfl
    L := line
    point_normalizer := hPM.symm
    line_normalizer := hLN
    K_image := hLK
    S_image := hLS
    T := U
    sylow_le := by
      rw [hLN]
      exact le_inf (le_inf (hU.trans inf_le_left) hUM) (hU.trans inf_le_right)
    E_eq_maxJ := hEU
    space_le_E := hZP
    E_le_S := hPS
    alternatingSylow := A
    E_quotient := hAP
    trio := trio
    sextet := sextet
    line_image := by rw [hLN, hproj]; exact htrio
    plane_image := by rw [hproj]; exact hsextet
    marker_vector := by rw [←hws]; exact (hmarked w).trans hw
    naturalEquiv := natF
    alternatingEquiv := natA
    natural_equivariant := fun b v => hnat b (Additive.ofMul v) }
  refine ⟨data,g,hT,hPE,?_,hvec,rfl,?_⟩
  · change normalizer (W : Set G) = L.map c.toMonoidHom
    rw [show W = elementaryAbelianMaxJ (U : Subgroup G) from hJ]
    exact hN
  · intro n
    exact DFunLike.congr_fun hproj n

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
