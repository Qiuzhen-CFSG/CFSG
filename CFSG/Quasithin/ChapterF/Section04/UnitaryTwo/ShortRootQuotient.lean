module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot.OrthogonalQuotient
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourShortCentralizer
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ShortRootFixedFour
public import Theory.GroupTheory.UniqueFixedCosetQuotient

/-!
# The original short-root quotient in a faithful completion

The marked short root belongs to the original overlap. The point-endpoint
centralizer hypothesis bounds the common centralizer of the long and short
roots by the plane endpoint. We retain the actual embedding of the model
short centralizer and its quotient by the central short-root line.

In C_G(t)/⟨t⟩ the image X_t^* has order 48 and its actual normal elementary
subgroup V^* has order four. Every nonidentity element of V^* is conjugate
to the image of the marked long root. These constructions supply the literal
local data of Aschbacher–Smith F.4.42, printed p.295; uniqueness of its fixed
coset and the subsequent recognition are separate source steps.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourPlaneLocal UnitaryFourShortRoot
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.ShortRootQuotient
open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open CFSG.Quasithin.ChapterF.UnitaryTwo
open ShortRootFixedFour
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "L" => L2Matrix 1 hn
local notation "X" => shortCentralizer F σ hσ
def modelShort : L := shortLocal F σ hσ
local notation "t" => modelShort

theorem short_mem_point : (t).val ∈ pointParabolicMatrix 1 hn := by
  change (shortLocal F σ hσ).val ∈ pointParabolicSU F (form F σ hσ)
  rw [mem_pointParabolicSU]
  exact ⟨rfl,rfl,rfl⟩

def shortPoint : pointParabolic 1 hn :=
  ⟨projection 1 hn (t).val, ⟨_,short_mem_point,rfl⟩⟩

private def shortOverlap : overlap 1 hn :=
  ⟨shortPoint.val, by
    rw [← exact_overlap]
    exact ⟨shortPoint.property,L2_le_planeParabolic 1 hn (L2ProjectIso 1 hn t).property⟩⟩

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
  (amalgam 1 hn) (G := G0)) (i : G0 →* G)

theorem short_image : matrixPlaneEmbedding c i t = i (c.left shortPoint) :=
  (congrArg i (DFunLike.congr_fun c.compatible shortOverlap)).symm

/-- The selected short root in the actual completion. -/
def sourceShort : G := matrixPlaneEmbedding c i t

/-- The actual model centralizer inside the ambient short-root centralizer. -/
def shortCentralizerEmbedding : X →* centralizer ({sourceShort c i} : Set G) :=
  ((matrixPlaneEmbedding c i).comp (X).subtype).codRestrict _ (by
    intro x
    apply mem_centralizer_singleton_iff.mpr
    exact (map_mul (matrixPlaneEmbedding c i) x.val t).symm.trans
      ((congrArg (matrixPlaneEmbedding c i) (mem_centralizer_singleton_iff.mp x.property)).trans
        (map_mul (matrixPlaneEmbedding c i) t x.val)))

theorem shortCentralizerEmbedding_injective (hi : Function.Injective i) :
    Function.Injective (shortCentralizerEmbedding c i) := by
  intro x y he
  apply Subtype.ext
  exact matrixPlaneEmbedding_injective c i hi (congrArg Subtype.val he)

/-- The common centralizer of the marked long and short roots already lies
in the original plane endpoint. -/
theorem source_common_centralizer_le_plane
    (hi : Function.Injective i)
    (hc : centralizer ({i (c.left longPoint)} : Set G) ≤ (i.comp c.left).range) :
    centralizer ({sourceShort c i} : Set G) ⊓
      centralizer ({i (c.left longPoint)} : Set G) ≤ (i.comp c.right).range := by
  intro g hg
  obtain ⟨p,hp⟩ := hc hg.2
  have he : p * shortPoint = shortPoint * p := by
    apply (hi.comp c.left_injective)
    have he := mem_centralizer_singleton_iff.mp hg.1
    change g * matrixPlaneEmbedding c i modelShort = matrixPlaneEmbedding c i modelShort * g at he
    rw [short_image, ← hp] at he
    simpa only [Function.comp_apply,MonoidHom.comp_apply,map_mul] using he
  obtain ⟨a,ha,hap⟩ := p.property
  have hmat : a * (t).val = (t).val * a := by
    apply projection_injective 1 hn
    have he' := congrArg (fun x : pointParabolic 1 hn => x.val) he
    change p.val * projection 1 hn modelShort.val = projection 1 hn modelShort.val * p.val at he'
    simpa only [map_mul,hap] using he'
  have hplane : a ∈ planeParabolicMatrix 1 hn :=
    centralizer_short_le_plane F σ hσ (mem_centralizer_singleton_iff.mpr hmat)
  have hpPlane : p.val ∈ planeParabolic 1 hn := ⟨a,hplane,hap⟩
  let b : overlap 1 hn := ⟨p.val, by rw [← exact_overlap]; exact ⟨p.property,hpPlane⟩⟩
  refine ⟨(amalgam 1 hn).right b, ?_⟩
  exact (congrArg i (DFunLike.congr_fun c.compatible b)).symm.trans hp

/-- The complete marked common centralizer is the image of the literal
model short centralizer, without an extra centralizer-size assumption. -/
theorem source_common_centralizer_le_short_image
    (hi : Function.Injective i)
    (hc : centralizer ({i (c.left longPoint)} : Set G) ≤ (i.comp c.left).range) :
    centralizer ({sourceShort c i} : Set G) ⊓
      centralizer ({i (c.left longPoint)} : Set G) ≤
        (X).map (matrixPlaneEmbedding c i) := by
  intro g hg
  obtain ⟨p,hp⟩ := source_common_centralizer_le_plane c i hi hc hg
  have hpL : p.val ∈ L2 1 hn := BinaryCompletion.plane_eq_local ▸ p.property
  let q : L2 1 hn := ⟨p.val,hpL⟩
  let a := (L2ProjectIso 1 hn).symm q
  have he : matrixPlaneEmbedding c i a = g := by
    change PlainFusion.planeEmbedding c i (L2ProjectIso 1 hn a) = g
    rw [MulEquiv.apply_symm_apply]
    exact hp
  refine ⟨a,?_,he⟩
  apply mem_centralizer_singleton_iff.mpr
  apply matrixPlaneEmbedding_injective c i hi
  have hh : matrixPlaneEmbedding c i a * matrixPlaneEmbedding c i modelShort =
      matrixPlaneEmbedding c i modelShort * matrixPlaneEmbedding c i a := by
    rw [he]
    exact mem_centralizer_singleton_iff.mp hg.1
  exact (map_mul (matrixPlaneEmbedding c i) a modelShort).trans
    (hh.trans (map_mul (matrixPlaneEmbedding c i) modelShort a).symm)



/-- The actual ambient centralizer of the selected short root. -/
abbrev ambientShortCentralizer := centralizer ({sourceShort c i} : Set G)

/-- The short root remains a central element in its actual ambient centralizer. -/
def ambientMark : ambientShortCentralizer c i :=
  ⟨sourceShort c i, mem_centralizer_singleton_iff.mpr rfl⟩

theorem ambientMark_central : ambientMark c i ∈ center (ambientShortCentralizer c i) := by
  apply mem_center_iff.mpr
  intro g
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.mp g.property

/-- The original central subgroup ⟨t⟩, inside C_G(t). -/
def ambientLine : Subgroup (ambientShortCentralizer c i) := zpowers (ambientMark c i)

instance ambientLine_normal : (ambientLine c i).Normal := by
  constructor
  intro n hx g
  have hc : n ∈ center (ambientShortCentralizer c i) :=
    (zpowers_le.mpr (ambientMark_central c i)) hx
  have he : g * n * g⁻¹ = n := by rw [mem_center_iff.mp hc g,mul_inv_cancel_right]
  rw [he]
  exact hx

theorem shortCentralizerEmbedding_mark :
    shortCentralizerEmbedding c i ShortRoot.mark = ambientMark c i := rfl

/-- The literal map X_t → C_G(t)/⟨t⟩. -/
def sourceQuotientMap : X →* ambientShortCentralizer c i ⧸ ambientLine c i :=
  (QuotientGroup.mk' (ambientLine c i)).comp (shortCentralizerEmbedding c i)

theorem sourceQuotientMap_ker (hi : Function.Injective i) :
    (sourceQuotientMap c i).ker = ShortRoot.centralLine := by
  ext x
  change QuotientGroup.mk' (ambientLine c i) (shortCentralizerEmbedding c i x) = 1 ↔ x ∈ ShortRoot.centralLine
  change (QuotientGroup.mk (shortCentralizerEmbedding c i x) : ambientShortCentralizer c i ⧸ ambientLine c i) = 1 ↔ x ∈ ShortRoot.centralLine
  rw [QuotientGroup.eq_one_iff]
  change shortCentralizerEmbedding c i x ∈ zpowers (ambientMark c i) ↔ x ∈ zpowers ShortRoot.mark
  rw [← shortCentralizerEmbedding_mark, ← MonoidHom.map_zpowers]
  constructor
  · rintro ⟨y,hy,he⟩
    exact shortCentralizerEmbedding_injective c i hi he ▸ hy
  · intro hx
    exact ⟨x,hx,rfl⟩

/-- The original model quotient embeds faithfully in the actual ambient quotient. -/
def sourceQuotientEmbedding (hi : Function.Injective i) :
    X ⧸ ShortRoot.centralLine →* ambientShortCentralizer c i ⧸ ambientLine c i :=
  QuotientGroup.lift ShortRoot.centralLine (sourceQuotientMap c i)
    (sourceQuotientMap_ker c i hi).ge

theorem sourceQuotientEmbedding_injective (hi : Function.Injective i) :
    Function.Injective (sourceQuotientEmbedding c i hi) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr (sourceQuotientMap_ker c i hi).symm

/-- The subgroup called X_t^* in the source. -/
def quotientEndpoint : Subgroup (ambientShortCentralizer c i ⧸ ambientLine c i) :=
  (sourceQuotientMap c i).range

/-- The subgroup called V^* in the source, using the actual quotient map. -/
def sourceFour : Subgroup (ambientShortCentralizer c i ⧸ ambientLine c i) :=
  ShortRoot.orthogonalInCentralizer.map (sourceQuotientMap c i)

theorem quotientEndpoint_card (hi : Function.Injective i) : Nat.card (quotientEndpoint c i) = 48 := by
  have h := (sourceQuotientMap c i).ker.card_mul_index
  rw [index_ker,sourceQuotientMap_ker c i hi,ShortRoot.centralLine_card,ShortRoot.centralizer_card] at h
  change 2 * Nat.card (quotientEndpoint c i) = 96 at h
  omega

theorem sourceFour_eq_map (hi : Function.Injective i) :
    sourceFour c i = ShortRoot.quotientFour.map (sourceQuotientEmbedding c i hi) := by
  rw [ShortRoot.quotientFour,Subgroup.map_map]
  change _ = ShortRoot.orthogonalInCentralizer.map
    ((QuotientGroup.lift _ _ _).comp (QuotientGroup.mk' _))
  rw [QuotientGroup.lift_comp_mk']
  rfl

theorem sourceFour_card (hi : Function.Injective i) : Nat.card (sourceFour c i) = 4 := by
  rw [sourceFour_eq_map c i hi,card_map_of_injective (sourceQuotientEmbedding_injective c i hi)]
  exact ShortRoot.quotientFour_card

instance sourceFour_elementary : IsElementaryAbelian 2 (sourceFour c i) :=
  IsElementaryAbelian.map (sourceQuotientMap c i)

theorem sourceFour_le_endpoint : sourceFour c i ≤ quotientEndpoint c i :=
  map_le_range _ _

instance sourceFour_normal : ((sourceFour c i).subgroupOf (quotientEndpoint c i)).Normal := by
  let : ShortRoot.orthogonalInCentralizer.Normal := orthogonalRadical_normal F σ hσ
  have he : (sourceFour c i).subgroupOf (quotientEndpoint c i) =
      ShortRoot.orthogonalInCentralizer.map (sourceQuotientMap c i).rangeRestrict := by
    ext x
    constructor
    · rintro ⟨y,hy,he⟩
      exact ⟨y,hy,Subtype.ext he⟩
    · rintro ⟨y,hy,he⟩
      exact ⟨y,hy,congrArg Subtype.val he⟩
  rw [he]
  exact Subgroup.Normal.map inferInstance _ (sourceQuotientMap c i).rangeRestrict_surjective

/-- Every nonidentity vector of the actual V^* is a conjugate of the
original marked long root in C_G(t)/⟨t⟩. -/
theorem sourceFour_fusion {v : ambientShortCentralizer c i ⧸ ambientLine c i}
    (hv : v ∈ sourceFour c i) (hv1 : v ≠ 1) :
    IsConj (sourceQuotientMap c i (radicalIntoCentralizer F σ hσ
      (Multiplicative.ofAdd (longParameter F σ)))) v := by
  apply binary_orthogonal_image_fusion F σ hσ
    (show Nat.card (FixedBy.subfield F σ) = 2 from PointLocal.fixedField_card 1 hn)
    (sourceQuotientMap c i) ?_ hv hv1
  change QuotientGroup.mk' (ambientLine c i) (ambientMark c i) = 1
  exact (QuotientGroup.eq_one_iff _).mpr (mem_zpowers _)

end CFSG.Quasithin.ChapterF.UnitaryTwo.ShortRootQuotient
