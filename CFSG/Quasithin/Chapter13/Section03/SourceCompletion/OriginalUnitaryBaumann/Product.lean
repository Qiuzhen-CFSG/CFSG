module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.CoreContainment
public import Theory.AtlasPort.LinearGroups.G2.BinaryNaturalPlane

/-!
# The quotient of the component–Baumann product

The original full natural action restricts to Y = L Baum(R). The root eight
and its proved residual conjugate generate the full G₂(2) image. Normality
of Y in LT identifies the kernel with O₂(Y); the previously proved Baumann
core containment then identifies Baum(R) with the full preimage of the
marked root eight. The quotient equivalence retains the original action map.

This is the exceptional radical marking needed by C.1.31(MS2)(b), not an
odd-index-radical assertion. The original source application is
OriginalUnitaryNoncentrality.PushingUp.
Source: Aschbacher–Smith C.1.37, pp.141–143, and 13.3.10(2), pp.887–888.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterB ChapterE Atlas.G2.Natural.BinaryPointFlag Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]

/-- The marked root eight and one residual conjugate generate the whole image
of the actual component--Baumann product. -/
theorem unitary_product_image_of_residual
    (q : G →* Atlas.G2.Model F) (hq : Function.Surjective q)
    (B : Subgroup G) (hB : B.map q = Atlas.G2.BinaryCore.elementary) :
    (pResidual 2 G ⊔ B).map q = ⊤ := by
  let Y := (pResidual 2 G ⊔ B).map q
  have hE : Atlas.G2.BinaryCore.elementary ≤ Y := hB ▸ map_mono le_sup_right
  obtain ⟨a,ha,hgen⟩ := Atlas.G2.Natural.BinaryPointGeneration.exists_residual_conjugate_generating
  have haY : a ∈ Y := by
    have hm := map_pResidual_of_surjective 2 q hq
    exact map_mono (show pResidual 2 G ≤ pResidual 2 G ⊔ B from le_sup_left) (hm.symm ▸ ha)
  apply top_unique
  rw [←hgen]
  apply sup_le hE
  rintro _ ⟨b,hb,rfl⟩
  exact Y.mul_mem (Y.mul_mem haY (hE hb)) (Y.inv_mem haY)

/-- The original action identifies the quotient of L Baum(R), and Baum(R)
is the full preimage of the actual root eight under this same quotient map. -/
theorem unitary_baumann_product_model
    {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
    (chosen : ChosenModule T L V) (hsimple : IsSimpleGroup (L ⧸ pCore 2 L))
    (hL : IsPPerfect 2 L) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (rho : Automizer V →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W)
    (he : ∀ a v, E (automizerRepresentation V a v) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hfull : (inducedAutomizer V (L ⊔ (T : Subgroup G))).map rho = ⊤)
    (R : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hQR : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R)
    (hJ : (inducedAutomizer V (elementaryAbelianMaxJ R)).map rho = Atlas.G2.BinaryCore.elementary)
    (hB : (inducedAutomizer V (baumann R)).map rho = Atlas.G2.BinaryCore.elementary) :
    let Y := L ⊔ baumann R
    ∃ e : (Y ⧸ pCore 2 Y) ≃* Atlas.G2.Model F,
      (∀ y : Y, e (QuotientGroup.mk' (pCore 2 Y) y) =
        rho (V.normalizerMonoidHom.rangeRestrict
          ⟨y, (sup_le chosen.normalizes (inf_le_left.trans (hRT.trans hTV))) y.property⟩)) ∧
      (baumann R).subgroupOf Y = Atlas.G2.BinaryCore.elementary.comap
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Y))) := by
  intro Y
  let X := L ⊔ (T : Subgroup G)
  let U := V.subgroupOf X
  let K := L.subgroupOf X
  have hVX : V ≤ X := chosen.le_sylow.trans le_sup_right
  have hBX : baumann R ≤ X := inf_le_left.trans (hRT.trans le_sup_right)
  have hYX : Y ≤ X := sup_le le_sup_left hBX
  have hXN : X ≤ normalizer (V : Set G) := sup_le chosen.normalizes hTV
  have hYN : Y ≤ normalizer (V : Set G) := hYX.trans hXN
  let : U.Normal := normal_subgroupOf_of_le_normalizer hXN
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVX (p := 2)
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer chosen.sylow_normalizes_component)
  let EU : Additive U ≃ₗ[F] Additive V :=
    { (subgroupOfEquivOfLe hVX).toAdditive with map_smul' := ZMod.map_smul _ }
  let q : X →* Atlas.G2.Model F :=
    (rho.comp V.normalizerMonoidHom.rangeRestrict).comp (inclusion hXN)
  have he' (x : X) (v : U) :
      (EU.trans E) (Additive.ofMul (MulAut.conjNormal x v)) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (q x)
        ((EU.trans E) (Additive.ofMul v)) :=
    he (V.normalizerMonoidHom.rangeRestrict (inclusion hXN x)) (EU (Additive.ofMul v))
  have hq : Function.Surjective q := by
    intro a
    have ha : a ∈ (inducedAutomizer V X).map rho := hfull.symm ▸ mem_top a
    obtain ⟨_,⟨n,hn,rfl⟩,hnr⟩ := ha
    exact ⟨⟨n.val,hn⟩,hnr⟩
  have hCambient : X ⊓ centralizer (V : Set G) = X.pCoreIn 2 := by
    have hc := congrArg (map L.subtype) (chosen.centralizer_eq_core_of_simple hsimple)
    have hc' : L ⊓ centralizer (V : Set G) = L.pCoreIn 2 := by
      simpa only [pCoreIn,subgroupOf_map_subtype,inf_comm] using hc
    exact ambient_centralizer_eq_core_of_normal_supplement L V (T : Subgroup G)
      chosen.sylow_normalizes_component hVX hXN T.isPGroup' hc' chosen.core_centralizes
  have hk : q.ker = pCore 2 X := by
    rw [unitary_coordinate_kernel U q (EU.trans E) he']
    apply map_injective X.subtype_injective
    rw [map_centralizer_subtype,map_subgroupOf_eq_of_le hVX]
    exact hCambient
  have hres : pResidual 2 X = K := by
    apply pResidual_eq_of_isPPerfect_sup K ((T : Subgroup G).subgroupOf X)
      (hL.of_surjective (subgroupOfEquivOfLe (show L ≤ X from le_sup_left)).symm.toMonoidHom
        (subgroupOfEquivOfLe (show L ≤ X from le_sup_left)).symm.surjective)
      T.isPGroup'.comap_subtype
    rw [←subgroupOf_sup (show L ≤ X from le_sup_left)
      (show (T : Subgroup G) ≤ X from le_sup_right),subgroupOf_self]
  have hBm : ((baumann R).subgroupOf X).map q = Atlas.G2.BinaryCore.elementary := by
    have hh : ((baumann R).subgroupOf X).map (inclusion hXN) =
        (baumann R).subgroupOf (normalizer (V : Set G)) := by
      apply map_injective (normalizer (V : Set G)).subtype_injective
      rw [map_map]
      change ((baumann R).subgroupOf X).map X.subtype = _
      rw [map_subgroupOf_eq_of_le hBX,map_subgroupOf_eq_of_le (hBX.trans hXN)]
    simpa only [q,←Subgroup.map_map,hh,inducedAutomizer] using hB
  have hYm : (Y.subgroupOf X).map q = ⊤ := by
    have hh := unitary_product_image_of_residual q hq ((baumann R).subgroupOf X) hBm
    rw [hres,←subgroupOf_sup (show L ≤ X from le_sup_left) hBX] at hh
    exact hh
  let qY : Y →* Atlas.G2.Model F := q.comp (inclusion hYX)
  have hqY : Function.Surjective qY := by
    apply MonoidHom.range_eq_top.mp
    change (q.comp (inclusion hYX)).range = ⊤
    rw [MonoidHom.range_comp]
    have hi : (inclusion hYX).range = Y.subgroupOf X := by
      ext x
      constructor
      · rintro ⟨y,rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x,hx⟩,rfl⟩
    rw [hi,hYm]
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    (le_inf chosen.sylow_normalizes_component (hTR.trans (normalizer_le_normalizer_baumann R))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hXY : X ≤ normalizer (Y : Set G) :=
    sup_le (le_sup_left.trans Y.le_normalizer) hTY
  have hkY : qY.ker = pCore 2 Y := by
    let : (Y.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer hXY
    have hc := pCore_map_iso 2 (subgroupOfEquivOfLe hYX)
    rw [pCore_subnormal_eq_comap 2
      (inferInstance : (Y.subgroupOf X).Normal).isSubnormal,
      map_equiv_eq_comap_symm',comap_comap] at hc
    change (q.ker).comap (inclusion hYX) = _
    rw [hk]
    exact hc
  let e : (Y ⧸ pCore 2 Y) ≃* Atlas.G2.Model F :=
    (QuotientGroup.quotientMulEquivOfEq hkY.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective qY hqY)
  have heq (y : Y) : e (QuotientGroup.mk' (pCore 2 Y) y) = qY y := rfl
  refine ⟨e,fun y => heq y,?_⟩
  have hmapB : ((baumann R).subgroupOf Y).map qY = Atlas.G2.BinaryCore.elementary := by
    change ((baumann R).subgroupOf Y).map (q.comp (inclusion hYX)) = _
    rw [←map_map]
    have hi : ((baumann R).subgroupOf Y).map (inclusion hYX) = (baumann R).subgroupOf X := by
      apply map_injective X.subtype_injective
      rw [map_map]
      change ((baumann R).subgroupOf Y).map Y.subtype = _
      rw [map_subgroupOf_eq_of_le (show baumann R ≤ Y from le_sup_right),map_subgroupOf_eq_of_le hBX]
    rw [hi,hBm]
  have hcore := (unitary_baumann_core_of_point_image chosen hsimple hL hTV rho E he
    hfull R hRT hTR hQR hJ).1
  have hkb : qY.ker ≤ (baumann R).subgroupOf Y := by
    rw [hkY]
    exact fun x hx => hcore (mem_map_of_mem Y.subtype hx)
  have hf : e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Y)) = qY := by
    apply MonoidHom.ext
    intro y
    exact heq y
  rw [hf,←hmapB,comap_map_eq_self hkb]
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
