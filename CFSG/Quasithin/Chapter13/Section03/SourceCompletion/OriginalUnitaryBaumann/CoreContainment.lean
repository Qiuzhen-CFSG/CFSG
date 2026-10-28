module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.CoreAction
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalApplicability
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Stellmacher.BaumannNormalizer
public import Stellmacher.BaumannMap
/-!
# The two-core of the original component–Baumann product

Work inside the actual LT. The chosen module detects its two-core as its
centralizer, and two-perfectness identifies L with its two-residual.
Baumann's centralizer saturation applies to the marked point Thompson
image. The product L Baum(R) is normal in LT because T normalizes both
factors. Its two-core therefore centralizes V and saturation puts it
inside Baum(R), where it is precisely C_Baum(R)(V).
Source: Aschbacher–Smith C.1.37 and the first paragraph of13.3.10(2),
printed pp.143,888. The original contrary case is applied in
OriginalUnitaryNoncentrality.BaumannCore.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterB ChapterE Atlas.G2.Natural.BinaryPointFlag Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]

/-- In the original LT, the genuine point Thompson image forces the core of
L Baum(R) into Baum(R); its kernel is exactly the centralizer of V there. -/
theorem unitary_baumann_core_of_point_image
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
    (hJ : (inducedAutomizer V (elementaryAbelianMaxJ R)).map rho =
      Atlas.G2.BinaryCore.elementary) :
    (L ⊔ baumann R).pCoreIn 2 ≤ baumann R ∧
      (L ⊔ baumann R).pCoreIn 2 = baumann R ⊓ centralizer (V : Set G) := by
  let X := L ⊔ (T : Subgroup G)
  let U := V.subgroupOf X
  let K := L.subgroupOf X
  let S := R.subgroupOf X
  have hVX : V ≤ X := chosen.le_sylow.trans le_sup_right
  have hRX : R ≤ X := hRT.trans le_sup_right
  have hXN : X ≤ normalizer (V : Set G) := sup_le chosen.normalizes hTV
  let : U.Normal := normal_subgroupOf_of_le_normalizer hXN
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVX (p := 2)
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer chosen.sylow_normalizes_component)
  let aU : Additive U ≃+ Additive V := (subgroupOfEquivOfLe hVX).toAdditive
  let EU : Additive U ≃ₗ[F] Additive V := { aU with map_smul' := ZMod.map_smul aU }
  let E' := EU.trans E
  let q : X →* Atlas.G2.Model F :=
    (rho.comp V.normalizerMonoidHom.rangeRestrict).comp (inclusion hXN)
  have he' (x : X) (v : U) :
      E' (Additive.ofMul (MulAut.conjNormal x v)) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (q x) (E' (Additive.ofMul v)) :=
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
  have hC : centralizer (U : Set X) = pCore 2 X := by
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
  have hJS : (elementaryAbelianMaxJ S).map X.subtype = elementaryAbelianMaxJ R := by
    rw [←elementaryAbelianMaxJ_map_injective _ X.subtype_injective,
      map_subgroupOf_eq_of_le hRX]
  have hJR : elementaryAbelianMaxJ R ≤ R := sSup_le fun _ hA => hA.1
  have hJ' : (elementaryAbelianMaxJ S).map q = Atlas.G2.BinaryCore.elementary := by
    have hJA : (elementaryAbelianMaxJ S).map (inclusion hXN) =
        (elementaryAbelianMaxJ R).subgroupOf (normalizer (V : Set G)) := by
      apply map_injective (normalizer (V : Set G)).subtype_injective
      rw [map_map]
      change (elementaryAbelianMaxJ S).map X.subtype = _
      rw [hJS,map_subgroupOf_eq_of_le (hJR.trans (hRX.trans hXN))]
    simpa only [q,←Subgroup.map_map,hJA,inducedAutomizer] using hJ
  have hd := unitary_point_baumann_decomposition U q hq E' he' S
    (T.isPGroup'.to_le hRT).comap_subtype
    (fun _ hx => hQR (chosen.le_core hx))
    (fun _ hx => hQR (mem_map_of_mem X.subtype hx)) hC hJ'
  have hBa : (baumann S).map X.subtype = baumann R := by
    exact (baumann_map_injective X.subtype X.subtype_injective S).trans
      (congrArg baumann (map_subgroupOf_eq_of_le hRX))
  have hB : baumann R ≤ X := inf_le_left.trans hRX
  have hY : L ⊔ baumann R ≤ X := sup_le le_sup_left hB
  have hcentral : baumann R ⊓ centralizer (V : Set G) =
      (L ⊔ baumann R) ⊓ centralizer (V : Set G) := by
    have hh := congrArg (map X.subtype) hd.2.2
    rw [hres,map_inf _ _ _ X.subtype_injective,map_inf _ _ _ X.subtype_injective,
      Subgroup.map_sup,hBa,map_centralizer_subtype,map_subgroupOf_eq_of_le hVX,
      map_subgroupOf_eq_of_le (show L ≤ X from le_sup_left)] at hh
    simpa only [←inf_assoc,inf_eq_left.mpr hB,inf_eq_left.mpr hY] using hh
  have hTY : (T : Subgroup G) ≤ normalizer ((L ⊔ baumann R : Subgroup G) : Set G) :=
    (le_inf chosen.sylow_normalizes_component (hTR.trans (normalizer_le_normalizer_baumann R))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hXY : X ≤ normalizer ((L ⊔ baumann R : Subgroup G) : Set G) :=
    sup_le (le_sup_left.trans (L ⊔ baumann R).le_normalizer) hTY
  have hQC : (L ⊔ baumann R).pCoreIn 2 ≤ centralizer (V : Set G) :=
    (pCoreIn_mono_of_normalizes (p := 2) hY hXY).trans chosen.core_centralizes
  have hle : (L ⊔ baumann R).pCoreIn 2 ≤ baumann R :=
    ((le_inf (pCoreIn_le 2 _) hQC).trans hcentral.ge).trans inf_le_left
  refine ⟨hle,le_antisymm (le_inf hle hQC) ?_⟩
  rw [hcentral]
  apply le_pCoreIn_of_normalizes
  · apply (isPGroup_pCoreIn 2 X).to_le
    rw [←hCambient]
    exact inf_le_inf_right _ hY
  · exact inf_le_left
  · apply (le_inf (L ⊔ baumann R).le_normalizer ?_).trans
      (inf_normalizer_le_normalizer_inf)
    exact (hY.trans hXN).trans ((normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (V : Set G))).mp inferInstance)
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
