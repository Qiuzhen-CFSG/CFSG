module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalQuotients
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.SeedControl
public import Theory.GroupTheory.SolvableResidual.TwoSupplement
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
public import Theory.GroupTheory.PerfectCenterFrattini

/-!
# Original seed and Baumann control on local-family normalizers

For every escaping constrained K in L(G₁,S), retain H=K N_S(K) and
U=⟨Z^H⟩ with the original Z=Ω₁(Z(T)). The actual normalizer Sylow
identifies O²(H) with K, makes H characteristic two, and places U in the
full local omega-center span while preserving nontrivial Thompson action.
The alpha decomposition therefore compares their moved modules and kernels.

An actual SL₂ image makes H a minimal parabolic: the comparison kernel
above O₂(K) is central in a perfect group, hence Frattini. Natural moved
coordinates on the same quotient then reconstruct a χ-block using the
original Baumann characteristic-normalizer control. The transfer uses
Baum(S)=Baum(N_S(K)) only after Baum(S)-normalization of K is supplied;
it never identifies the full Sylow and Baumann control closures.

This is preparation for the original 15.1.20(2) nonblock exclusion.
Baumann normalization and extraction of the natural coordinates (including
the separate A₅ action branch) remain with this catalogue owner. The
conditional natural theorem does not assert that they have been proved.
No Borel equality, ambient C-componenthood, or S-normalization is assumed.

Source: Aschbacher--Smith 15.1.17, 15.1.20(2), C.1.16(3), C.1.26,
printed pp.1092,1094--1095,125--126,132.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterB ChapterC ChapterC.RankOne.ChiProduct.SelectedRankOne
open Section03 Section03.InitialSource ChapterA.Section05To06
attribute [local instance] RankOneBaumann.semilinear_moved_elementary
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The literal normalizer retains its residual, central seed, and Thompson movement. -/
theorem localFamily_normalizer_seed_setup (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K) :
    let H := K ⊔ d.normalizerSylow K
    ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = d.normalizerSylow K ∧
      generalizedFitting H = pCore 2 H ∧
      pResidual 2 H = K.subgroupOf H ∧
      d.normalizerModule K ≤ normalClosure (omegaOneCenterAmbient (P : Subgroup H) : Set H) ∧
      ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (d.normalizerModule K : Set H) := by
  obtain ⟨⟨P,hP⟩,hJRS,hZR⟩ := d.localFamily_normalizer_setup h hM.1.2 hu hK hq hout hf
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf
  let R := d.normalizerSylow K
  let H := K ⊔ R
  let K0 := K.subgroupOf H
  let : K0.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer inf_le_right)
  have hK0 : K0.IsCComponent := hK.2.1.subgroupOf_of_le le_sup_left
    (sup_le le_sup_left (inf_le_left.trans le_sup_right))
  let : Group.IsPerfect K0 := hK0.perfect
  have hPS : (P : Subgroup H) = R.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le (show R ≤ H from le_sup_right)]
  have hgen : K0 ⊔ (P : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),hP,
      ←MonoidHom.range_eq_map,range_subtype]
  have hfitH : generalizedFitting H = pCore 2 H :=
    (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
      (centralizer_pCore_sup_le 2 K R (hf ▸ centralizer_generalizedFitting_le K)
        (T.isPGroup'.to_le (inf_le_left.trans d.S_le_T)) inf_le_right)
  have hres : pResidual 2 H = K0 :=
    (residuals_of_perfect_normal_sup_twoGroup K0 (P : Subgroup H) P.isPGroup' hgen).1
  refine ⟨P,hP,hfitH,hres,?_,?_⟩
  · apply normalClosure_mono
    intro z hz
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨?_,?_,?_⟩
    · rw [hPS]
      exact hZR hz
    · apply Subtype.ext
      exact ((mem_omegaOneCenterAmbient_iff (T : Subgroup G) (z : G)).mp hz).2.1
    · intro x hx
      exact Subtype.ext (centralInvolutions_le_centralizer_sylow T hz x
        (d.S_le_T (show (x : G) ∈ d.S from (hP ▸ mem_map_of_mem H.subtype hx).1)))
  · intro hj
    have hJQ : elementaryAbelianMaxJ (P : Subgroup H) ≤ pCore 2 H := by
      rw [a.core,←hPS]
      exact le_inf (sSup_le fun _ hA => hA.1) hj
    have he := elementaryAbelianMaxJ_eq_of_intermediate (P : Subgroup H) (pCore 2 H)
      hJQ (pCore_isPGroup.le_sylow_of_normal P)
    have hn : K0 ≤ normalizer (elementaryAbelianMaxJ (P : Subgroup H) : Set H) := by
      rw [←he]
      exact le_normalizer_of_normal.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _)
    have hm := (map_mono (f := H.subtype) hn).trans
      ((elementaryAbelianMaxJ (P : Subgroup H)).le_normalizer_map H.subtype)
    rw [map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
      ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP,hJRS] at hm
    exact d.localFamily_thompson_escape hG hempty hM hJ hu h hK hout hm

/-- The exact restriction of the original Baumann characteristic-normalizer control. -/
theorem localFamily_baumann_control (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) {K : Subgroup G}
    (hbaum : baumann d.S ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ d.normalizerSylow K : Subgroup G))
    (hP : (P : Subgroup (K ⊔ d.normalizerSylow K : Subgroup G)).map
      (K ⊔ d.normalizerSylow K).subtype = d.normalizerSylow K) :
    (baumann (P : Subgroup (K ⊔ d.normalizerSylow K : Subgroup G))).characteristicNormalizerClosure ≤
      M.subgroupOf (K ⊔ d.normalizerSylow K) := by
  let H := K ⊔ d.normalizerSylow K
  have hBR : baumann d.S ≤ d.normalizerSylow K := le_inf inf_le_left hbaum
  have hB : baumann (d.normalizerSylow K) = baumann d.S :=
    baumann_eq_of_intermediate d.S _ hBR inf_le_left
  have hm : (baumann (P : Subgroup H)).map H.subtype = baumann d.S := by
    unfold baumann thompsonAlpha
    rw [baumann_map_injective H.subtype H.subtype_injective,hP]
    exact hB
  have hb : baumann (P : Subgroup H) = (baumann d.S).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hm,map_subgroupOf_eq_of_le (hBR.trans le_sup_right)]
  rw [hb]
  exact characteristicNormalizerClosure_subgroupOf_le (hBR.trans le_sup_right)
    (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).2.2.1

/-- Apply the seed comparison to the literal source normalizer module. -/
theorem localFamily_normalizer_omega_comparison (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K) :
    let H := K ⊔ d.normalizerSylow K
    ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = d.normalizerSylow K ∧
      (thompsonAlpha (P : Subgroup H) ≤ ⁅d.normalizerModule K,K.subgroupOf H⁆ ⊔
        (thompsonAlpha (P : Subgroup H) ⊓ centralizer (K.subgroupOf H : Set H)) →
        let W := normalClosure (omegaOneCenterAmbient (P : Subgroup H) : Set H)
        ⁅W,K.subgroupOf H⁆ = ⁅d.normalizerModule K,K.subgroupOf H⁆ ∧
          centralizer (W : Set H) = centralizer (d.normalizerModule K : Set H)) := by
  obtain ⟨P,hP,hfitH,hres,hseed,_⟩ :=
    d.localFamily_normalizer_seed_setup hG hempty hM hJ hu h hK hq hout hf
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf
  let := a.reduced.elementary
  refine ⟨P,hP,?_⟩
  intro ha
  have ha' := hres.symm ▸ ha
  have hc := seed_omega_comparison P (d.normalizerModule K) a.reduced hfitH hseed ha'
  simpa only [hres] using hc

/-- The actual rank-one image makes K N_S(K) a minimal parabolic.
The original two-core quotient has central, hence Frattini, comparison kernel. -/
theorem NormalizerAction.minimalParabolic_of_rankOne {d : CaseIComponentData T M Mc V}
    {K : Subgroup G} (a : d.NormalizerAction K)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : d.normalizerImage K ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (P : Sylow 2 (K ⊔ d.normalizerSylow K : Subgroup G))
    (hP : (P : Subgroup (K ⊔ d.normalizerSylow K : Subgroup G)).map
      (K ⊔ d.normalizerSylow K).subtype = d.normalizerSylow K) :
    IsMinimalParabolicOver P ⊤ := by
  let H := K ⊔ d.normalizerSylow K
  let K0 := K.subgroupOf H
  let : K0.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer inf_le_right)
  let i : K0 ≃* K := subgroupOfEquivOfLe le_sup_left
  let f := e.toMonoidHom.comp ((d.toNormalizerImage K).comp i.toMonoidHom)
  have hfs : Function.Surjective f := e.surjective.comp
    ((d.toNormalizerImage_surjective K).comp i.surjective)
  have hi : IsPGroup 2 i.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr i.injective]
    exact IsPGroup.of_bot
  have hfk : f.ker ≤ (frattini (K0 ⧸ pCore 2 K0)).comap (QuotientGroup.mk' (pCore 2 K0)) := by
    rw [←i.toMonoidHom.comap_frattini_pCore_of_pKernel i.surjective hi]
    intro x hx
    let := hq
    apply center_le_frattini_of_isPerfect
    apply a.coreToImage_ker_central hq
    change d.toNormalizerImage K (i x) = 1
    apply e.injective
    exact hx.trans (map_one e.toMonoidHom).symm
  have hgen : K0 ⊔ (P : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),hP,
      ←MonoidHom.range_eq_map,range_subtype]
  exact minimal_over_normal_rankOne_frattini F K0 P hgen f hfs hfk

/-- Natural coordinates on the original quotient imply a block, using only
Baumann normalization of K. This retains the two remaining source inputs
(normalization and the natural row); it is not the unconditional nonblock exclusion. -/
theorem localFamily_chi_of_natural_normalizer (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K)
    (hbaum : baumann d.S ≤ normalizer (K : Set G)) (a : d.NormalizerAction K) :
    let H := K ⊔ d.normalizerSylow K
    let U := d.normalizerModule K
    letI := a.reduced.elementary
    let q := QuotientGroup.mk' (centralizer (U : Set H))
    let L := generalizedFitting (H ⧸ centralizer (U : Set H))
    ∀ (P : Sylow 2 H), (P : Subgroup H).map H.subtype = d.normalizerSylow K →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
        (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F), 2 < Nat.card F →
        ∀ (f : Additive (⁅U,pResidual 2 H⁆ : Subgroup H) →ₗ[ZMod 2] (Fin 2 → F)),
          Function.Surjective f →
          (∀ (g : H) (hg : q g ∈ L) (v : Additive (⁅U,pResidual 2 H⁆ : Subgroup H)),
            f (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
              SL2NaturalOffenders.NoStrong.natural (e ⟨q g,hg⟩) (f v)) →
          (∀ (v : Additive (⁅U,pResidual 2 H⁆ : Subgroup H)),
            f v = 0 ↔ (v.toMul : H) ∈ centralizer (pResidual 2 H : Set H)) →
          IsChiBlock K := by
  dsimp only
  intro P hP F _ _ _ _ e hF f hfs hfe hfk
  let H := K ⊔ d.normalizerSylow K
  let := a.reduced.elementary
  obtain ⟨P0,hP0,hfitH,hres,hseed,hmove⟩ :=
    d.localFamily_normalizer_seed_setup hG hempty hM hJ hu h hK hq hout hf
  have hPP : P0 = P := by
    apply Sylow.ext
    apply map_injective H.subtype_injective
    exact hP0.trans hP.symm
  subst P0
  have hmin := a.minimalParabolic_of_rankOne hq F
    ((MulEquiv.subgroupCongr a.fitting).trans e) P hP
  have hcpu := d.localFamily_baumann_control hG hM hJ h hbaum P hP
  have hesc : ¬ pResidual 2 H ≤ M.subgroupOf H := by
    rw [hres]
    intro hh
    apply d.localFamily_not_le_M hG hempty hM hu hK hout
    intro k hk
    exact hh (show (⟨k,mem_sup_left hk⟩ : H) ∈ K.subgroupOf H from hk)
  have hb := normal_layer_seed_block_of_baumann_control P hmin (d.normalizerModule K)
    a.reduced hmove (QuotientGroup.mk' (centralizer (d.normalizerModule K : Set H)))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) _ e hF
    f hfs hfe hfk hseed hfitH (M.subgroupOf H) hcpu hesc
  rw [hres] at hb
  exact RankOne.ChiProduct.chi_of_equiv (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)) hb.2

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
