module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNonblock
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.FixedWitness

/-!
# Original rank-one fixed witnesses and the remaining support separation

The literal H = K N_S(K) action gives a noncentral J(N_S(K))-fixed
vector in [⟨Z^H⟩,K], without assuming K is a block. Thompson heredity and
injective omega-center transport place that same vector in α(S). The
natural SL₂ and permutation A₅ branches retain their central kernels.
Both the literal core quotient and the original normalizer-image forms
are provided.

If a distinct S-conjugate of the moved support centralizes K, this fixed
vector prevents Baum(S) from moving K. The existing original pair argument
then gives nonblock placement in M_Z. This final implication retains an
explicit support-separation premise; LocalSeparation now constructs it from
the B.5.6 action on the full component orbit.
The original C-components need not commute before passing to the action
quotient. No block assumption or identification of those kernels is used.

Source: Aschbacher--Smith C.1.16(3), pp.125--126, and 15.1.20(2),
pp.1094--1095. General Borel placement and higher-field parabolic
constructions remain separate obligations of this catalogue.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterB ChapterC ChapterC.RankOne.ChiProduct.SelectedRankOne
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
attribute [local instance] RankOneBaumann.semilinear_moved_elementary

/-- The actual moved subgroup of the original seed in K N_S(K), embedded in G. -/
@[expose] def normalizerMoved (d : CaseIComponentData T M Mc V) (K : Subgroup G) : Subgroup G :=
  (⁅d.normalizerModule K,K.subgroupOf (K ⊔ d.normalizerSylow K)⁆).map
    (K ⊔ d.normalizerSylow K).subtype

/-- The moved seed is contained in the original local member. -/
theorem normalizerMoved_le (d : CaseIComponentData T M Mc V) (K : Subgroup G) :
    d.normalizerMoved K ≤ K := by
  let H := K ⊔ d.normalizerSylow K
  let : (K.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer inf_le_right)
  have hm := map_mono (f := H.subtype)
    (commutator_le_right (d.normalizerModule K) (K.subgroupOf H))
  rw [map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left)] at hm
  exact hm

private theorem localFamily_witness_of_minimalParabolic (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K)
    (P : Sylow 2 (K ⊔ d.normalizerSylow K : Subgroup G))
    (hP : (P : Subgroup (K ⊔ d.normalizerSylow K : Subgroup G)).map
      (K ⊔ d.normalizerSylow K).subtype = d.normalizerSylow K)
    (hmin : IsMinimalParabolicOver P ⊤) :
    ∃ u ∈ d.normalizerMoved K, u ∈ thompsonAlpha d.S ∧ u ∉ centralizer (K : Set G) := by
  let := h.elementary
  let H := K ⊔ d.normalizerSylow K
  let U := d.normalizerModule K
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf
  let := a.reduced.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hsq := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
  have hsqK := (IsSQTK.equiv (subgroupOfEquivOfLe hK.1)).mp (hsq.subgroup (K.subgroupOf d.G1))
  obtain ⟨P0,hP0,_,hres,_,hmove⟩ :=
    d.localFamily_normalizer_seed_setup hG hempty hM hJ hu h hK hq hout hf
  have hPP : P0 = P := by
    apply Sylow.ext
    exact map_injective H.subtype_injective (hP0.trans hP.symm)
  subst P0
  obtain ⟨hqs,⟨c⟩⟩ := a.fitting_source_classification hsqK
  have hw := quasisimple_rankOne_fixed_noncentral P hmin U a.reduced hmove q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) hqs c
  let W := (⁅U,pResidual 2 H⁆ : Subgroup H)
  obtain ⟨u,huW,huc⟩ := SetLike.not_le_iff_exists.mp hw
  have hWP : W ≤ (P : Subgroup H) :=
    (commutator_le_left U _).trans (a.reduced.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal P))
  let : IsElementaryAbelian 2 (W ⊓ centralizer (elementaryAbelianMaxJ (P : Subgroup H) : Set H) : Subgroup H) :=
    IsElementaryAbelian.of_le (show W ⊓ centralizer (elementaryAbelianMaxJ (P : Subgroup H) : Set H) ≤ W from inf_le_left)
  have hua : u ∈ thompsonAlpha (P : Subgroup H) :=
    elementary_centralizer_maxJ_le_omegaCenter (P : Subgroup H) _
      (inf_le_left.trans hWP) inf_le_right huW
  have hJRS := (d.localFamily_normalizer_setup h hM.1.2 hu hK hq hout hf).2.1
  have hα : (thompsonAlpha (P : Subgroup H)).map H.subtype = thompsonAlpha d.S := by
    unfold thompsonAlpha
    rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
      ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP,hJRS]
  refine ⟨u,?_,hα ▸ mem_map_of_mem H.subtype hua,?_⟩
  · change (u : G) ∈ (⁅U,K.subgroupOf H⁆ : Subgroup H).map H.subtype
    rw [←hres]
    exact mem_map_of_mem H.subtype huW.1
  · intro hc
    apply huc
    intro k hk
    apply Subtype.ext
    exact hc k (show k ∈ K.subgroupOf H from hres ▸ hk)

/-- The original source image form retains H/C_H(⟨Z^H⟩) and its actual K-image. -/
theorem localFamily_rankOne_fixed_witness (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : d.normalizerImage K ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ u ∈ d.normalizerMoved K, u ∈ thompsonAlpha d.S ∧ u ∉ centralizer (K : Set G) := by
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf
  obtain ⟨⟨P,hP⟩,_,_⟩ := d.localFamily_normalizer_setup h hM.1.2 hu hK hq hout hf
  exact d.localFamily_witness_of_minimalParabolic hG hempty hM hJ hu h hK hq hout hf
    P hP (a.minimalParabolic_of_rankOne hq F e P hP)

/-- Every escaping rank-one local member has a noncentral J(S)-fixed
witness in its literal moved seed. Neither S-normality nor a block hypothesis
is imposed, and the quotient is the original K/O₂(K). -/
theorem localFamily_core_rankOne_fixed_witness (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ u ∈ d.normalizerMoved K, u ∈ thompsonAlpha d.S ∧ u ∉ centralizer (K : Set G) := by
  obtain ⟨⟨P,hP⟩,_,_⟩ := d.localFamily_normalizer_setup h hM.1.2 hu hK hq hout hf
  let H := K ⊔ d.normalizerSylow K
  let K0 := K.subgroupOf H
  let : K0.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer inf_le_right)
  let i : K0 ≃* K := subgroupOfEquivOfLe le_sup_left
  let e0 := (QuotientGroup.congr _ _ i (pCore_map_iso 2 i)).trans e
  let f := e0.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K0))
  have hfs : Function.Surjective f := e0.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfk : f.ker ≤ (frattini (K0 ⧸ pCore 2 K0)).comap (QuotientGroup.mk' (pCore 2 K0)) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e0.injective,QuotientGroup.ker_mk']
    intro x hx
    change QuotientGroup.mk' (pCore 2 K0) x ∈ frattini (K0 ⧸ pCore 2 K0)
    have hxq : QuotientGroup.mk' (pCore 2 K0) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hx
    rw [hxq]
    exact one_mem _
  have hgen : K0 ⊔ (P : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),hP,
      ←MonoidHom.range_eq_map,range_subtype]
  have hmin := minimal_over_normal_rankOne_frattini F K0 P hgen f hfs hfk
  exact d.localFamily_witness_of_minimalParabolic hG hempty hM hJ hu h hK hq hout hf
    P hP hmin

/-- The original nonblock implication reduces to separation of the literal
moved supports. The witness and all rank-one action, pair, and seed inputs
are discharged here. LocalSeparation proves the remaining premise using the
full B.5.6 action; C-component commutation modulo the two-core alone is not
used to infer separation. -/
theorem localFamily_nonblock_le_MZ_of_moved_separation (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : generalizedFitting K = pCore 2 K)
    (hsep : ∀ g ∈ d.S, K.map (MulAut.conj g).toMonoidHom ≠ K →
      (d.normalizerMoved K).map (MulAut.conj g).toMonoidHom ≤ centralizer (K : Set G))
    (hnot : ¬ IsChiBlock K)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) F) : K ≤ d.MZ := by
  by_contra hout
  obtain ⟨u,huW,hua,huc⟩ := d.localFamily_core_rankOne_fixed_witness
    hG hempty hM hJ hu h hK hq hout hf F e
  have hbaum : baumann d.S ≤ normalizer (K : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    by_contra hn
    have hfix : g*u*g⁻¹ = u := mul_inv_eq_iff_eq_mul.mpr (hg.2 u hua).symm
    have huim : u ∈ (d.normalizerMoved K).map (MulAut.conj g).toMonoidHom := by
      rw [←hfix]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom huW
    exact huc (hsep g hg.1 hn huim)
  exact hnot (d.localFamily_core_rankOne_chi_of_baumann_normalizes
    hG hempty hM hJ hu h hK hq hout hf hbaum F e)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
