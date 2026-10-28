module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.At.Geometry
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.Source

/-!
# The two residual calculations with inputs at the original G,T

These are pointwise versions of the accepted source proofs named below. The
structural and marked implications are used only at their displayed G,T.
The literal plane, residuals, quotient actions and relative normality are
preserved. The fixed branch uses the actual two-member elementary family;
the moving branch uses normal cubic residuals and its proved action.

Source: Aschbacher–Smith, 12.4.6, p.814, and C.1.34(5), pp.136–137.
-/

public section
open CFSG.Quasithin.Chapter12.Section02
/- Local form of SmallFusion/Setup.lean. -/
section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

namespace SLThreeExtension

variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

variable (E : SLThreeExtension D)

end SLThreeExtension

variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G}

theorem exists_slThree_fixed_involution_setup_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At K T)
    (earlier : Chapter1.Section02.UniquenessEarlierResults K)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    Nat.card (fixedSubgroup L V) = 2 ∧
    ∃ z : G, orderOf z = 2 ∧ fixedSubgroup L V = zpowers z ∧
      normalizer (L : Set G) = centralizer ({z} : Set G) ∧
      normalizer (L : Set G) = normalizer (V : Set G) ∧
      z ∈ omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) ∧
      centralizer (omegaOneAmbient ((center (T : Subgroup G)).map
        (T : Subgroup G).subtype) : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨E⟩ := marked L V h D hmodel hne
  have hc := E.fixed_card_eq_two hne
  exact ⟨hc, SLThreeSource.At.exists_fixed_involution_setup_of_card_two h D structural earlier hc⟩

end CFSG.Quasithin.Chapter12.Section04.SmallFusion

end

/- Local form of SmallFusion/SLThreeFusion.lean. -/
section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

theorem source_slThree_fusion_at
    {K : GroupClass.{u}} (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (marked : SLThreeSource.At.SLThreeAlternative1222At K T)
    (earlier : Chapter1.Section02.UniquenessEarlierResults K)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (v : G) (hvV : v ∈ V) (hv : v ∉ fixedSubgroup L V)
    (R : Subgroup G) (hRT : R ≤ T) (hindex : R.relIndex (T : Subgroup G) = 2)
    (hR : Chapter1.IsSylowIn 2 R (centralizer ({v} : Set G))) :
    ∃ z : G, orderOf z = 2 ∧ fixedSubgroup L V = zpowers z ∧
      centralizer ({z} : Set G) ≤ normalizer (V : Set G) ∧
      (∀ g : G, MulAut.conj g z ∈ V → MulAut.conj g z = z) ∧
      ∀ x ∈ V, ∀ y ∈ V, IsConj x y → ∃ l ∈ L, MulAut.conj l x = y := by
  obtain ⟨E⟩ := marked L V h D hmodel hne
  obtain ⟨z, hz, hzgen, hM, hMV, _, _⟩ :=
    SLThreeSource.At.exists_fixed_involution_setup_of_card_two h D structural earlier (E.fixed_card_eq_two hne)
  have hT : (T : Subgroup G) ≤ centralizer ({z} : Set G) :=
    (structural L h).1.trans hM.le
  have hf := slThree_fusion_of_sylow_centralizer E z hz hzgen hT v hvV hv R hRT hindex hR
  exact ⟨z, hz, hzgen, hM.symm.le.trans hMV.le, hf.1, hf.2⟩

end CFSG.Quasithin.Chapter12.Section04.SmallFusion

end

/- Local form of SmallFusion/NormalizerReduction.lean. -/
section
open Subgroup Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

theorem escaping_normalizer_four_group_at
    {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (marked : SLThreeSource.At.SLThreeAlternative1222At K T)
    (earlier : Chapter1.Section02.UniquenessEarlierResults K)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (E : Subgroup G) (hEV : E ≤ V) (hfour : Nat.card E = 4)
    (hsplit : omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)) =
      (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ⊔ V)
    (hfixed : omegaCenterIn (T : Subgroup G) ⊓ V = fixedSubgroup L V)
    (hplane : V ⊓ centralizer (((T : Subgroup G) ⊓ centralizer (E : Set G) : Subgroup G) : Set G) = E)
    (hindex : ((T : Subgroup G) ⊓ centralizer (E : Set G)).relIndex T = 2)
    (hescape : ¬ normalizer (((T : Subgroup G) ⊓ centralizer (E : Set G) : Subgroup G) : Set G) ≤
      normalizer (L : Set G)) :
    omegaCenterIn (T : Subgroup G) = fixedSubgroup L V ∧
    Nat.card (omegaCenterIn (T : Subgroup G)) = 2 ∧
    E = omegaCenterIn ((T : Subgroup G) ⊓ centralizer (E : Set G)) ∧
    normalizer (((T : Subgroup G) ⊓ centralizer (E : Set G) : Subgroup G) : Set G) ≤ normalizer (E : Set G) ∧
    ((normalizer (L : Set G)) ⊓ normalizer
      (((T : Subgroup G) ⊓ centralizer (E : Set G) : Subgroup G) : Set G)).relIndex
      (normalizer (((T : Subgroup G) ⊓ centralizer (E : Set G) : Subgroup G) : Set G)) = 3 := by
  let Z := omegaCenterIn (T : Subgroup G)
  let R := (T : Subgroup G) ⊓ centralizer (E : Set G)
  let N := normalizer (R : Set G)
  let M := normalizer (L : Set G)
  obtain ⟨hc,z,hz,hgen,hM,_,hzZ,_⟩ := exists_slThree_fixed_involution_setup_at
    h D structural marked earlier hmodel hne
  have hzZ' : z ∈ Z := by
    change z ∈ omegaCenterIn (T : Subgroup G)
    rwa [omegaCenterIn_eq_omegaOneAmbient]
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz
  have hzF : z ∈ fixedSubgroup L V := hgen ▸ mem_zpowers z
  have hZfacts := omega_center_of_fixed_supplement D E hEV hsplit
    (hfixed.le.trans inf_le_right) hplane
  have hZL : Z ≤ centralizer (L : Set G) := hZfacts.1
  have hRsplit : omegaCenterIn R = Z ⊔ E := hZfacts.2.2
  have hZC : Z ≤ centralizer ((T : Subgroup G) : Set G) :=
    fun x hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1
  have hzE : z ∈ E := hplane.le ⟨hzF.1, centralizer_le inf_le_left (hZC hzZ')⟩
  have hFZ : fixedSubgroup L V ≤ Z := by
    rw [hgen]
    exact zpowers_le_of_mem hzZ'
  have hFE : fixedSubgroup L V ≤ E := by
    rw [hgen]
    exact zpowers_le_of_mem hzE
  have hZE : Z ⊓ E = fixedSubgroup L V := le_antisymm
    ((inf_le_inf_left _ hEV).trans hfixed.le) (le_inf hFZ hFE)
  have hZnorm : E ≤ normalizer (Z : Set G) :=
    (le_centralizer_iff.mp (hZC.trans (centralizer_le (hEV.trans D.le_sylow)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcard := card_mul_eq_card_inf_mul_card_sup_of_normalizes Z E hZnorm
  rw [hZE,hfour,hc] at hcard
  have hmult : Nat.card (Z ⊔ E : Subgroup G) = Nat.card Z * 2 := by omega
  have hhyper : Z.relIndex (omegaCenterIn R) = 2 := by
    rw [hRsplit]
    have ht := relIndex_mul_relIndex (⊥ : Subgroup G) Z (Z ⊔ E) bot_le le_sup_left
    rw [relIndex_bot_left, relIndex_bot_left, hmult] at ht
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos ht
  have hZne : Z ≠ ⊥ := fun he => hz1 (show z ∈ (⊥ : Subgroup G) from he ▸ hzZ')
  have hNomega := normalizer_le_normalizer_omegaCenterIn R
  obtain ⟨g,hgN,hgM⟩ := SetLike.not_le_iff_exists.mp hescape
  have horbit : componentOrbit L (T : Subgroup G) = L := by
    apply le_antisymm _ (le_componentOrbit L _)
    exact iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl
      (structural L h).1
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_earlier earlier
    h.simpleQTKE T h.maximal_faithful.1
  have hd : Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥ := by
    have hh := hu.centralizer_intersection g (by simpa only [horbit] using hgM)
    change (Z ⊓ centralizer (componentOrbit L (T : Subgroup G) : Set G)) ⊓
      (Z ⊓ centralizer (componentOrbit L (T : Subgroup G) : Set G)).map
        (MulAut.conj g).toMonoidHom = ⊥ at hh
    rw [horbit, inf_eq_left.mpr hZL] at hh
    exact hh
  have hZle : Z ≤ omegaCenterIn R := hRsplit.symm ▸ le_sup_left
  obtain ⟨hZcard,hRcard⟩ := card_eq_two_of_disjoint_conjugate_hyperplane
    Z (omegaCenterIn R) hZle hZne hhyper g (hNomega hgN) hd
  have hZF : Z = fixedSubgroup L V := (eq_of_le_of_card_ge hFZ (by rw [hZcard,hc])).symm
  have hEeq : E = omegaCenterIn R := eq_of_le_of_card_ge
    (hRsplit.symm ▸ le_sup_right) (by rw [hfour,hRcard])
  have hNE : N ≤ normalizer (E : Set G) := by rw [hEeq]; exact hNomega
  have hTN : (T : Subgroup G) ≤ N := by
    let : (R.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hindex
    exact le_normalizer_of_normal_subgroupOf (show R ≤ (T : Subgroup G) from inf_le_left)
  have hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G) :=
    (structural L h).1.trans hM.le
  have hi := centralizer_relIndex_eq_three_of_four T N E hTN hNE hfour z hzE hz1 hTz
    (by simpa only [← hM] using hescape)
  refine ⟨hZF,hZcard,hEeq,hNE,?_⟩
  simpa only [← hM, inf_comm] using hi

theorem characteristic_eq_bot_of_normal_in_LR_at
    {K : GroupClass.{u}} {T : Sylow 2 G} {L : Subgroup G}
    (h : Hypothesis1223 K T L) (structural : Structural1222At K T)
    (earlier : Chapter1.Section02.UniquenessEarlierResults K)
    (R : Subgroup G) (hRT : R ≤ T) (hindex : R.relIndex T = 2)
    (hescape : ¬ normalizer (R : Set G) ≤ normalizer (L : Set G))
    (C : Subgroup R) [C.Characteristic]
    (hCnormal : ((C.map R.subtype).subgroupOf (L ⊔ R)).Normal) : C = ⊥ := by
  by_contra hC
  have horbit : componentOrbit L (T : Subgroup G) = L := by
    apply le_antisymm _ (le_componentOrbit L _)
    exact iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl
      (structural L h).1
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_earlier earlier
    h.simpleQTKE T h.maximal_faithful.1
  have hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = normalizer (L : Set G) := by
    intro N hN hLN
    simpa only [horbit] using hu.normalizer_unique N hN hLN
  have hN := normalizer_le_normalizer_characteristic_image R C
  have hTN : (T : Subgroup G) ≤ normalizer (R : Set G) := by
    let : (R.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hindex
    exact le_normalizer_of_normal_subgroupOf hRT
  let := hCnormal
  have hLN : L ⊔ R ≤ normalizer (C.map R.subtype : Set G) :=
    le_normalizer_of_normal_subgroupOf ((map_subtype_le C).trans le_sup_right)
  have hRp : IsPGroup 2 R := T.isPGroup'.of_injective
    (inclusion hRT) (inclusion_injective _)
  have hCN := normalizer_le_of_unique_maximalTwoLocal hunique
    ((hRp.to_subgroup C).map R.subtype)
    (fun he => hC ((C.map_eq_bot_iff_of_injective R.subtype_injective).mp he))
    (sup_le (le_sup_left.trans hLN) (hTN.trans hN))
  exact hescape (hN.trans hCN)

end CFSG.Quasithin.Chapter12.Section04.SmallFusion

end

/- Local form of SLThreeCommutatorSource/NormalizerAction.lean. -/
section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource

open Section02 SmallFusion

universe u

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

theorem normalizerAction_of_structural_marked_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    ∀ n ∈ normalizer (V : Set G), ∃ l ∈ L, ∀ v ∈ V,
      MulAut.conj n v = MulAut.conj l v := by
  intro n hn
  obtain ⟨E⟩ := marked L V h D hmodel hne
  obtain ⟨z, _, _, _, hnorm, _, _⟩ := SLThreeSource.At.exists_fixed_involution_setup_of_card_two h D structural
    SLThreeSource.uniquenessEarlier_knownSimple (E.fixed_card_eq_two hne)
  exact same_action_of_common_normalizer E n hn (by rwa [hnorm])

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource

end

/- Local form of SmallFusion/SLThreeSource/Geometry.lean. -/
section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

namespace LocalGeometry

variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}
  (d : LocalGeometry D)

theorem escape_geometry_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    omegaCenterIn (T : Subgroup G) = fixedSubgroup L V ∧
    Nat.card (omegaCenterIn (T : Subgroup G)) = 2 ∧
    d.E = omegaCenterIn d.R ∧
    normalizer (d.R : Set G) ≤ normalizer (d.E : Set G) ∧
    (normalizer (L : Set G) ⊓ normalizer (d.R : Set G)).relIndex
      (normalizer (d.R : Set G)) = 3 :=
  escaping_normalizer_four_group_at h D structural marked uniquenessEarlier_knownSimple
    hmodel hne d.E d.le_module d.card_plane d.fixed_supplement
    (d.fixed_line_at h structural (Classical.choice (marked L V h D hmodel hne)) hne)
    d.fixed_plane d.index hescape

end LocalGeometry

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

end

/- Local form of SmallFusion/SLThreeSource/FixedBlockSpecializationSetup.lean. -/
section
open Subgroup Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Section02

open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

universe u

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

namespace LocalGeometry

variable (d : LocalGeometry D)

theorem ms_characteristic_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    MSNoCharacteristicNormal L d.R := by
  intro C hc hn
  let := hc
  exact characteristic_eq_bot_of_normal_in_LR_at h structural
    uniquenessEarlier_knownSimple d.R inf_le_left d.index hescape C hn

end LocalGeometry

theorem smallMSPair_of_oddIndex_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (ext : SLThreeExtension D) (d : LocalGeometry D)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hradical : MSOddIndex L d.R) : SmallMSPair KnownSimple.IsKnownSimple L d.R := by
  have hTV := ((structural L h).2.2 V D).1
  exact ⟨inferInstance, d.ms_sqtk ext h hTV,
    generalizedFitting_eq_pCore_of_selfCentralizing 2 (d.ms_characteristicTwo ext h hTV),
    d.ms_product, d.ms_component h, ms_rankTwo ext, hradical,
    d.ms_characteristic_at h structural hescape⟩

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

end

/- Local form of SmallFusion/SLThreeSource/MovingResidualConstructionBase.lean. -/
section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

namespace LocalGeometry

variable (d : LocalGeometry D)

theorem plane_centralizer_le_normalizer_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    centralizer (d.E : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨hZ, _, _, _, _⟩ := d.escape_geometry_at h structural marked hmodel hne hescape
  obtain ⟨_, z, _, hgen, hM, _, _, _⟩ := exists_slThree_fixed_involution_setup_at
    h D structural marked uniquenessEarlier_knownSimple hmodel hne
  have hFE : fixedSubgroup L V ≤ d.E := by
    rw [← d.fixed_plane]
    rw [← hZ]
    exact le_inf (hZ ▸ (show fixedSubgroup L V ≤ V from inf_le_left))
      (fun x hx => centralizer_le (show d.R ≤ T from inf_le_left)
        ((mem_omegaCenterIn_iff _ _).mp hx).2.1)
  rw [hM]
  exact centralizer_le (Set.singleton_subset_iff.mpr (hFE (hgen ▸ mem_zpowers z)))

theorem moving_overgroup_characteristicTwo_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (X : Subgroup G) (hXM : X ≤ normalizer (L : Set G)) :
    HasCharacteristicTwo (X ⊔ (L ⊔ (T : Subgroup G)) : Subgroup G) := by
  let M := normalizer (L : Set G)
  let J := X ⊔ (L ⊔ (T : Subgroup G))
  have hTM := (structural L h).1
  have he : componentOrbit L (T : Subgroup G) = L := by
    apply le_antisymm _ (le_componentOrbit _ _)
    exact iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTM
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_earlier
    uniquenessEarlier_knownSimple h.simpleQTKE T h.maximal_faithful.1
  have hm : IsMaximalTwoLocal M := by simpa only [he] using hu.normalizer_maximal
  have hc := h.simpleQTKE.evenCharacteristic T M hm hTM
  have hJM : J ≤ M := sup_le hXM (sup_le L.le_normalizer hTM)
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right.trans le_sup_right
  have hrel := centralizer_pCore_le_of_sylow_le (T.subtype hTM) (J.subgroupOf M)
    (fun t ht => hTJ ht) hc
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hJM)).mp hrel

end LocalGeometry

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

end

/- Local form of SmallFusion/SLThreeSource/MovingResidualConstructionCubic.lean. -/
section
open Subgroup Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

namespace LocalGeometry

variable (d : LocalGeometry D)

theorem fixed_le_plane_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    fixedSubgroup L V ≤ d.E := by
  obtain ⟨hZ, _, _, _, _⟩ := d.escape_geometry_at h structural marked hmodel hne hescape
  rw [← d.fixed_plane]
  apply le_inf inf_le_left
  change fixedSubgroup L V ≤ centralizer (d.R : Set G)
  rw [← hZ]
  exact fun x hx => centralizer_le (show d.R ≤ T from inf_le_left)
    ((mem_omegaCenterIn_iff _ _).mp hx).2.1

end LocalGeometry

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

end

/- Local form of SmallFusion/SLThreeSource/FixedBlockSpecializationRadical.lean. -/
section
open Subgroup Theory.GroupTheory

open scoped IsMulCommutative Pointwise

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Section02

open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

universe u

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

namespace LocalGeometry

variable (d : LocalGeometry D)

private theorem radical_quotient_map_at (ext : SLThreeExtension D)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    ∃ q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Matrix.PSL3Two.SL,
      Function.Surjective q ∧ q.ker = pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
  let H := L ⊔ (T : Subgroup G)
  have hcover : (H : Set G) ⊆ (L : Set G) * (H.pCoreIn 2 : Set G) := by
    intro g hg
    let : ((H.pCoreIn 2).subgroupOf H).Normal :=
      normal_subgroupOf_of_le_normalizer (H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
    have hm : (⟨g,hg⟩ : H) ∈ L.subgroupOf H ⊔ (H.pCoreIn 2).subgroupOf H := by
      rw [← subgroupOf_sup le_sup_left (pCoreIn_le 2 H),
        ← join_eq_component_sup_core D ext hTV, subgroupOf_self]
      trivial
    obtain ⟨l,hl,k,hk,he⟩ := mem_sup_of_normal_right.mp hm
    exact ⟨l,hl,k,hk,congrArg Subtype.val he⟩
  obtain ⟨e,_⟩ := exists_pCoreQuotientEquiv_of_cover (p := 2)
    (show L ≤ H from le_sup_left) hcover
  let a := e.symm.trans ext.quotientEquiv
  let q := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  refine ⟨q,a.surjective.comp (QuotientGroup.mk'_surjective _),?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ a.injective,QuotientGroup.ker_mk']

theorem radical_normalizer_core_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    ((L ⊔ (T : Subgroup G)) ⊓ normalizer (d.E : Set G)).pCoreIn 2 = d.R := by
  obtain ⟨ext⟩ := marked L V h D hmodel hne
  have hTV := ((structural L h).2.2 V D).1
  have hFE := d.fixed_le_plane_at h structural marked hmodel hne hescape
  have hTE := d.sylow_normalizes.trans
    (d.escape_geometry_at h structural marked hmodel hne hescape).2.2.2.1
  let H := L ⊔ (T : Subgroup G)
  let A := (normalizer (d.E : Set G)).subgroupOf H
  let C := (centralizer (d.E : Set G)).subgroupOf H
  obtain ⟨q,hq,hk⟩ := radical_quotient_map_at ext hTV
  have hkC : q.ker ≤ C := by
    intro x hx
    rw [hk] at hx
    have hxQ : (x : G) ∈ H.pCoreIn 2 := mem_map_of_mem H.subtype hx
    exact centralizer_le d.le_module (D.core_centralizes hxQ)
  have hcalc := Matrix.PSL3Two.core_of_index_seven_cover q hq (by rw [hk]; exact pCore_isPGroup)
    (T.subtype (show T ≤ H from le_sup_right)) A C (d.R.subgroupOf H)
    hkC (fun _ hx => Subgroup.centralizer_le_normalizer _ hx) (fun _ hx => hTE hx)
    (d.radical_normalizer_index ext hne hTV hFE hTE)
    (d.radical_centralizer_index ext hne hTV hFE)
    (by ext x; rfl)
    (by
      rw [Sylow.coe_subtype,
        relIndex_subgroupOf (show (T : Subgroup G) ≤ H from le_sup_right)]
      exact d.index)
  have hm := congrArg (fun B : Subgroup H => B.map H.subtype) hcalc
  rw [map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
    map_subgroupOf_eq_of_le (show d.R ≤ H from inf_le_left.trans le_sup_right)] at hm
  simpa only [A,subgroupOf_map_subtype,inf_comm] using hm

theorem ms_oddIndex_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    MSOddIndex L d.R := by
  obtain ⟨ext⟩ := marked L V h D hmodel hne
  have hTV := ((structural L h).2.2 V D).1
  have hFE := d.fixed_le_plane_at h structural marked hmodel hne hescape
  have hTE := d.sylow_normalizes.trans
    (d.escape_geometry_at h structural marked hmodel hne hescape).2.2.2.1
  have hi := d.radical_normalizer_index ext hne hTV hFE hTE
  let A := (L ⊔ (T : Subgroup G)) ⊓ normalizer (d.E : Set G)
  have hAi : A.relIndex (L ⊔ (T : Subgroup G)) = 7 := by
    rw [inf_relIndex_left]
    exact hi
  refine ⟨A,?_,?_,d.radical_normalizer_core_at h structural marked hmodel hne hescape⟩
  · rw [d.ms_join_eq ext h hTV]
    apply lt_iff_le_not_ge.mpr
    refine ⟨inf_le_left,?_⟩
    intro hle
    have hi1 : A.relIndex (L ⊔ (T : Subgroup G)) = 1 := relIndex_eq_one.mpr hle
    omega
  · change Odd (A.relIndex (L ⊔ d.R))
    rw [d.ms_join_eq ext h hTV,hAi]
    decide

theorem smallMSPair_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.SmallMSPair
      KnownSimple.IsKnownSimple L d.R := by
  obtain ⟨ext⟩ := marked L V h D hmodel hne
  exact smallMSPair_of_oddIndex_at h structural ext d hescape
    (d.ms_oddIndex_at h structural marked hmodel hne hescape)

end LocalGeometry

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

end

/- Local form of SmallFusion/SLThreeSource/FixedBlockSpecializationComparison.lean. -/
section
open Subgroup Theory.GroupTheory Representation

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Section02

open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

universe u

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

omit [Finite G] in

private theorem section_card_at {A W : Type*} [Group A] [AddCommGroup W]
    [Module (ZMod 2) W] {Q C : Subgroup G} {a : L →* A}
    {rho : Representation (ZMod 2) A W} (h : HasSectionModel L Q C a rho) :
    Nat.card Q = Nat.card W * Nat.card C := by
  obtain ⟨hCQ, _, _, hn, e, _⟩ := h
  rw [card_eq_card_quotient_mul_card_subgroup (C.subgroupOf Q),
    Nat.card_congr e.toEquiv, Nat.card_congr (subgroupOfEquivOfLe hCQ).toEquiv]
  rfl

omit [Finite G] in

private theorem section_fixed_eq_bot_at {A W : Type*} [Group A] [AddCommGroup W]
    [Module (ZMod 2) W] {Q : Subgroup G} {a : L →* A}
    {rho : Representation (ZMod 2) A W} (ha : Function.Surjective a)
    (hf : OneCohomology.fixed rho = ⊥)
    (h : HasSectionModel L Q ⊥ a rho) : Q ⊓ centralizer (L : Set G) = ⊥ := by
  obtain ⟨_, _, _, hn, e, he⟩ := h
  apply bot_unique
  intro x hx
  let q : Q := ⟨x, hx.1⟩
  have hfix : (e (QuotientGroup.mk' _ q)).toAdd ∈ OneCohomology.fixed rho := by
    intro g
    obtain ⟨l,rfl⟩ := ha g
    exact (he l q q (mul_inv_eq_iff_eq_mul.mpr (hx.2 l l.property)).symm).symm
  rw [hf] at hfix
  have heq : e (QuotientGroup.mk' _ q) = 1 :=
    Multiplicative.toAdd.injective hfix
  have hq : q ∈ (⊥ : Subgroup G).subgroupOf Q :=
    (QuotientGroup.eq_one_iff q).mp (e.map_eq_one_iff.mp heq)
  exact hq

private theorem natural_pair_fixed_at :
    OneCohomology.fixed ((specialLinearNatural (k := ZMod 2) 3).prod
      (specialLinearNatural (k := ZMod 2) 3)) = ⊥ := by
  apply bot_unique
  intro v hv
  have h₁ : v.1 ∈ OneCohomology.fixed (specialLinearNatural (k := ZMod 2) 3) :=
    fun g => congrArg Prod.fst (hv g)
  have h₂ : v.2 ∈ OneCohomology.fixed (specialLinearNatural (k := ZMod 2) 3) :=
    fun g => congrArg Prod.snd (hv g)
  rw [OneCohomology.SLHigherNatural.fixed_eq_bot (by decide : 2 ≤ 3)] at h₁ h₂
  exact Prod.ext h₁ h₂

namespace LocalGeometry

variable (d : LocalGeometry D)

theorem ms_fixed_alternative_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (halt : MSModuleAlternatives L d.R T 1 (ZMod 2) e) :
    FixedMSAlternative L d.R T e ∧ msQ L d.R = V := by
  obtain ⟨ext⟩ := marked L V h D hmodel hne
  have hTV := ((structural L h).2.2 V D).1
  have hVc := module_card_sixteen ext hne
  have hVQ := d.module_le_msQ ext h hTV
  have hVZ := d.module_le_ms_center ext h hTV
  have ha : Function.Surjective (linearThreeActor e) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hq : msQ L d.R ≤ (L ⊔ d.R).pCoreIn 2 :=
    le_normalizer_iff_commutator_le_left.mp
      (le_sup_left.trans ((L ⊔ d.R).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (L ⊔ d.R) (pCore 2 _))))
  have hQT : msQ L d.R ≤ (T : Subgroup G) := by
    rw [d.ms_core_eq ext h hTV] at hq
    exact hq.trans inf_le_left
  have hlast : FixedMSAlternative L d.R T e := by
    rcases halt with h₁ | h₂ | h₃ | h₄ | h₅
    · have hc := section_card_at h₁.2.2
      have hv := card_le_of_le hVQ
      simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin, card_bot, mul_one] at hc
      rw [hVc, hc] at hv
      norm_num at hv
    · have hz := section_fixed_eq_bot_at ha natural_pair_fixed_at h₂.1
      apply (hne (bot_unique ?_)).elim
      exact (inf_le_inf_right _ hVQ).trans hz.le
    · have hc := section_card_at h₃.1
      have hv := card_le_of_le hVZ
      simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin, card_bot, mul_one] at hc
      rw [hVc, hc] at hv
      norm_num at hv
    · let C := msQ L d.R ⊓ centralizer (L : Set G)
      let _ : IsElementaryAbelian 2 C := h₄.1
      have hCZ : C ≤ Subgroup.omegaCenterIn (T : Subgroup G) := by
        intro x hx
        refine (mem_omegaCenterIn_iff _ _).mpr
          ⟨hQT hx.1, ?_, elemPow_eq_one_of_isElementaryAbelian x hx⟩
        intro t ht
        obtain ⟨z,hz,he⟩ := h₄.2.2.1 hx
        have htJ : t ∈ L ⊔ d.R := by
          rw [d.ms_join_eq ext h hTV]
          exact mem_sup_right ht
        have hc := congrArg Subtype.val (mem_center_iff.mp hz ⟨t,htJ⟩)
        change (z : G) = x at he
        change t * (z : G) = (z : G) * t at hc
        exact he ▸ hc
      have hc := card_le_of_le hCZ
      have hz := (d.escape_geometry_at h structural marked hmodel hne hescape).2.1
      rw [h₄.2.1, hz] at hc
      norm_num at hc
    · exact h₅
  refine ⟨hlast, eq_of_le_of_card_ge hVQ ?_ |>.symm⟩
  have hc := section_card_at hlast.2.2.1
  obtain ⟨eC⟩ := hlast.2.1
  have hC : Nat.card (msQ L d.R ⊓ centralizer (L : Set G) : Subgroup G) = 2 :=
    (Nat.card_congr eC.toEquiv).trans (Nat.card_zmod 2)
  rw [hc, Nat.card_fun, Nat.card_zmod, Nat.card_fin, hC, hVc]
  norm_num

end LocalGeometry

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

end

/- Local form of SmallFusion/SLThreeSource/FixedBlockMSIndependent.lean. -/
section
open Subgroup Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Section02 ChapterC

open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
local notation "msCenter" =>
  CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in

private theorem natural_section_order_at {K U : Subgroup G}
    (a : K →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (h : HasSectionModel K U ⊥ a
      (Representation.specialLinearNatural (k := ZMod 2) 3)) : Nat.card U = 8 := by
  obtain ⟨_,_,_,hn,e,_⟩ := h
  let := hn
  let b := (QuotientGroup.quotientMulEquivOfEq (bot_subgroupOf U)).trans
    (QuotientGroup.quotientBot (G := U))
  have hc := Nat.card_congr (b.symm.trans e).toEquiv
  change Nat.card U = Nat.card (Fin 3 → ZMod 2) at hc
  norm_num only [Nat.card_fun,Nat.card_zmod,Nat.card_fin] at hc
  exact hc

private theorem no_large_distance_of_central_four_space_at {K R W : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple K R)
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (common : BinaryMS.MS93.CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical)
    (hcard : Nat.card W = 16) (hWZ : W ≤ msCenter (msQ K R))
    (hm : W = ⁅W,K⁆) : False := by
  let A := K ⊔ R
  let U := ⁅msCenter (msQ K R),K⁆
  have hZA : msCenter (msQ K R) ≤ A :=
    (map_subtype_le (center (msQ K R))).trans (msQ_le_join K R)
  have hUA : U ≤ A := (@Subgroup.commutator_le_sup G _ _ _).trans
    (sup_le hZA le_sup_left)
  have hWA : W ≤ A := hWZ.trans hZA
  have hWU : W ≤ U := hm.le.trans (commutator_mono hWZ le_rfl)
  have hUsub : ⁅msCenter (msQ (K.subgroupOf A) (R.subgroupOf A)),K.subgroupOf A⁆ =
      U.subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [map_commutator,msQ_subgroupOf le_sup_left le_sup_right,
      centerIn_subgroupOf (msQ_le_join K R),map_subgroupOf_eq_of_le hZA,
      map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le hUA]
  obtain ⟨_,_,_,hU⟩ := t.center_source_sections common hb
  rw [hUsub] at hU
  have h8 : Nat.card (U.subgroupOf A) = 8 := natural_section_order_at _ hU
  have h16 : Nat.card (W.subgroupOf A) = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hWA).toEquiv).trans hcard
  have hle := Nat.card_le_card_of_injective
    (inclusion (show W.subgroupOf A ≤ U.subgroupOf A from comap_mono hWU))
    (inclusion_injective _)
  omega

variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

namespace LocalGeometry

variable (d : LocalGeometry D)

theorem ms_core_commutative_without_binary_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    IsMulCommutative (msQ L d.R) := by
  obtain ⟨ext⟩ := marked L V h D hmodel hne
  have hTV := ((structural L h).2.2 V D).1
  have hMS := d.smallMSPair_at h structural marked hmodel hne hescape
  have hVZ := d.module_le_ms_center ext h hTV
  have hV16 := module_card_sixteen ext hne
  by_contra hc
  have hc' : ¬ IsMulCommutative
      (BinaryMS.commutatorCore (L.subgroupOf (L ⊔ d.R))) := by
    intro hh
    apply hc
    apply isMulCommutative_iff.mpr
    intro x y
    apply (binaryCoreEquiv L d.R).symm.injective
    simpa only [map_mul] using isMulCommutative_iff.mp hh
      ((binaryCoreEquiv L d.R).symm x) ((binaryCoreEquiv L d.R).symm y)
  obtain ⟨t⟩ := BinaryMS.MS93.exists_setup (hMS.binaryInput ext.quotientEquiv) hc'
  obtain ⟨common⟩ := t.commonFacts hc'
  by_cases hb : t.geometry.b t.reduction.radical = 4
  · obtain ⟨e,hZ,_⟩ := hMS.distance_four_source_sections ext.quotientEquiv t common hb
    have h8 : Nat.card (msCenter (msQ L d.R)) = 8 := natural_section_order_at _ hZ
    have hle := card_le_of_le hVZ
    omega
  have hlarge : 4 < t.geometry.b t.reduction.radical := by
    have he := t.geometry.even (BinaryMS.MS93.alpha t.reduction.radical) rfl
    change Even (t.geometry.b t.reduction.radical) at he
    obtain ⟨n,hn⟩ := he
    have hl := common.large_distance
    omega
  exact no_large_distance_of_central_four_space_at hMS ext.quotientEquiv t common hlarge
    hV16 hVZ D.eq_commutator

theorem ms_specialization_without_binary_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      FixedMSAlternative L d.R T e ∧ msQ L d.R = V ∧ ChapterC.IsLinearTwoBlock L 3 := by
  obtain ⟨ext⟩ := marked L V h D hmodel hne
  have hTV := ((structural L h).2.2 V D).1
  have hMS := d.smallMSPair_at h structural marked hmodel hne hescape
  have hc := d.ms_core_commutative_without_binary_at h structural marked hmodel hne hescape
  obtain ⟨e,he⟩ := hMS.abelian_source ext.quotientEquiv hc T
    (d.ms_sylow ext h hTV) inf_le_left
  obtain ⟨hcase,hQ⟩ := d.ms_fixed_alternative_at h structural marked hmodel hne hescape e he
  exact ⟨e,hcase,hQ,d.ms_isLinearTwoBlock h ext hmodel e hcase hQ⟩

end LocalGeometry

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

end

/- Local form of SmallFusion/SLThreeSource/FixedBlockSpecializationProductsKernel.lean. -/
section
open Subgroup Theory.GroupTheory Representation

open scoped IsMulCommutative commutatorElement Pointwise

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Section02 ChapterC

open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

universe u

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

namespace LocalGeometry

variable (d : LocalGeometry D)

theorem ms_module_not_le_radical_commutator_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (ext : SLThreeExtension D)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) (hQ : msQ L d.R = V) :
    ¬ V ≤ ⁅d.R,d.R⁆ := by
  intro hVF
  have hFL : ⁅L,⁅d.R,d.R⁆⁆ ≤ ⁅d.R,d.R⁆ := by
    have hFQ := d.ms_radical_commutator_le_core h ext hTV e hcase
    have hh : ⁅(T : Subgroup G) ⊓ centralizer (V : Set G),L⁆ = V := by
      rw [← d.ms_core_eq ext h hTV]
      exact hQ
    rw [commutator_comm] at hh
    exact ((commutator_mono le_rfl hFQ).trans hh.le).trans hVF
  have hnorm : L ⊔ d.R ≤ normalizer ((⁅d.R,d.R⁆ : Subgroup G) : Set G) := sup_le
    (le_normalizer_iff_commutator_le_right.mpr hFL)
    (by
      rw [← d.R.map_subtype_commutator]
      exact d.R.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image d.R (_root_.commutator d.R)))
  have hf := d.ms_characteristic_at h structural hescape (_root_.commutator d.R)
    inferInstance (by
      rw [d.R.map_subtype_commutator]
      exact normal_subgroupOf_of_le_normalizer hnorm)
  have hbot : ⁅d.R,d.R⁆ = ⊥ := by rw [← d.R.map_subtype_commutator,hf,Subgroup.map_bot]
  have hVbot : V = ⊥ := le_bot_iff.mp (hbot ▸ hVF)
  exact hne (le_bot_iff.mp (inf_le_left.trans hVbot.le))

theorem ms_core_centralization_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) (hQ : msQ L d.R = V) :
    L.pCoreIn 2 ≤ centralizer
      (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := by
  obtain ⟨ext⟩ := marked L V h D hmodel hne
  have hTV := ((structural L h).2.2 V D).1
  let _ := D.elementary
  let P := L.pCoreIn 2
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  let A := L ⊓ d.R
  have hQR : Q ≤ d.R := inf_le_inf_left _ (centralizer_le d.le_module)
  have hVR : V ≤ d.R := le_inf D.le_sylow
    (V.le_centralizer.trans (centralizer_le d.le_module))
  have hcomm : ⁅L,Q⁆ = V := by
    change ⁅L,(T : Subgroup G) ⊓ centralizer (V : Set G)⁆ = V
    rw [commutator_comm,← d.ms_core_eq ext h hTV]
    exact hQ
  have hplane : ⁅A,V⁆ = d.E :=
    d.ms_component_radical_commutator_plane h ext hTV hne e hcase hQ
  have hEF : d.E ≤ ⁅d.R,d.R⁆ := by
    rw [← hplane]
    exact commutator_mono inf_le_right hVR
  have hFE := d.fixed_le_plane_at h structural marked hmodel hne hescape
  have hkernel := d.ms_kernel_commutator_le_fixed h ext hTV hQ
  apply le_centralizer_iff.mp
  intro q hq
  by_contra hn
  have hPq : ¬ P ≤ centralizer ({q} : Set G) := by
    intro hc
    apply hn
    intro p hp
    exact mem_centralizer_singleton_iff.mp (hc hp)
  have hVq : V ≤ centralizer ({q} : Set G) := by
    intro v hv
    exact mem_centralizer_singleton_iff.mpr (hq.2 v hv)
  have hc : P ⊓ centralizer ({q} : Set G) = V :=
    centralizer_inter_eq_of_card_le_twice P V D.le_componentCore q hVq hPq
      (by rw [module_card_sixteen ext hne]; exact d.ms_core_card_le_thirtyTwo h ext hne e hQ)
  have hker : ∀ a ∈ A, ⁅a,q⁆ ∈ d.E ↔ a ∈ P := by
    intro a ha
    constructor
    · intro hdelta
      by_contra haP
      have hs : a ^ 2 ∈ P := d.ms_component_radical_square h ext hTV e hcase a ha.1 ha.2
      have hsn : a ^ 2 ∉ V := by
        intro hsv
        have he := d.ms_core_eq_module_of_square_mem h e hQ a ha.1 haP hsv
        apply hPq
        change L.pCoreIn 2 ≤ _
        rw [he]
        exact hVq
      have hh : ⁅a ^ 2,q⁆ = 1 := by
        rw [pow_two,commutatorElement_mul_left_eq_conj_mul,
          (ha.2.2 _ hdelta).symm,mul_inv_cancel_right,← pow_two]
        exact elemPow_eq_one_of_isElementaryAbelian _ (d.le_module hdelta)
      have hm : a ^ 2 ∈ P ⊓ centralizer ({q} : Set G) :=
        ⟨hs,mem_centralizer_singleton_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mp hh)⟩
      exact hsn (hc ▸ hm)
    · intro haP
      exact hFE (hkernel (commutator_mem_commutator haP hq))
  have hVF : V ≤ ⁅d.R,d.R⁆ := le_self_commutator_of_four_plane_displacement
    A P V d.E d.R hplane.le d.le_module hEF inf_le_right
    (module_card_sixteen ext hne) d.card_plane
    (d.ms_component_radical_index h ext hTV e hcase) q (hQR hq)
    (fun a ha => hcomm ▸ commutator_mem_commutator ha.1 hq) hker
  exact d.ms_module_not_le_radical_commutator_at h ext structural hTV hne hescape e hcase hQ hVF

theorem ms_core_product_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) (hQ : msQ L d.R = V) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  obtain ⟨ext⟩ := marked L V h D hmodel hne
  exact d.ms_core_product_of_core_centralization h ext
    ((structural L h).2.2 V D).1 hne hQ
    (d.ms_core_centralization_at h structural marked hmodel hne hescape e hcase hQ)

end LocalGeometry

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

end

/- Local form of SmallFusion/SLThreeSource/FixedBlockSpecializationProductsResidual.lean. -/
section
open Subgroup Theory.GroupTheory Representation

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

namespace LocalGeometry

variable (d : LocalGeometry D)

end LocalGeometry

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Subgroup Theory.GroupTheory Representation Section02

open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

namespace LocalGeometry

variable (d : LocalGeometry D)

end LocalGeometry

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Subgroup Theory.GroupTheory Representation Section02

universe u

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

namespace LocalGeometry

variable (d : LocalGeometry D)

theorem ms_residual_action_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    d.R ⊓ centralizer (d.L₁ : Set G) ≤ centralizer (V : Set G) ∧
      V ⊓ centralizer (d.L₁ : Set G) = d.E := by
  obtain ⟨ext⟩ := marked L V h D hmodel hne
  have hFE := d.fixed_le_plane_at h structural marked hmodel hne hescape
  exact ⟨d.residual_centralizer_le_module_centralizer ext hne hFE
    ((structural L h).2.2 V D).1 (structural L h).1,
    d.module_inf_lineResidual_centralizer ext hne hFE⟩

theorem ms_residual_centralizer_product_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hproduct : (T : Subgroup G) ⊓ centralizer (V : Set G) =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G))) :
    d.R ⊓ centralizer (d.L₁ : Set G) =
      d.E ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  obtain ⟨himage, hfixed⟩ := d.ms_residual_action_at h structural marked hmodel hne hescape
  exact d.ms_residual_centralizer_of_geometry hproduct himage hfixed

end LocalGeometry

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

end

/- Local form of SmallFusion/SLThreeSource/FixedBlockSpecializationProducts.lean. -/
section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Section02

open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

universe u

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

namespace LocalGeometry

variable (d : LocalGeometry D)

theorem ms_fixedBlockIdentities_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcase : FixedMSAlternative L d.R T e) (hQ : msQ L d.R = V) :
    FixedBlockIdentities d := by
  have hproduct := d.ms_core_product_at h structural marked hmodel hne hescape e hcase hQ
  exact ⟨hproduct,
    d.ms_residual_centralizer_product_at h structural marked hmodel hne hescape hproduct⟩

end LocalGeometry

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

end

/- Local form of SmallFusion/SLThreeSource/FixedBlock.lean. -/
section
open Subgroup Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

theorem fixedBlock_frattini_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) (d : LocalGeometry D)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hline : normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G))
    (hcentralizer : d.R ⊓ centralizer (d.L₁ : Set G) =
      d.E ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G))) :
    frattini ((T : Subgroup G) ⊓ centralizer (L : Set G) : Subgroup G) = ⊥ := by
  let C := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let B := d.R ⊓ centralizer (d.L₁ : Set G)
  let F := (frattini C).map C.subtype
  have hTN := (structural L h).1
  have hLN : L ≤ normalizer (C : Set G) :=
    (le_centralizer_iff.mpr (show C ≤ centralizer (L : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer
      (hTN.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  have hLTF : L ⊔ (T : Subgroup G) ≤ normalizer (F : Set G) :=
    (sup_le hLN hTC).trans (normalizer_le_normalizer_characteristic_image C (frattini C))
  have hNB : normalizer (d.R : Set G) ≤ normalizer (B : Set G) :=
    (le_inf le_rfl (hline.trans (normalizer_le_normalizer_centralizer d.L₁))).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨_, _, hE, _, _⟩ := d.escape_geometry_at h structural marked hmodel hne hescape
  have hEB : d.E ≤ centralizer (B : Set G) := by
    rw [hE]
    intro x hx
    exact centralizer_le (show B ≤ d.R from inf_le_left)
      ((mem_omegaCenterIn_iff _ _).mp hx).2.1
  let _ := D.elementary
  have hEp : IsElementaryAbelian 2 d.E := IsElementaryAbelian.of_le d.le_module
  have hBp : IsPGroup 2 B := T.isPGroup'.of_injective
    (inclusion (show B ≤ T from inf_le_left.trans inf_le_left)) (inclusion_injective _)
  have hphi : (frattini B).map B.subtype = F :=
    frattini_map_eq_of_central_elementary_supplement B C d.E hBp hEp hEB hcentralizer
  have hNF : normalizer (d.R : Set G) ≤ normalizer (F : Set G) := by
    rw [← hphi]
    exact hNB.trans (normalizer_le_normalizer_characteristic_image B (frattini B))
  have horbit : componentOrbit L (T : Subgroup G) = L := by
    apply le_antisymm _ (le_componentOrbit L _)
    exact iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl hTN
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_earlier
    uniquenessEarlier_knownSimple h.simpleQTKE T h.maximal_faithful.1
  have hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = normalizer (L : Set G) := by
    intro N hN hLN
    simpa only [horbit] using hu.normalizer_unique N hN hLN
  have hFp : IsPGroup 2 F := T.isPGroup'.of_injective
    (inclusion ((map_subtype_le (frattini C)).trans inf_le_left)) (inclusion_injective _)
  have hF : F = ⊥ := by
    by_contra hF
    exact hescape (hNF.trans (normalizer_le_of_unique_maximalTwoLocal
      hunique hFp hF hLTF))
  exact ((frattini C).map_eq_bot_iff_of_injective C.subtype_injective).mp hF

theorem fixedBlock_selfCentralizing_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) (d : LocalGeometry D)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hline : normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G))
    (hproduct : (T : Subgroup G) ⊓ centralizer (V : Set G) =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)))
    (hcentralizer : d.R ⊓ centralizer (d.L₁ : Set G) =
      d.E ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G))) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) = V ∧
      (T : Subgroup G) ⊓ centralizer (L : Set G) = fixedSubgroup L V := by
  let C := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  have hphi := fixedBlock_frattini_at h structural marked hmodel hne d hescape hline hcentralizer
  let _ : Fact (IsPGroup 2 C) := ⟨T.isPGroup'.of_injective
    (inclusion (show C ≤ T from inf_le_left)) (inclusion_injective _)⟩
  let _ : IsElementaryAbelian 2 C := (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hphi
  have hprod : Q = V ⊔ C := hproduct
  have hCQ : C ≤ Q := by
    rw [hprod]
    exact le_sup_right
  have hCQc : C ≤ centralizer (Q : Set G) := by
    apply le_centralizer_iff.mpr
    rw [hprod]
    exact sup_le (le_centralizer_iff.mp (hCQ.trans inf_le_right)) C.le_centralizer
  have hCo : C ≤ omegaCenterIn Q := by
    intro x hx
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨hCQ hx, hCQc hx, elemPow_eq_one_of_isElementaryAbelian x hx⟩
  obtain ⟨hZ, _, _, _, _⟩ := d.escape_geometry_at h structural marked hmodel hne hescape
  have ho : omegaCenterIn Q = V := by
    change omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)) = V
    rw [d.fixed_supplement, hZ, inf_eq_left.mpr
      (show fixedSubgroup L V ≤ centralizer (L : Set G) from inf_le_right),
      sup_eq_right.mpr (show fixedSubgroup L V ≤ V from inf_le_left)]
  have hCV : C ≤ V := ho ▸ hCo
  refine ⟨hproduct.trans (sup_eq_left.mpr hCV), le_antisymm (le_inf hCV inf_le_right) ?_⟩
  exact le_inf (inf_le_left.trans D.le_sylow) inf_le_right

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

end

/- Local form of SmallFusion/SLThreeSource/FixedBlockImages.lean. -/
section
open Subgroup Theory.GroupTheory Stellmacher

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Section02

universe u

private theorem max_image_eq_top_at
    {X H : Type*} [Group X] [Group H] [Finite X] [Finite H]
    (V E : Subgroup X) [IsElementaryAbelian 2 V]
    (q : X →* H) (hker : q.ker = V) (hH : Nat.card H = 4)
    (hV : Nat.card V = 16) (hE : Nat.card E = 4)
    (hplane : ∀ a : X, a ∉ V → V ⊓ centralizer ({a} : Set X) = E)
    (A : Subgroup X) (hA : A ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup X))
    (hAV : ¬ A ≤ V) : A.map q = ⊤ := by
  let _ := hA.2.1
  obtain ⟨a, ha, hav⟩ := SetLike.not_le_iff_exists.mp hAV
  have hi : A ⊓ V ≤ E := by
    rw [← hplane a hav]
    exact le_inf inf_le_right (inf_le_left.trans
      (A.le_centralizer.trans (centralizer_le (Set.singleton_subset_iff.mpr ha))))
  have hi4 : Nat.card (A ⊓ V : Subgroup X) ≤ 4 := (card_le_of_le hi).trans_eq hE
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup X) (A ⊓ V) A bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_left, ← hker,
    relIndex_ker, hker] at hcount
  have hA16 : 16 ≤ Nat.card A := hV ▸ hA.2.2 V le_top inferInstance
  have hlo : 16 ≤ 4 * Nat.card (A.map q) := hA16.trans
    (hcount ▸ Nat.mul_le_mul_right (Nat.card (A.map q)) hi4)
  have hhi : Nat.card (A.map q) ≤ 4 :=
    (Nat.card_le_card_of_injective _ (A.map q).subtype_injective).trans_eq hH
  have he : Nat.card (A.map q) = 4 := by omega
  apply eq_of_le_of_card_ge le_top
  simp only [card_top, hH, he, le_refl]

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

theorem exists_max_not_le_module_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) (d : LocalGeometry D)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    ∃ A ∈ elementaryAbelianMaxSubgroups d.R, ¬ A ≤ V := by
  classical
  let _ := D.elementary
  have hVR : V ≤ d.R := le_inf D.le_sylow
    (V.le_centralizer.trans (centralizer_le d.le_module))
  obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty d.R
  by_cases hAV : A ≤ V
  · have he : A = V := eq_of_le_of_card_ge hAV (hA.2.2 V hVR inferInstance)
    subst A
    obtain ⟨_, z, _, _, _, hM, _, _⟩ := exists_slThree_fixed_involution_setup_at
      h D structural marked uniquenessEarlier_knownSimple hmodel hne
    obtain ⟨g, hg, hgM⟩ := SetLike.not_le_iff_exists.mp hescape
    let f := (MulAut.conj g).toMonoidHom
    have hR : d.R.map f = d.R := mem_normalizer_iff_map_conj_eq.mp hg
    have hB := (maxFamily_map_injective_iff f (MulAut.conj g).injective d.R V).mpr hA
    rw [hR] at hB
    refine ⟨V.map f, hB, ?_⟩
    intro hBV
    have hBVeq : V.map f = V := eq_of_le_of_card_ge hBV
      (hB.2.2 V hVR inferInstance)
    apply hgM
    rw [hM]
    exact mem_normalizer_iff_map_conj_eq.mpr hBVeq
  · exact ⟨A, hA, hAV⟩

theorem fixedBlock_pair_of_plane_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) (d : LocalGeometry D)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hself : (T : Subgroup G) ⊓ centralizer (V : Set G) = V)
    (hVcard : Nat.card V = 16)
    (hindex : V.relIndex d.R = 4)
    (hplane : ∀ a ∈ d.R, a ∉ V → V ⊓ centralizer ({a} : Set G) = d.E) :
    ∃ A : Subgroup G, V ∈ elementaryAbelianMaxSubgroups d.R ∧
      elementaryAbelianMaxSubgroups d.R ⊆ {V, A} := by
  classical
  let _ := D.elementary
  have hVR : V ≤ d.R := le_inf D.le_sylow
    (V.le_centralizer.trans (centralizer_le d.le_module))
  let W := V.subgroupOf d.R
  let E := d.E.subgroupOf d.R
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVR
  have hER : d.E ≤ d.R := d.le_module.trans hVR
  have hWcard : Nat.card W = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVR).toEquiv).trans hVcard
  have hEcard : Nat.card E = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hER).toEquiv).trans d.card_plane
  have hWN : (V.subgroupOf d.R).Normal :=
    (normal_subgroupOf_iff_le_normalizer hVR).mpr
      (inf_le_left.trans ((structural L h).2.2 V D).1)
  let _ := hWN
  let q : d.R →* (d.R ⧸ W) := QuotientGroup.mk' W
  have hker : q.ker = W := QuotientGroup.ker_mk' W
  have hquot : Nat.card (d.R ⧸ W) = 4 := hindex
  have hWself : centralizer (W : Set d.R) = W := by
    apply le_antisymm ?_ W.le_centralizer
    intro x hx
    have hc : (x : G) ∈ centralizer (V : Set G) := by
      intro v hv
      exact congrArg Subtype.val (hx ⟨v, hVR hv⟩ hv)
    change (x : G) ∈ V
    exact hself.le ⟨x.property.1, hc⟩
  have hplanes : ∀ a : d.R, a ∉ W → W ⊓ centralizer ({a} : Set d.R) = E := by
    intro a ha
    ext x
    change ((x : G) ∈ V ∧ x ∈ centralizer ({a} : Set d.R)) ↔ (x : G) ∈ d.E
    rw [← hplane a a.property ha]
    simp only [mem_inf, mem_centralizer_singleton_iff]
    exact and_congr_right fun _ => Subtype.ext_iff
  obtain ⟨A, hA, hAV⟩ := exists_max_not_le_module_at h structural marked hmodel hne d hescape
  obtain ⟨B, hB, hAB⟩ := (maxFamily_equiv_iff d.R (MulEquiv.refl d.R) A).mp hA
  have hBW : ¬ B ≤ W := by
    intro hBW
    apply hAV
    rw [hAB]
    rintro _ ⟨x, hx, rfl⟩
    exact hBW hx
  have himage := max_image_eq_top_at W E q hker hquot hWcard hEcard hplanes B hB hBW
  obtain ⟨a, ha, haw⟩ := SetLike.not_le_iff_exists.mp hBW
  have hfixed : W ⊓ centralizer (B : Set d.R) = E := by
    apply le_antisymm
    · rw [← hplanes a haw]
      exact inf_le_inf_left W (centralizer_le (Set.singleton_subset_iff.mpr ha))
    · intro x hx
      refine ⟨d.le_module hx, ?_⟩
      intro b hb
      apply Subtype.ext
      have hxfixed : (x : G) ∈ V ⊓ centralizer (d.R : Set G) := d.fixed_plane ▸ hx
      exact hxfixed.2 b b.property
  have hf := ambient_maxFamily_eq_pair_of_common_image d.R W B q
    (hker.trans hWself.symm) hWself hB hWcard
    (by rw [himage, card_top]; exact hquot)
    (by rw [hfixed]; exact hEcard) a ha (hfixed.trans (hplanes a haw).symm)
    (by intro C hC hCW; rw [himage]; exact
      max_image_eq_top_at W E q hker hquot hWcard hEcard hplanes C hC hCW)
  rw [map_subgroupOf_eq_of_le hVR] at hf
  refine ⟨B.map d.R.subtype, ?_, ?_⟩
  · rw [hf]
    exact Or.inl rfl
  · exact hf.le

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

end

/- Local form of SmallFusion/SLThreeSource/FixedBlockActionSource.lean. -/
section
open Subgroup Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

private theorem sylow_action_index_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (ext : SLThreeExtension D)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hself : (T : Subgroup G) ⊓ centralizer (V : Set G) = V) :
    V.relIndex (T : Subgroup G) = 8 := by
  have hcore : (L ⊔ (T : Subgroup G)).pCoreIn 2 = V :=
    (centralizer_eq_core D h hTV).symm.trans hself
  have hjoin : L ⊔ (T : Subgroup G) = L := by
    rw [join_eq_component_sup_core D ext hTV, hcore, sup_eq_left.mpr D.le_component]
  have hTL : (T : Subgroup G) ≤ L := hjoin ▸ le_sup_right
  have hcoreL : L.pCoreIn 2 = V := by rwa [hjoin] at hcore
  have hp : pCore 2 L = V.subgroupOf L := by
    rw [← hcoreL, pCoreIn]
    exact (comap_map_eq_self_of_injective L.subtype_injective (pCore 2 L)).symm
  let S : Sylow 2 L := T.subtype hTL
  let q := QuotientGroup.mk' (pCore 2 L)
  let Sbar : Sylow 2 (L ⧸ pCore 2 L) :=
    S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  have hcard : Nat.card Sbar = 8 := by
    rw [Sbar.card_eq_multiplicity, Nat.card_congr ext.quotientEquiv.toEquiv,
      Matrix.PSL3Two.card_SL]
    decide +kernel
  have hi : (pCore 2 L).relIndex (S : Subgroup L) = 8 := by
    have hh := relIndex_ker (S : Subgroup L) q
    rw [QuotientGroup.ker_mk'] at hh
    exact hh.trans hcard
  rw [hp, Sylow.coe_subtype, relIndex_subgroupOf hTL] at hi
  exact hi

private theorem single_fixed_plane_at
    (ext : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hN : ∀ n ∈ normalizer (V : Set G), ∃ l ∈ L,
      ∀ v ∈ V, MulAut.conj n v = MulAut.conj l v)
    (hself : (T : Subgroup G) ⊓ centralizer (V : Set G) = V)
    (d : LocalGeometry D) (a : G) (ha : a ∈ d.R) (haV : a ∉ V) :
    V ⊓ centralizer ({a} : Set G) = d.E := by
  let W : Subgroup G := V ⊓ centralizer ({a} : Set G)
  have hEW : d.E ≤ W := by
    refine le_inf d.le_module ?_
    intro e he
    exact mem_centralizer_singleton_iff.mpr (ha.2 e he)
  have hW : Nat.card W ≤ 4 := by
    by_contra! hlarge
    have hc := SLThreeCommutatorSource.CentralizerBound.local_centralizer_of_card_gt_four
      ext hne hN W inf_le_left hlarge
    have haC : a ∈ centralizer (W : Set G) := by
      intro w hw
      exact mem_centralizer_singleton_iff.mp hw.2
    exact haV (hself.le ⟨ha.1, hc.le ⟨hTV ha.1, haC⟩⟩)
  exact (eq_of_le_of_card_ge hEW (by rw [d.card_plane]; exact hW)).symm

theorem fixedBlockActionCalculation_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) (d : LocalGeometry D)
    (hself : (T : Subgroup G) ⊓ centralizer (V : Set G) = V) :
    FixedBlockAction d := by
  obtain ⟨ext⟩ := marked L V h D hmodel hne
  have hTV := ((structural L h).2.2 V D).1
  have hN := SLThreeCommutatorSource.normalizerAction_of_structural_marked_at
    structural marked h D hmodel hne
  let _ := D.elementary
  have hVR : V ≤ d.R := le_inf D.le_sylow
    (V.le_centralizer.trans (centralizer_le d.le_module))
  refine ⟨module_card_sixteen ext hne, ?_, single_fixed_plane_at ext hne hTV hN hself d⟩
  have hi := relIndex_mul_relIndex V d.R (T : Subgroup G) hVR inf_le_left
  rw [d.index, sylow_action_index_at h ext hTV hself] at hi
  omega

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

end

/- Local form of SmallFusion/SLThreeSource/MovingResidualConstructionSpan.lean. -/
section
open Subgroup Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

private theorem normal_cubic_span_at {H : Type*} [Group H] [Finite H]
    {ι : Type*} (P : ι → Subgroup H) (hn : ∀ i, (P i).Normal)
    (hp : ∀ i, IsPPerfect 2 (P i))
    (hc : ∀ i, Nat.card (P i ⧸ pCore 2 (P i)) = 3)
    (hr : primeRank 3 H ≤ 2) (i j : ι) (hne : P i ≠ P j) :
    IsElementaryAbelian 3 ((⨆ k, P k : Subgroup H) ⧸ pCore 2 (⨆ k, P k : Subgroup H)) ∧
    Nat.card ((⨆ k, P k : Subgroup H) ⧸ pCore 2 (⨆ k, P k : Subgroup H)) = 9 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  let A (k : ι) := (P k).map q
  have hAc (k : ι) : Nat.card (A k) = 3 :=
    (Nat.card_congr ((hn k).isSubnormal.quotientCoreImageEquiv 2).toEquiv).symm.trans (hc k)
  let : ∀ k, (A k).Normal := fun k => (hn k).map q (QuotientGroup.mk'_surjective _)
  let : ∀ k, IsCyclic (A k) := fun k => isCyclic_of_prime_card (hAc k)
  let : ∀ k, IsElementaryAbelian 3 (A k) := fun k => {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
      rw [← hAc k]
      exact pow_card_eq_one' }
  have hcomm (k l : ι) : A k ≤ centralizer (A l : Set (H ⧸ pCore 2 H)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_eq_bot_of_odd_normalizes_card_three _ _ (hAc k)
    · rw [hAc l]; decide
    · exact le_normalizer_of_normal
  let : IsElementaryAbelian 3 (⨆ k, A k : Subgroup (H ⧸ pCore 2 H)) :=
    IsElementaryAbelian.iSup_of_le_centralizer A hcomm
  have hcard : Nat.card (⨆ k, A k : Subgroup (H ⧸ pCore 2 H)) ≤ 9 := by
    rw [IsElementaryAbelian.card_eq_pow_primeRank (p := 3)]
    change 3 ^ primeRank 3 (⨆ k, A k : Subgroup (H ⧸ pCore 2 H)) ≤ 3 ^ 2
    apply Nat.pow_le_pow_right (by decide : 0 < 3)
    exact (primeRank_subgroup_le 3 _).trans
      ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hr)
  have hneA : A i ≠ A j := by
    intro he
    apply hne
    rw [← residual_core_preimage_eq (P i) (hn i).isSubnormal (hp i),
      ← residual_core_preimage_eq (P j) (hn j).isSubnormal (hp j)]
    exact congrArg (fun B : Subgroup (H ⧸ pCore 2 H) =>
      (pResidual 2 (B.comap q)).map (B.comap q).subtype) he
  have hgt : 3 < Nat.card (⨆ k, A k : Subgroup (H ⧸ pCore 2 H)) := by
    by_contra hle
    have hei : A i = ⨆ k, A k := eq_of_le_of_card_ge (le_iSup A i) (by rw [hAc i]; omega)
    have hej : A j = ⨆ k, A k := eq_of_le_of_card_ge (le_iSup A j) (by rw [hAc j]; omega)
    exact hneA (hei.trans hej.symm)
  have he9 : Nat.card (⨆ k, A k : Subgroup (H ⧸ pCore 2 H)) = 9 := by
    obtain ⟨n, he⟩ := (IsElementaryAbelian.isPGroup 3
      (⨆ k, A k : Subgroup (H ⧸ pCore 2 H))).exists_card_eq
    have hn2 : n ≤ 2 := by
      by_contra hh
      have hbig : 3 ^ 3 ≤ 3 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      rw [← he] at hbig
      omega
    interval_cases n
    · rw [he] at hgt; norm_num at hgt
    · rw [he] at hgt; norm_num at hgt
    · exact he
  let : ∀ k, (P k).Normal := hn
  have hs : (⨆ k, P k : Subgroup H).IsSubnormal := Normal.isSubnormal inferInstance
  let e := (hs.quotientCoreImageEquiv 2).trans (MulEquiv.subgroupCongr (map_iSup q P))
  exact ⟨IsElementaryAbelian.of_injective e.toMonoidHom e.injective,
    (Nat.card_congr e.toEquiv).trans he9⟩

namespace LocalGeometry

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}
  (d : LocalGeometry D)

theorem plane_centralizer_threeRank_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hCM : centralizer (d.E : Set G) ≤ normalizer (L : Set G)) :
    primeRank 3 (centralizer (d.E : Set G)) ≤ 2 := by
  have he : componentOrbit L (T : Subgroup G) = L := by
    apply le_antisymm _ (le_componentOrbit _ _)
    exact iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl (structural L h).1
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_earlier
    uniquenessEarlier_knownSimple h.simpleQTKE T h.maximal_faithful.1
  have hm : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    simpa only [he] using hu.normalizer_maximal
  exact (primeRank_mono 3 hCM).trans
    (isQuasithin_iff_twoLocal.mp h.simpleQTKE.quasithin _ hm.1 3 Nat.prime_three (by decide))

theorem movingSpan_quotient_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hmoves : ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G)) :
    IsElementaryAbelian 3 (d.movingSpan ⧸ pCore 2 d.movingSpan) ∧
    Nat.card (d.movingSpan ⧸ pCore 2 d.movingSpan) = 9 := by
  classical
  obtain ⟨ext⟩ := marked L V h D hmodel hne
  have hFE := d.fixed_le_plane_at h structural marked hmodel hne hescape
  have hcard := d.lineResidual_quotient_card ext hne hFE
  have hCM := d.plane_centralizer_le_normalizer_at h structural marked hmodel hne hescape
  obtain ⟨_, _, _, hNE, _⟩ := d.escape_geometry_at h structural marked hmodel hne hescape
  let C := centralizer (d.E : Set G)
  let N := normalizer (d.R : Set G)
  let Y (g : N) := d.L₁.map (MulAut.conj (g : G)).toMonoidHom
  have hYC (g : N) : Y g ≤ C :=
    (map_mono (f := (MulAut.conj (g : G)).toMonoidHom)
      (d.lineResidual_le.trans inf_le_right)).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp
          (normalizer_le_normalizer_centralizer d.E (hNE g.property)))
  let P (g : N) := (Y g).subgroupOf C
  let e (g : N) : d.L₁ ≃* P g :=
    ((MulAut.conj (g : G)).subgroupMap d.L₁).trans
      (subgroupOfEquivOfLe (hYC g)).symm
  have hn (g : N) : (P g).Normal := d.conjugate_normal_in_centralizer hCM hNE g g.property
  have hp (g : N) : IsPPerfect 2 (P g) :=
    d.lineResidual_twoPerfect.of_surjective (e g).toMonoidHom (e g).surjective
  have hc (g : N) : Nat.card (P g ⧸ pCore 2 (P g)) = 3 :=
    (Nat.card_congr (QuotientGroup.congr _ _ (e g) (pCore_map_iso 2 (e g))).toEquiv).symm.trans hcard
  obtain ⟨g, hg, hgnot⟩ : ∃ g ∈ N, g ∉ normalizer (d.L₁ : Set G) := by
    simpa only [N, SetLike.le_def, not_forall, Classical.not_imp, exists_prop] using hmoves
  have hPne : P (1 : N) ≠ P ⟨g, hg⟩ := by
    intro he
    have hm := congrArg (map C.subtype) he
    rw [map_subgroupOf_eq_of_le (hYC 1), map_subgroupOf_eq_of_le (hYC ⟨g, hg⟩)] at hm
    have hY1 : Y (1 : N) = d.L₁ := by
      change d.L₁.map (MulAut.conj 1).toMonoidHom = d.L₁
      rw [map_one]
      exact map_id _
    exact hgnot (mem_normalizer_iff_map_conj_eq.mpr ((hY1.symm.trans hm).symm))
  obtain ⟨hel, hnine⟩ := normal_cubic_span_at P hn hp hc
    (d.plane_centralizer_threeRank_at h structural hCM) 1 ⟨g, hg⟩ hPne
  have hmap : (⨆ g, P g : Subgroup C).map C.subtype = d.movingSpan := by
    rw [Subgroup.map_iSup]
    change (⨆ g, (P g).map C.subtype) = ⨆ g : N, Y g
    congr 1
    funext g
    exact map_subgroupOf_eq_of_le (hYC g)
  let ei : (⨆ g, P g : Subgroup C) ≃* d.movingSpan :=
    ((⨆ g, P g : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  let eq := QuotientGroup.congr _ _ ei (pCore_map_iso 2 ei)
  let := hel
  exact ⟨IsElementaryAbelian.of_injective eq.symm.toMonoidHom eq.symm.injective,
    (Nat.card_congr eq.toEquiv).symm.trans hnine⟩

end LocalGeometry

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

end

/- Local form of SmallFusion/SLThreeSource/MovingResidualConstructionLineAction.lean. -/
section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

omit [Finite G] in

private theorem componentCoreAction_restrict_ker_at
    (hc : center (L ⧸ pCore 2 L) = ⊥) :
    ((componentCoreAction L).comp (inclusion L.le_normalizer)).ker = pCore 2 L := by
  exact pCoreJoinAction_restrict_ker 2 (L := L) (U := ⊥) bot_le hc

omit [Finite G] in

private theorem mem_coreActionKernel_iff_at (L : Subgroup G)
    (x : normalizer (L : Set G)) :
    (x : G) ∈ coreActionKernel L ↔ x ∈ (componentCoreAction L).ker := by
  change (x : G) ∈ (componentCoreAction L).ker.map (normalizer (L : Set G)).subtype ↔ _
  rw [mem_map]
  constructor
  · rintro ⟨y, hy, he⟩
    exact (Subtype.ext he : y = x) ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

namespace LocalGeometry

variable (d : LocalGeometry D)

private theorem lineResidual_not_le_coreActionKernel_at
    (ext : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥)
    (hFE : fixedSubgroup L V ≤ d.E) : ¬ d.L₁ ≤ coreActionKernel L := by
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply bot_unique
    intro x hx
    apply ext.quotientEquiv.map_eq_one_iff.mp
    exact Matrix.PSL3Two.center_eq_bot.le
      ((centerCongr ext.quotientEquiv ⟨x, hx⟩).property)
  intro hK
  let i : d.L₁ →* L := inclusion (d.lineResidual_le.trans inf_le_left)
  have hi (x : d.L₁) : i x ∈ pCore 2 L := by
    rw [← componentCoreAction_restrict_ker_at hz]
    exact (mem_coreActionKernel_iff_at L _).mp (hK x.property)
  let f : d.L₁ →* pCore 2 L := i.codRestrict _ hi
  have hf := d.lineResidual_twoPerfect.hom_eq_one_of_isPGroup pCore_isPGroup f
  have hbot : d.L₁ = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have he := DFunLike.congr_fun hf ⟨x, hx⟩
    exact congrArg (fun a : pCore 2 L => ((a : L) : G)) he
  have hd := card_quotient_dvd_card (pCore 2 d.L₁)
  rw [d.lineResidual_quotient_card ext hne hFE, hbot, card_bot] at hd
  norm_num at hd

theorem centralizingLine_card_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hmoves : ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G)) :
    Nat.card (centralizingLine L d.movingSpan) = 3 := by
  obtain ⟨ext⟩ := marked L V h D hmodel hne
  have hFE := d.fixed_le_plane_at h structural marked hmodel hne hescape
  obtain ⟨_, _, _, hNE, _⟩ := d.escape_geometry_at h structural marked hmodel hne hescape
  have hCM := d.plane_centralizer_le_normalizer_at h structural marked hmodel hne hescape
  have hXM := (d.movingSpan_le_centralizer hNE).trans hCM
  let f := (componentCoreAction L).comp (inclusion hXM)
  have hk : f.ker = (d.movingSpan ⊓ coreActionKernel L).subgroupOf d.movingSpan := by
    ext x
    change f x = 1 ↔ (x : G) ∈ d.movingSpan ∧ (x : G) ∈ coreActionKernel L
    rw [and_iff_right x.property]
    exact (mem_coreActionKernel_iff_at L (inclusion hXM x)).symm
  let P := d.L₁.subgroupOf d.movingSpan
  let e := subgroupOfEquivOfLe d.lineResidual_le_movingSpan
  have hp : IsPPerfect 2 P := d.lineResidual_twoPerfect.of_surjective
    e.symm.toMonoidHom e.symm.surjective
  have hout : ¬ P ≤ f.ker := by
    intro hPk
    apply d.lineResidual_not_le_coreActionKernel_at ext hne hFE
    intro x hx
    have hmem := hPk (show (⟨x, d.lineResidual_le_movingSpan hx⟩ : d.movingSpan) ∈ P from hx)
    rw [hk] at hmem
    exact hmem.2
  have h9 := (d.movingSpan_quotient_at h structural marked hmodel hne hescape hmoves).2
  let eq := ext.quotientEquiv.trans Matrix.PSL3Two.equiv
  have hAut : Nat.card (MulAut (L ⧸ pCore 2 L)) = 336 :=
    (Nat.card_congr (MulAut.congr eq).toEquiv).trans Matrix.PSL3Two.Automorphisms.card_aut
  have hc := f.card_kernel_image_cubic P hp hout h9 (by rw [hAut]; decide)
  rw [hk] at hc
  exact hc

end LocalGeometry

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

end

/- Local form of SmallFusion/SLThreeSource/MovingResidualConstructionInverter.lean. -/
section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

namespace LocalGeometry

variable (d : LocalGeometry D)

private theorem component_sylow_at (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup G).subgroupOf L := by
  let J := L ⊔ (T : Subgroup G)
  let : (L.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer hTL)
  obtain ⟨P, hP⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_subgroupOf_eq_of_normal
    (L.subgroupOf J)
  let e := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (P : Subgroup (L.subgroupOf J)).map e.toMonoidHom = _
  rw [hP]
  ext l
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hl
    exact ⟨⟨⟨l, (le_sup_left : L ≤ J) l.property⟩, l.property⟩, hl, rfl⟩

theorem movingLineInverter_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    MovingLineInverter d := by
  obtain ⟨ext⟩ := marked L V h D hmodel hne
  have hTL := (structural L h).1
  have hFE := d.fixed_le_plane_at h structural marked hmodel hne hescape
  have hc := d.lineResidual_quotient_card ext hne hFE
  obtain ⟨_, _, _, hNE, _⟩ := d.escape_geometry_at h structural marked hmodel hne hescape
  have hCM := d.plane_centralizer_le_normalizer_at h structural marked hmodel hne hescape
  have hXM := (d.movingSpan_le_centralizer hNE).trans hCM
  have hY : d.L₁ ∈ normalCubicResiduals d.movingSpan := by
    refine ⟨d.lineResidual_le_movingSpan, ?_, d.lineResidual_twoPerfect, hc⟩
    exact normal_subgroupOf_of_le_normalizer
      ((le_inf hXM (d.movingSpan_le_centralizer hNE)).trans d.centralizer_normalizes_lineResidual)
  have hTY : (T : Subgroup G) ≤ normalizer (d.L₁ : Set G) :=
    (le_inf hTL d.sylow_normalizes).trans (d.intersection_normalizes_lineResidual hNE)
  obtain ⟨S, hS⟩ := component_sylow_at hTL
  let A := d.L₁.subgroupOf L
  have hAL : d.L₁ ≤ L := d.lineResidual_le.trans inf_le_left
  let eA := subgroupOfEquivOfLe hAL
  have hAp : IsPPerfect 2 A := d.lineResidual_twoPerfect.of_surjective
    eA.symm.toMonoidHom eA.symm.surjective
  have hAc : Nat.card (A ⧸ pCore 2 A) = 3 :=
    (Nat.card_congr (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).toEquiv).trans hc
  let f : L →* Matrix.PSL3Two.SL :=
    ext.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f := ext.quotientEquiv.surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ ext.quotientEquiv.injective,
      QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hSA : (S : Subgroup L) ≤ normalizer (A : Set L) := by
    rw [hS]
    intro t ht
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (hTY ht) a
  have hn := Matrix.PSL3Two.ResidualRecognition.commutator_not_two_of_cover
    f hf hk A S hAp hAc hSA
  have hcomm : ¬ IsPGroup 2 (⁅d.L₁, (T : Subgroup G) ⊓ L⁆ : Subgroup G) := by
    intro hp
    apply hn
    have he : (⁅A, (S : Subgroup L)⁆).map L.subtype = ⁅d.L₁, (T : Subgroup G) ⊓ L⁆ := by
      rw [map_commutator, hS, map_subgroupOf_eq_of_le hAL, subgroupOf_map_subtype]
    have hm : IsPGroup 2 ((⁅A, (S : Subgroup L)⁆).map L.subtype) := he.symm ▸ hp
    exact hm.of_equiv ((⁅A, (S : Subgroup L)⁆).equivMapOfInjective
      L.subtype L.subtype_injective).symm
  obtain ⟨t, ht⟩ := exists_normalCubic_inverter_of_commutator_not_two
    d.movingSpan d.L₁ ((T : Subgroup G) ⊓ L) hY
    (inf_le_left.trans (d.sylow_normalizes.trans d.normalizer_normalizes_movingSpan))
    (inf_le_left.trans hTY) hcomm
  exact ⟨⟨t, t.property.1⟩, t.property.2, ht⟩

end LocalGeometry

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

namespace CFSG.Quasithin.Chapter14.Section03.CaseOneSource

open Chapter12.Section02 Chapter12.Section04.SmallFusion

open Chapter12.Section04.SmallFusion.SLThreeSource

universe u

end CFSG.Quasithin.Chapter14.Section03.CaseOneSource

end

/- Local form of SmallFusion/SLThreeSource/NormalResidualOrbit.lean. -/
section
open Subgroup Theory.GroupTheory

open scoped Pointwise

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

namespace NormalResidualGeometry

variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}
  {d : LocalGeometry D}

end NormalResidualGeometry

namespace LocalGeometry

variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}
  (d : LocalGeometry D)

theorem false_of_moving_normal_residual_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hmoves : ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G))
    (f : NormalResidualGeometry d) : False := by
  obtain ⟨_, _, _, hNE, hi⟩ := d.escape_geometry_at h structural marked hmodel hne hescape
  have hn := d.normalizes_fourth_normal_residual f hNE hi hmoves
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_earlier
    uniquenessEarlier_knownSimple h.simpleQTKE T h.maximal_faithful.1
  have he : componentOrbit L (T : Subgroup G) = L := by
    apply le_antisymm _ (le_componentOrbit L _)
    exact iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl
      (structural L h).1
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      f.X ⊔ (L ⊔ (T : Subgroup G)) ≤ N →
      N = normalizer (L : Set G) := by
    intro N hN hON
    simpa only [he] using hu.normalizer_unique N hN (le_sup_right.trans hON)
  let := f.residual_normal
  have hX₁ : f.X₁ ≤ f.X ⊔ (L ⊔ (T : Subgroup G)) := f.fixed_mem.1.trans le_sup_left
  have hcontrol := normalizer_le_of_characteristic_two_unique
    f.characteristic_two huniq hX₁ f.residual_nontrivial
    (le_normalizer_of_normal_subgroupOf hX₁)
  exact hescape (hn.trans hcontrol)

end LocalGeometry

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

end

/- Local form of SmallFusion/SLThreeSource/MovingResidualConstructionAssembly.lean. -/
section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

namespace LocalGeometry

variable (d : LocalGeometry D)

theorem normalResidualGeometry_of_action_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hmoves : ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G))
    (hblock : ChapterC.IsLinearTwoBlock L 3)
    (hline : Nat.card (centralizingLine L d.movingSpan) = 3)
    (hinv : MovingLineInverter d) : Nonempty (NormalResidualGeometry d) := by
  obtain ⟨hel, h9⟩ := d.movingSpan_quotient_at h structural marked hmodel hne hescape hmoves
  let := hel
  obtain ⟨_, _, _, hNE, _⟩ := d.escape_geometry_at h structural marked hmodel hne hescape
  have hCM := d.plane_centralizer_le_normalizer_at h structural marked hmodel hne hescape
  have hXM := (d.movingSpan_le_centralizer hNE).trans hCM
  have hTM := (structural L h).1
  have hTX := d.sylow_normalizes.trans d.normalizer_normalizes_movingSpan
  obtain ⟨ext⟩ := marked L V h D hmodel hne
  have hL1 : d.L₁ ∈ normalCubicResiduals d.movingSpan := by
    refine ⟨d.lineResidual_le_movingSpan, ?_, d.lineResidual_twoPerfect, ?_⟩
    · apply normal_subgroupOf_of_le_normalizer
      exact (le_inf hXM (d.movingSpan_le_centralizer hNE)).trans
        d.centralizer_normalizes_lineResidual
    · exact d.lineResidual_quotient_card ext hne
        (d.fixed_le_plane_at h structural marked hmodel hne hescape)
  have hX1 := centralizingResidual_mem L d.movingSpan h9 hline
  obtain ⟨t, htL, htinv⟩ := hinv
  let a : normalizer (d.movingSpan : Set G) :=
    ⟨t, d.normalizer_normalizes_movingSpan (d.sylow_normalizes t.property)⟩
  have htfix : ∀ z ∈ normalCubicResidualImage d.movingSpan (centralizingResidual L d.movingSpan),
      normalCubicQuotientAction d.movingSpan a z = z := by
    apply quotientAction_fixes_of_centralizes
    exact le_centralizer_iff.mp (centralizingResidual_centralizes L d.movingSpan hblock hXM) htL
  refine ⟨{
    X := d.movingSpan
    X₁ := centralizingResidual L d.movingSpan
    normalizes_X := d.normalizer_normalizes_movingSpan
    elementary := hel
    quotient_card := h9
    line_mem := hL1
    fixed_mem := hX1
    distinct_images := ?_
    actor := t
    inverts_line := htinv
    fixes_line := htfix
    characteristic_two := moving_overgroup_characteristicTwo_at h structural d.movingSpan hXM
    residual_normal := centralizingResidual_normal_join L d.movingSpan T hblock hXM hTM hTX
    residual_nontrivial := centralizingResidual_ne_bot L d.movingSpan h9 hline }⟩
  exact cubic_images_distinct_of_inverted_fixed _ _ (normalCubicResidualImage_card hL1)
    (normalCubicQuotientAction d.movingSpan a) htinv htfix

theorem false_of_moving_source_action_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hmoves : ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G))
    (hblock : ChapterC.IsLinearTwoBlock L 3)
    (hline : Nat.card (centralizingLine L d.movingSpan) = 3)
    (hinv : MovingLineInverter d) : False := by
  obtain ⟨f⟩ := d.normalResidualGeometry_of_action_at h structural marked hmodel hne
    hescape hmoves hblock hline hinv
  exact d.false_of_moving_normal_residual_at h structural marked hmodel hne hescape hmoves f

end LocalGeometry

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

namespace CFSG.Quasithin.Chapter14.Section03.CaseOneSource

open Chapter12.Section02 Chapter12.Section04.SmallFusion

open Chapter12.Section04.SmallFusion.SLThreeSource

universe u

end CFSG.Quasithin.Chapter14.Section03.CaseOneSource

end

/- Local form of SmallFusion/SLThreeSource/FixedBlockMSIndependentApplication.lean. -/
section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Section02

open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

universe u

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

namespace LocalGeometry

variable (d : LocalGeometry D)

theorem fixedBlockIdentities_without_binary_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    FixedBlockIdentities d := by
  obtain ⟨e,hc,hQ,_⟩ := d.ms_specialization_without_binary_at h structural marked hmodel hne hescape
  exact d.ms_fixedBlockIdentities_at h structural marked hmodel hne hescape e hc hQ

theorem false_of_moving_without_binary_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (marked : SLThreeSource.At.SLThreeAlternative1222At KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hmoves : ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G))
    (hline : Nat.card (centralizingLine L d.movingSpan) = 3)
    (hinv : MovingLineInverter d) : False := by
  obtain ⟨_,_,_,hb⟩ := d.ms_specialization_without_binary_at h structural marked hmodel hne hescape
  exact d.false_of_moving_source_action_at h structural marked hmodel hne hescape hmoves
    hb hline hinv

end LocalGeometry

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

end
