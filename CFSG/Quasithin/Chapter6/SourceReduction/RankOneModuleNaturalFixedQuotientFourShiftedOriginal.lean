module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourShiftedSource
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourOvergroups
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientHermitianThompson
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticOrbit
public import Theory.GroupTheory.PResidual.SylowJoin

/-!
# The original quintic actor fails to normalize the orbit Sylow

For an actual H-star member H in K₀T, normalization of T∩K₀ by the quintic
actor would make S=O₂(XT) Sylow in K₀S, hence in O²(H)S. This normal
subgroup of H contains J(T). The proved normal-intersection E.6.26 uses
H's actual generation-one witness and forces H≤M, a contradiction.
Every group and actor remains on the original carrier. No generation
parameter inheritance for O²(H)S is assumed.

Source: Aschbacher--Smith 6.1.4, printed p.665.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
attribute [local instance] SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H M₁ K : Subgroup G} {n : ℕ}

/-- The original inner Sylow traps an H of generation one when it is Sylow
in O²(H)S. The proof uses H's own E-members and its actual maximum family. -/
theorem original_hermitian_residual_inner_sylow_overgroup_le
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2))
    (hTH : (T : Subgroup G) ≤ H) (hgen : ChapterE.generationParameter H = 1)
    (hSyl : Chapter1.IsSylowIn 2
      (((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
      ((pResidual 2 H).map H.subtype ⊔
        (((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2))) : H ≤ M := by
  let S := ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2
  let R := (pResidual 2 H).map H.subtype
  let P := T.subtype hTH
  let N := pResidual 2 H ⊔ S.subgroupOf H
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hST : S ≤ (T : Subgroup G) := sup_le inf_le_left hQT
  have hSH : S ≤ H := hST.trans hTH
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) := by
    dsimp only [S]
    rw [←original_hermitian_quintic_sylow_core h hout hm]
    exact le_sup_right.trans
      ((quinticResidual T L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _
          (pCore 2 (quinticResidual T L ⊔ (T : Subgroup G) : Subgroup G))))
  let _ : N.Normal := pResidual_sup_normal_of_sylow_normalizes P (S.subgroupOf H) (by
    intro x hx
    rw [←subgroupOf_normalizer_eq hSH]
    exact hTS hx)
  have hPmap : (P : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hTH
  have hNmap : N.map H.subtype = R ⊔ S := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hSH]
  have hTI : (T : Subgroup G) ⊓ (R ⊔ S) = S :=
    (Chapter1.isSylowIn_iff.mp hSyl).2.2 _ (T.isPGroup'.to_le inf_le_left)
      (le_inf hST le_sup_right) inf_le_right
  have hmap : ((P : Subgroup H) ⊓ N).map H.subtype = S := by
    rw [Subgroup.map_inf _ _ H.subtype H.subtype_injective,hPmap,hNmap,hTI]
  have hJN : ChapterB.thompsonJ (P : Subgroup H) 0 ≤ N := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [←ChapterB.thompsonJ_map_injective H.subtype H.subtype_injective,hPmap,hNmap,
      ChapterB.thompsonJ_zero,original_hermitian_four_thompson_eq_twoCore h hout hm]
    have hh := ChapterB.thompsonJ_le ((L ⊔ (T : Subgroup G)).pCoreIn 2) 0
    rw [ChapterB.thompsonJ_zero] at hh
    exact hh.trans (le_sup_right.trans le_sup_right)
  have hE := full_reduced_hermitian_hypothesisE61 h hm
  have hQ : ChapterE.Section06.sylowCentralizer (T : Subgroup G)
      (reducedSubgroup (L ⊔ (T : Subgroup G))) ≤ S := by
    change (T : Subgroup G) ⊓ centralizer
      (reducedSubgroup (L ⊔ (T : Subgroup G)) : Set G) ≤ S
    rw [full_reduced_hermitian_sylow_centralizer h hm]
    exact le_sup_right
  have hJ := (h.reduced_enlargement.rankOneInput hout).hermitian_inner_thompson_one_centralizes
    hm (by decide : 1 < 2)
  have hEG : ChapterE.IsEGenerated 1 H := by
    have hh := ChapterE.isEGenerated_generationParameter_of_pos (G := H)
      (hgen ▸ (by decide : 0 < (1 : ℕ)))
    rwa [hgen] at hh
  exact (ChapterE.Section06.FixedPointBounds.SylowThompson.source_E_6_26_of_normal_intersection
    hE (by decide : 0 < 1) H P N hEG hJN (hmap.symm ▸ hQ) (hmap.symm ▸ hST)
    (full_reduced_hermitian_one_lt_globalR h hout hm (by decide)) (hmap.symm ▸ hJ)).1

omit [Finite G] in
private theorem residual_le_orbit (K₀ : Subgroup G)
    (hTK : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hH : H ≤ K₀ ⊔ (T : Subgroup G)) : (pResidual 2 H).map H.subtype ≤ K₀ := by
  let J := K₀ ⊔ (T : Subgroup G)
  let C := K₀.subgroupOf J
  let _ : C.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le K₀.le_normalizer hTK)
  have hsup : C ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show K₀ ≤ J from le_sup_left),
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right),
      ←MonoidHom.range_eq_map,range_subtype]
  have hq := isPGroup_quotient_of_sup_eq_top C ((T : Subgroup G).subgroupOf J)
    T.isPGroup'.comap_subtype hsup
  have hr : pResidual 2 J ≤ C := sInf_le ⟨inferInstance,hq⟩
  have hh := (map_pResidual_le 2 (inclusion hH)).trans hr
  rintro _ ⟨x,hx,rfl⟩
  exact hh (mem_map_of_mem (inclusion hH) hx)

/-- The literal quintic residual cannot normalize the inner Sylow of the
T-orbit of any actual comparison component outside M. -/
theorem original_hermitian_quintic_not_normalizes_orbit_sylow
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M) :
    ¬ quinticResidual T L ≤ normalizer
      (((T : Subgroup G) ⊓ componentOrbit K (T : Subgroup G)) : Set G) := by
  classical
  intro hn
  let K₀ := componentOrbit K (T : Subgroup G)
  let S := ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hSyl : Chapter1.IsSylowIn 2 S (K₀ ⊔ S) :=
    original_hermitian_orbit_sylow_of_normalizes h hout hm hn
  have hTM₁ : (T : Subgroup G) ≤ M₁ := sylow_le_omegaCentralizer.trans hCM₁
  have horb : K₀ ⊔ (T : Subgroup G) ≤ M₁ := by
    rw [componentOrbit_sup]
    exact sup_le hK.1 hTM₁
  have hescape : ¬ K₀ ⊔ (T : Subgroup G) ≤ M :=
    fun hh => hnot ((le_componentOrbit K (T : Subgroup G)).trans (le_sup_left.trans hh))
  let F : Set (Subgroup G) := {H | H ∈ Chapter1.HOver G (T : Set G) ∧
    ¬ H ≤ M ∧ H ≤ K₀ ⊔ (T : Subgroup G)}
  have hF : F.Nonempty := ⟨K₀ ⊔ (T : Subgroup G),
    Chapter3.mem_HOver_of_sylow_interval T le_sup_right horb
      ⟨Chapter1.mem_H_of_isTwoLocal hM₁.1,hTM₁⟩,hescape,le_rfl⟩
  obtain ⟨H,hH⟩ := (Set.toFinite F).exists_minimalFor id F hF
  have hstar : H ∈ Chapter3.HStar (T : Subgroup G) M := by
    refine ⟨⟨hH.1.1,hH.1.2.1⟩,?_⟩
    intro Y hY hYH
    exact hH.2 ⟨hY.1,hY.2,hYH.trans hH.1.2.2⟩ hYH
  have hr : (pResidual 2 H).map H.subtype ≤ K₀ :=
    residual_le_orbit K₀ (le_normalizer_componentOrbit K _) hH.1.2.2
  have hsyl : Chapter1.IsSylowIn 2 S ((pResidual 2 H).map H.subtype ⊔ S) :=
    hSyl.restrict le_sup_right (sup_le_sup_right hr S)
  exact hstar.1.2 (original_hermitian_residual_inner_sylow_overgroup_le
    h hout hm hstar.1.1.2 (h.generation_one H hstar) hsyl)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
