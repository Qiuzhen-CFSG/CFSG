module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PointCoreNormalizer
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentCoverPlacement
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.NormalizerConjugacy
public import Theory.GroupTheory.FiniteParabolicTransfer

/-!
# The original component normalizer has no large three-subgroup

For the selected original K, N_K(R1) lies in M. Its prime-to-three residual
therefore lies in L, and its two-perfectness places it in the same L1.
Every three-subgroup of N_K(R1) embeds in an actual Sylow E9 of L1.

Because H contains the original Sylow T, O2(H) lies in R1. Thus the literal
map H -> H/O2(H) carries N_K(R1) onto N_{K-star}(R1-star). Lifting Sylow
subgroups through this same map proves that every Sylow three-subgroup
of the latter normalizer has order dividing nine. This is the source upper
bound for the cubic A7 contradiction; the correctly marked model lower
bound, the Mathieu module exclusion and the remaining component cases
are still needed. Earlier fixed-space and invariance inputs stay explicit.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The prime-to-three residual of the original component normalizer lies
in the original point residual, as in the cubic A7 exclusion on p.832. -/
theorem SourceHypothesis.original_component_pointNormalizer_residual_le
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H) :
    let N := c.K ⊓ normalizer ((D.fullSetup hZ T z).R₁ : Set G)
    (primeToResidual 3 N).map N.subtype ≤ (D.fullSetup hZ T z).L₁ := by
  let F := D.fullSetup hZ T z
  let N := c.K ⊓ normalizer (F.R₁ : Set G)
  let A := (primeToResidual 3 N).map N.subtype
  have hNM : N ≤ M L := inf_le_right.trans
    (S.original_point_core_thompson D hZ z hz hTV hTz).2
  have hAL : A ≤ L := (embedded_primeToResidual_mono 3 hNM).trans_eq
    (S.normalizer_primeToResidual D)
  have hAC : A ≤ L ⊓ F.Gz := le_inf hAL
    ((map_subtype_le _).trans (inf_le_left.trans (c.le_H.trans hH.2.1)))
  have hp : IsPPerfect 2 A :=
    (isPPerfect_primeToResidual (G := N) 3 2 (by decide)).of_surjective
      (N.subtype.subgroupMap (primeToResidual 3 N)) (N.subtype.subgroupMap_surjective _)
  have he : (pResidual 2 A).map A.subtype = A := by
    rw [(pResidual_eq_top_iff 2 A).mpr hp,←MonoidHom.range_eq_map,range_subtype]
  change A ≤ F.L₁
  rw [←he]
  exact embedded_pResidual_mono 2 hAC

/-- Every original three-subgroup of N_K(R1) embeds in the actual E9 Sylow
of L1. This is the literal upper bound contradicted by the cubic A7 model. -/
theorem SourceHypothesis.original_component_pointNormalizer_three_card
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H)
    (P : Subgroup G) (hP : IsPGroup 3 P)
    (hPN : P ≤ c.K ⊓ normalizer ((D.fullSetup hZ T z).R₁ : Set G)) :
    P ≤ (D.fullSetup hZ T z).L₁ ∧ Nat.card P ∣ 9 := by
  let F := D.fullSetup hZ T z
  let N := c.K ⊓ normalizer (F.R₁ : Set G)
  have hPR : P ≤ (primeToResidual 3 N).map N.subtype := by
    rw [←map_subgroupOf_eq_of_le hPN]
    exact map_mono (le_primeToResidual_of_isPGroup hP.comap_subtype)
  have hPA : P ≤ F.L₁ := hPR.trans
    (S.original_component_pointNormalizer_residual_le D hZ z hz hTV hTz hH c)
  obtain ⟨R,hR⟩ := (hP.comap_subtype (K := F.L₁)).exists_le_sylow
  have hc := card_dvd_of_le hR
  change Nat.card (P.subgroupOf F.L₁) ∣ Nat.card R at hc
  rw [Nat.card_congr (subgroupOfEquivOfLe hPA).toEquiv,
    (S.original_point_residual_sylow D hZ z hz hTz R).2] at hc
  exact ⟨hPA,hc⟩


/-- The original H two-core lies in R1 because H contains the same Sylow T. -/
theorem SourceHypothesis.original_core_le_point_core
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    H.pCoreIn 2 ≤ (D.fullSetup hZ T z).R₁ := by
  let F := D.fullSetup hZ T z
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow H (T.subtype hTH)).trans_eq
      (by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH])
  apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H) (hQT.trans le_sup_right)
  exact (show F.L₁ ⊔ (T : Subgroup G) ≤ H from
    sup_le (fun x hx => hH.1.2 (Or.inl hx)) (fun x hx => hH.1.2 (Or.inr hx))).trans
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))

/-- The full component normalizer commutes with the literal star quotient.
The kernel containment is proved on the unchanged original R1. -/
theorem SourceHypothesis.original_component_pointNormalizer_star
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H) :
    Nonabelian.Setup.star H (c.K ⊓ normalizer ((D.fullSetup hZ T z).R₁ : Set G)) =
      Nonabelian.Setup.star H c.K ⊓
        normalizer (Nonabelian.Setup.star H (D.fullSetup hZ T z).R₁ : Set (Nonabelian.Setup.Hstar H)) := by
  let F := D.fullSetup hZ T z
  let q := QuotientGroup.mk' (pCore 2 H)
  let R := F.R₁.subgroupOf H
  have hRH : F.R₁ ≤ H := (S.original_point_core_eq D hZ z hz hTz).2.2.trans
    (fun x hx => hH.1.2 (Or.inr hx))
  have hk : q.ker ≤ R := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact S.original_core_le_point_core D hZ z hH (mem_map_of_mem H.subtype hx)
  have hn : (normalizer (R.map q : Set (Nonabelian.Setup.Hstar H))).comap q =
      (normalizer (F.R₁ : Set G)).subgroupOf H := by
    rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),
      comap_map_eq_self hk,←subgroupOf_normalizer_eq hRH]
  change ((c.K ⊓ normalizer (F.R₁ : Set G)).subgroupOf H).map q =
    (c.K.subgroupOf H).map q ⊓ normalizer (R.map q : Set (Nonabelian.Setup.Hstar H))
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨mem_map_of_mem q hy.1,hn.ge hy.2⟩
  · rintro ⟨⟨y,hy,rfl⟩,hx⟩
    exact ⟨y,⟨hy,hn.le hx⟩,rfl⟩

/-- Every Sylow three-subgroup of the actual star normalizer has order
at most nine. The upcoming cover-model contradiction must use this same normalizer. -/
theorem SourceHypothesis.original_component_pointNormalizer_star_sylow_card
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H)
    (P : Sylow 3 (Nonabelian.Setup.star H c.K ⊓
      normalizer (Nonabelian.Setup.star H (D.fullSetup hZ T z).R₁ : Set (Nonabelian.Setup.Hstar H)) :
      Subgroup (Nonabelian.Setup.Hstar H))) : Nat.card P ∣ 9 := by
  let F := D.fullSetup hZ T z
  let N := c.K ⊓ normalizer (F.R₁ : Set G)
  let B := Nonabelian.Setup.star H c.K ⊓
    normalizer (Nonabelian.Setup.star H F.R₁ : Set (Nonabelian.Setup.Hstar H))
  have hNH : N ≤ H := inf_le_left.trans c.le_H
  let q := QuotientGroup.mk' (pCore 2 H)
  let e : N ≃* N.subgroupOf H := (subgroupOfEquivOfLe hNH).symm
  let f : N →* B :=
    (MulEquiv.subgroupCongr (S.original_component_pointNormalizer_star D hZ z hz hTz hH c)).toMonoidHom.comp
      ((q.subgroupMap (N.subgroupOf H)).comp e.toMonoidHom)
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr (S.original_component_pointNormalizer_star D hZ z hz hTz hH c)).surjective.comp
      ((q.subgroupMap_surjective _).comp e.surjective)
  obtain ⟨R,hR⟩ := Sylow.mapSurjective_surjective hf 3 P
  have hc := (S.original_component_pointNormalizer_three_card D hZ z hz hTV hTz hH c
    ((R : Subgroup N).map N.subtype) (R.isPGroup'.map N.subtype) (map_subtype_le _)).2
  rw [card_map_of_injective N.subtype_injective] at hc
  have hd : Nat.card P ∣ Nat.card R := by
    rw [←hR]
    exact card_dvd_of_surjective (f.subgroupMap (R : Subgroup N))
      (f.subgroupMap_surjective _)
  exact hd.trans hc

end CFSG.Quasithin.Chapter12.Section06
