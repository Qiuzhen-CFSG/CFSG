module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallCoreInterval
public import Theory.SpecificGroups.PSL2.SmallCubicCore
/-!
# Exact core indices in the collapsed source enlargement

Retain X=O²(H), K=<X^E>, and S=T∩K from the original normalizer argument.
When O₂(X)≤O₂(K), the image of X is its original cubic plane, normalized
by the full quotient Sylow. The two cyclic coordinate projections have
order three, so each four-group centralizes exactly two elements against
its cubic. Consequently the image of O₂(XS) has order four.

The literal quotient map then gives [O₂(XS):O₂(K)]=4 and
[S:O₂(XS)]=4. These are the exact indices in the previously established
strict core interval. The source consumer retains all ambient, module,
component, congruence and collapse hypotheses. This does not exclude the
collapsed configuration or complete either original contract. That exclusion
and final assembly remain with qt-d-10-nona5-half-sylow-unique; ModuleChoiceAt
is the only external premise, finally discharged by
qt-d-10-nona5-point-control.

Source: Aschbacher--Smith 10.2.5--6, printed pp.748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H P I : Subgroup G}

/-- The actual parabolic core has image of order four in the containing quotient. -/
theorem Data.collapsed_quotient_core_card (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 8 = 3 ∨ p % 8 = 5)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    Nat.card (quotientImage (enlargedResidual T L H)
      ((residual H ⊔ ((T : Subgroup G) ⊓ enlargedResidual T L H)).pCoreIn 2)) = 4 := by
  let K := enlargedResidual T L H
  let A := quotientImage K P
  obtain ⟨S,hS⟩ := h.quotient_sylow
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hpc := hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))
  let : IsElementaryAbelian 3 P := hpc.1
  let : IsElementaryAbelian 3 (P.subgroupOf K) :=
    IsElementaryAbelian.subgroupOf (hs.toLocalInput.complement_le.trans h.residual_le_enlargedResidual)
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.map (QuotientGroup.mk' (pCore 2 K))
  have hep : Nonempty (P ≃* quotientImage (enlargedResidual T L H) P) :=
    hK.symm ▸ ⟨SwappedSylow.quotientComplementEquiv hs.toSwappedInput⟩
  obtain ⟨ep⟩ := hep
  have hA : Nat.card A = 9 := (Nat.card_congr ep.toEquiv).symm.trans hpc.2
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  let j := e.trans (eF.prodCongr eF)
  have hr : primeRank 3 (PSL(2,F) × PSL(2,F)) ≤ 2 := by
    rw [←primeRank_congr 3 j,hK]
    exact (SwappedSylow.orbit_quotient_sqtk hs.toSwappedInput).stronglyQuasithin 3
      (by decide) (by decide)
  let A' := A.map j.toMonoidHom
  have hthree : IsPGroup 3 A' := (IsElementaryAbelian.isPGroup 3 A).map _
  let : IsCyclic (A'.map (MonoidHom.fst PSL(2,F) PSL(2,F))) :=
    SwappedFactorsProof.cyclic_pSubgroup_of_product_rank (by decide) hr _ (hthree.map _)
  let : IsCyclic (A'.map (MonoidHom.snd PSL(2,F) PSL(2,F))) :=
    SwappedFactorsProof.cyclic_pSubgroup_of_product_rank (by decide) hr _ (hthree.map _)
  have hN : (S : Subgroup (XiQuotient K)) ≤ normalizer (A : Set _) := by
    rw [hS,show A = quotientImage K (residual H) from
      (h.quotient_residual_eq_complement_of_core_le hs.toLocalInput hc).symm]
    apply (map_mono ?_).trans (le_normalizer_map (QuotientGroup.mk' (pCore 2 K)))
    rw [←subgroupOf_normalizer_eq h.residual_le_enlargedResidual]
    exact subgroupOf_mono K hs.invariant
  rw [←h.quotient_parabolic_core_eq_image,
    h.quotient_residual_eq_complement_of_core_le hs.toLocalInput hc,←hS]
  exact Theory.PSL2.small_pair_cubic_core_card_of_equiv j
    ⟨p,1,hp,ho,by decide,by simpa using hF⟩
    (Theory.PSL2.not_eight_dvd_card_of_small_mod_eight (hF ▸ ho) (hF ▸ hmod)) S A hA hN

omit [Finite G] in
private theorem quotientImage_card {K A : Subgroup G} (hA : A ≤ K) :
    Nat.card (quotientImage K A) = (K.pCoreIn 2).relIndex A := by
  have he : (K.pCoreIn 2).subgroupOf K = pCore 2 K :=
    comap_map_eq_self_of_injective K.subtype_injective _
  have hm := relIndex_ker (A.subgroupOf K) (QuotientGroup.mk' (pCore 2 K))
  rw [QuotientGroup.ker_mk'] at hm
  rw [←relIndex_subgroupOf hA,he]
  exact hm.symm

/-- Both steps in the original core interval have index four under collapse. -/
theorem Data.collapsed_parabolic_core_relIndex (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 8 = 3 ∨ p % 8 = 5)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    ((enlargedResidual T L H).pCoreIn 2).relIndex
      ((residual H ⊔ ((T : Subgroup G) ⊓ enlargedResidual T L H)).pCoreIn 2) = 4 ∧
    ((residual H ⊔ ((T : Subgroup G) ⊓ enlargedResidual T L H)).pCoreIn 2).relIndex
      ((T : Subgroup G) ⊓ enlargedResidual T L H) = 4 := by
  let K := enlargedResidual T L H
  let B := (residual H ⊔ ((T : Subgroup G) ⊓ K)).pCoreIn 2
  let S : Subgroup G := (T : Subgroup G) ⊓ K
  have hBS : B ≤ S := h.parabolic_intersection_core_le.trans
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  have hQB : K.pCoreIn 2 ≤ B := by
    apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K)
      ((h.enlargedResidual_core_le_intersection.trans
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).trans le_sup_right)
    exact (sup_le h.residual_le_enlargedResidual inf_le_right).trans
      (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  have hfour : (K.pCoreIn 2).relIndex B = 4 := by
    rw [←quotientImage_card (hBS.trans inf_le_right)]
    exact h.collapsed_quotient_core_card hn hs hK hp ho hm hmod hc
  refine ⟨hfour,?_⟩
  obtain ⟨U,hU⟩ := h.quotient_sylow
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  let j := e.trans (eF.prodCongr eF)
  have h16 : Nat.card U = 16 := by
    have hh := Theory.PSL2.small_pair_sylow_card
      ⟨p,1,hp,ho,by decide,by simpa using hF⟩
      (Theory.PSL2.not_eight_dvd_card_of_small_mod_eight (hF ▸ ho) (hF ▸ hmod))
      (U.mapSurjective (f := j.toMonoidHom) j.surjective)
    exact (Nat.card_congr (j.subgroupMap U).toEquiv).trans hh
  have hi : (K.pCoreIn 2).relIndex S = 16 := by
    rw [←quotientImage_card (show S ≤ K from inf_le_right)]
    change Nat.card (quotientImage K ((T : Subgroup G) ⊓ K)) = 16
    unfold quotientImage
    rw [inf_subgroupOf_right]
    change Nat.card (quotientImage (enlargedResidual T L H) (T : Subgroup G)) = 16
    rw [←hU]
    exact h16
  have hmul := relIndex_mul_relIndex (K.pCoreIn 2) B S hQB hBS
  rw [hfour,hi] at hmul
  change B.relIndex S = 4
  omega

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- Both original contracts, or the original collapsed configuration with its
exact core indices. No local exclusion or normalizer premise is added. -/
theorem sourceContracts_or_cubicCoreIndices (hchoice : Selection.ModuleChoiceAt T) :
    (StabilizerNormalizerAt T ∧ HalfSylowUniqueAt T) ∨
      ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        SourceCubicNormalizerEnlargement D ∧
        ∃ (H P I : Subgroup G) (p : ℕ), Data D H ∧
          SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
            (residual H) P (enlargement T L H) I ∧
          enlargedResidual T L H = componentOrbit I (T : Subgroup G) ∧
          p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient I) 2 p ∧
          (p % 24 = 11 ∨ p % 24 = 13) ∧
          (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2 ∧
          ((enlargedResidual T L H).pCoreIn 2).relIndex
            ((residual H ⊔ ((T : Subgroup G) ⊓ enlargedResidual T L H)).pCoreIn 2) = 4 ∧
          ((residual H ⊔ ((T : Subgroup G) ⊓ enlargedResidual T L H)).pCoreIn 2).relIndex
            ((T : Subgroup G) ⊓ enlargedResidual T L H) = 4 := by
  rcases sourceContracts_or_cubicNormalizerEnlargement hchoice with hh | ⟨L,D,hc⟩
  · exact Or.inl hh
  · right
    refine ⟨L,D,hc,?_⟩
    obtain ⟨_,_,_,hn,_,_,_,_,H,P,I,p,h,hs,hK,hp,ho,hm,hmod,h24,_,_,_,hcollapse⟩ := hc
    exact ⟨H,P,I,p,h,hs,hK,hp,ho,hm,h24,hcollapse,
      h.collapsed_parabolic_core_relIndex hn hs hK hp ho hm hmod hcollapse⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
