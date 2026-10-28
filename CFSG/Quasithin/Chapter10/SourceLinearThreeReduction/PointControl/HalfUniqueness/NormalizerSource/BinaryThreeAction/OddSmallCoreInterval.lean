module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallModuleAction
public import Theory.GroupTheory.NormalThreeJoinCore
public import Theory.SpecificGroups.PSL2.SmallSylowCentralizer

/-!
# The actual core interval in the collapsed odd-prime configuration

Write X=O²(H), K=<X^E>, and S=T∩K for the original source parabolic and
normalizer enlargement. If O₂(X)≤O₂(K), the image of X is its original
cubic complement image P, normalized by the full quotient Sylow. Hence
O₂(XS) has quotient image C_S(P), which is strictly smaller than S because
the quotient Sylow is self-centralizing. Both O₂(XS)=S and N_K(S)=XS
therefore fail under this collapse.

The consumer retains every original source guard and both requested
contracts. This identifies the precise obstruction to applying the two
identities in the small-congruence step on printed p.748; it does not
construct a counterexample to the full ambient source theorem. Excluding
the collapsed configuration using the original module and ambient hypotheses
remains with qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is the only
external premise, finally discharged by qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 10.2.5--6, printed pp.748--749.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Subgroup Theory.GroupTheory Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H P I : Subgroup G}

/-- The embedded parabolic two-core commutes with the literal containing quotient map. -/
theorem Data.quotient_parabolic_core_eq_image (h : Data D H) :
    (quotientImage (enlargedResidual T L H) (residual H) ⊔
      quotientImage (enlargedResidual T L H) (T : Subgroup G)).pCoreIn 2 =
    quotientImage (enlargedResidual T L H)
      ((residual H ⊔ ((T : Subgroup G) ⊓ enlargedResidual T L H)).pCoreIn 2) := by
  let K := enlargedResidual T L H
  let B := (residual H).subgroupOf K ⊔ (T : Subgroup G).subgroupOf K
  have hB : B.map K.subtype = residual H ⊔ ((T : Subgroup G) ⊓ K) := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le h.residual_le_enlargedResidual,
      subgroupOf_map_subtype]
  have hc : B.pCoreIn 2 =
      ((residual H ⊔ ((T : Subgroup G) ⊓ K)).pCoreIn 2).subgroupOf K := by
    rw [←hB,←map_pCoreIn_of_injective 2 B K.subtype K.subtype_injective]
    exact (comap_map_eq_self_of_injective K.subtype_injective _).symm
  have hm := map_pCoreIn_of_ker_isPGroup
    (QuotientGroup.mk' (pCore 2 K)) (by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) B
  rw [hc,Subgroup.map_sup] at hm
  exact hm.symm

/-- In the collapsed case the parabolic core image is the Sylow centralizer of the original cubic image. -/
theorem Data.collapsed_quotient_core_centralizer (h : Data D H)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    quotientImage (enlargedResidual T L H)
      ((residual H ⊔ ((T : Subgroup G) ⊓ enlargedResidual T L H)).pCoreIn 2) =
    quotientImage (enlargedResidual T L H) (T : Subgroup G) ⊓
      centralizer (quotientImage (enlargedResidual T L H) P :
        Set (XiQuotient (enlargedResidual T L H))) := by
  let K := enlargedResidual T L H
  obtain ⟨S,hS⟩ := h.quotient_sylow
  have hN : (S : Subgroup (XiQuotient K)) ≤ normalizer (quotientImage K P : Set _) := by
    rw [hS,←h.quotient_residual_eq_complement_of_core_le hi hc]
    apply (map_mono ?_).trans (le_normalizer_map (QuotientGroup.mk' (pCore 2 K)))
    rw [←subgroupOf_normalizer_eq h.residual_le_enlargedResidual]
    exact subgroupOf_mono K hi.invariant
  rw [←h.quotient_parabolic_core_eq_image,h.quotient_residual_eq_complement_of_core_le hi hc,←hS]
  exact Theory.GroupTheory.core_join_three_eq_sylow_centralizer _ S (hi.odd_complement.isPGroup.comap_subtype.map _) hN

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Subgroup Theory.GroupTheory Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H P I : Subgroup G}

/-- The collapsed parabolic core has strictly smaller image than the full quotient Sylow. -/
theorem Data.collapsed_quotient_core_lt_sylow (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 8 = 3 ∨ p % 8 = 5)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    quotientImage (enlargedResidual T L H)
      ((residual H ⊔ ((T : Subgroup G) ⊓ enlargedResidual T L H)).pCoreIn 2) <
    quotientImage (enlargedResidual T L H) (T : Subgroup G) := by
  let K := enlargedResidual T L H
  let A := quotientImage K P
  obtain ⟨S,hS⟩ := h.quotient_sylow
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hpc := hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))
  have hep : Nonempty (P ≃* A) := by
    change Nonempty (P ≃* quotientImage (enlargedResidual T L H) P)
    exact hK.symm ▸ ⟨SwappedSylow.quotientComplementEquiv hs.toSwappedInput⟩
  obtain ⟨ep⟩ := hep
  have hA : A ≠ ⊥ := by
    intro he
    have hh := Nat.card_congr ep.toEquiv
    rw [hpc.2,he,card_bot] at hh
    norm_num at hh
  have hN : (S : Subgroup (XiQuotient K)) ≤ normalizer (A : Set _) := by
    rw [hS,show A = quotientImage K (residual H) from
      (h.quotient_residual_eq_complement_of_core_le hs.toLocalInput hc).symm]
    apply (map_mono ?_).trans (le_normalizer_map (QuotientGroup.mk' (pCore 2 K)))
    rw [←subgroupOf_normalizer_eq h.residual_le_enlargedResidual]
    exact subgroupOf_mono K hs.invariant
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p,1,hp,ho,by decide,by simpa using hF⟩
  have h8 := Theory.PSL2.not_eight_dvd_card_of_small_mod_eight (hF ▸ ho) (hF ▸ hmod)
  have hself := Theory.PSL2.small_pair_self_centralizing_of_equiv (e.trans (eF.prodCongr eF)) hodd h8 S
  rw [←h.quotient_parabolic_core_eq_image,h.quotient_residual_eq_complement_of_core_le hs.toLocalInput hc,←hS]
  exact Theory.GroupTheory.core_join_three_lt_selfCentralizing_sylow A S (hs.odd_complement.isPGroup.of_equiv ep) hA hself hN

/-- In the collapsed source case the two-core equality printed in the
small-congruence step cannot hold. This is a necessary condition on the
remaining configuration, not an exclusion of its original ambient hypotheses. -/
theorem Data.collapsed_parabolic_core_ne_sylow (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 8 = 3 ∨ p % 8 = 5)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    (residual H ⊔ ((T : Subgroup G) ⊓ enlargedResidual T L H)).pCoreIn 2 ≠
      (T : Subgroup G) ⊓ enlargedResidual T L H := by
  intro he
  have hh := (h.collapsed_quotient_core_lt_sylow hn hs hK hp ho hm hmod hc).ne
  apply hh
  rw [he]
  unfold quotientImage
  rw [inf_subgroupOf_right]

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Subgroup Theory.GroupTheory Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
open BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The remaining source obstruction has a strict core interval on the
same parabolic and the same quotient. No new model witness is selected. -/
theorem SourceCubicNormalizerEnlargement.exists_strict_core_interval
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hc : SourceCubicNormalizerEnlargement D) :
    ∃ (H P I : Subgroup G) (p : ℕ), Data D H ∧
      SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
        (residual H) P (enlargement T L H) I ∧
      enlargedResidual T L H = componentOrbit I (T : Subgroup G) ∧
      p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient I) 2 p ∧
      (p % 24 = 11 ∨ p % 24 = 13) ∧
      residual H < enlargedResidual T L H ∧
      stabilizerIntersection T L H = (T : Subgroup G) ⊓ enlargedResidual T L H ∧
      (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2 ∧
      quotientImage (enlargedResidual T L H)
        ((residual H ⊔ ((T : Subgroup G) ⊓ enlargedResidual T L H)).pCoreIn 2) <
        quotientImage (enlargedResidual T L H) (T : Subgroup G) := by
  obtain ⟨_,_,_,hn,_,_,_,_,H,P,I,p,h,hs,hK,hp,ho,hm,hmod,h24,_,hlt,hR,hc⟩ := hc
  exact ⟨H,P,I,p,h,hs,hK,hp,ho,hm,h24,hlt,hR,hc,
    h.collapsed_quotient_core_lt_sylow hn hs hK hp ho hm hmod hc⟩

/-- Both original contracts, or an original source configuration in which
the small-congruence core equality fails. This does not assert that the
second alternative is realizable in the simple ambient group. Its exclusion
and final assembly remain with the half-Sylow source owner. -/
theorem sourceContracts_or_strictCubicCoreInterval
    (hchoice : Selection.ModuleChoiceAt T) :
    (StabilizerNormalizerAt T ∧ HalfSylowUniqueAt T) ∨
      ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        SourceCubicNormalizerEnlargement D ∧
        ∃ H : Subgroup G, Data D H ∧
          (residual H ⊔ ((T : Subgroup G) ⊓ enlargedResidual T L H)).pCoreIn 2 ≠
            (T : Subgroup G) ⊓ enlargedResidual T L H := by
  rcases sourceContracts_or_cubicNormalizerEnlargement hchoice with hh | ⟨L,D,hc⟩
  · exact Or.inl hh
  · right
    refine ⟨L,D,hc,?_⟩
    obtain ⟨_,_,_,hn,_,_,_,_,H,P,I,p,h,hs,hK,hp,ho,hm,hmod,_,_,_,_,hcollapse⟩ := hc
    exact ⟨H,h,h.collapsed_parabolic_core_ne_sylow hn hs hK hp ho hm hmod hcollapse⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Subgroup Theory.GroupTheory Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H P I : Subgroup G}

/-- The normalizer identity in the same printed step also requires the
collapsed source case to be excluded first. The normalizer here is relative
to K, and the Sylow is the literal T ∩ K. -/
theorem Data.collapsed_parabolic_ne_sylow_normalizer (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 8 = 3 ∨ p % 8 = 5)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    residual H ⊔ ((T : Subgroup G) ⊓ enlargedResidual T L H) ≠
      enlargedResidual T L H ⊓ normalizer
        ((T : Subgroup G) ⊓ enlargedResidual T L H : Set G) := by
  intro he
  apply h.collapsed_parabolic_core_ne_sylow hn hs hK hp ho hm hmod hc
  apply le_antisymm
  · exact h.parabolic_intersection_core_le.trans
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  · apply le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left) le_sup_right
    exact he ▸ inf_le_right

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
