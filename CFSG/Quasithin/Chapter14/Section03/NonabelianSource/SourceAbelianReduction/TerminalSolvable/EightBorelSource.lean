module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelNormalizer
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.SpecificGroups.SL2.BorelJoin
public import CFSG.Quasithin.Chapter14.Section02.NormalF11

/-!
# Original eight-row applicability of the large-parabolic source

For the actual component K, perfectness and normalization by T identify the
embedded O² of H = K join T with K. The rank-one Borel overgroup theorem makes
H minimal outside M when its Borel lies in M. The intrinsic quotient equivalence
then transports to O²(H), and the genuine normal F.1.1 construction applies.

The noncontainment theorem here remains conditional on the earlier 14.2.7
classification of that minimal parabolic. Its discharge and final assembly are
owned by qt-e-14315-eight-borel-exclusion; neither T ≤ K nor ambient recognition
is hidden in the applicability hypotheses.

Source: Aschbacher--Smith 14.3.6(1),14.3.15, printed pp.991,994
(`refs/quasithin.pdf`).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The exact `H(T,M)` and embedded residual conditions of 14.3.6, with
`H = K ⊔ T` and the original local component as `K₁`. -/
theorem eight_join_source_applicability
    {T : Sylow 2 G} {M : Subgroup G}
    {F : InvariantFlag T (rankTwoSeed T M) 2} {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) (h8 : EightImageRow F K) (hout : ¬ K ≤ M) :
    (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      K ⊔ (T : Subgroup G) ∈ Chapter1.HOver G (T : Set G) ∧
      ¬ K ⊔ (T : Subgroup G) ≤ M ∧
      (pResidual 2 (K ⊔ (T : Subgroup G) : Subgroup G)).map
        (K ⊔ (T : Subgroup G)).subtype = K := by
  have hn : (T : Subgroup G) ≤ normalizer (K : Set G) := by
    have h := le_normalizer_conjugateSpanBy K (T : Subgroup G)
    rwa [← h8.1] at h
  have hKH : K ≤ K ⊔ (T : Subgroup G) := le_sup_left
  let : Group.IsPerfect (K.subgroupOf (K ⊔ (T : Subgroup G))) := hK.local_component.1.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKH).toMonoidHom) (subgroupOfEquivOfLe hKH).surjective
  have hp : IsPPerfect 2 K := by
    intro N hN hq
    let : N.Normal := hN
    by_contra hne
    let : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (K ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (K ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (K ⧸ N) inferInstance
  refine ⟨hn, ⟨?_, fun _ hx => mem_sup_right hx⟩, fun h => hout (le_sup_left.trans h),
    embedded_pResidual_join_pGroup K (T : Subgroup G) hp T.isPGroup' hn⟩
  intro hb
  exact hK.local_component.2 ((map_eq_bot_iff_of_injective
    (pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G))
    (K ⊔ (T : Subgroup G)).subtype_injective).mp hb)

/-- In the rank-one eight-row case, Borel containment makes the actual
join a minimal outside member. This does not assume `T ≤ K`. -/
theorem eight_join_mem_HStar_of_borel_le
    {T : Sylow 2 G} {M : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    {F : InvariantFlag T (rankTwoSeed T M) 2} {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) (h8 : EightImageRow F K) (hout : ¬ K ≤ M)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (hB : (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype ≤ M) :
    K ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) M := by
  obtain ⟨hn,hH,hHM,_⟩ := eight_join_source_applicability hK h8 hout
  let e := eK.trans (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).symm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    ext k
    change e (QuotientGroup.mk k) = 1 ↔ k ∈ pCore 2 K
    rw [e.map_eq_one_iff,QuotientGroup.eq_one_iff]
  refine ⟨⟨hH,hHM⟩,?_⟩
  intro Y hY hYH
  by_contra hHY
  exact hY.2 ((Matrix.SpecialLinearGroup.proper_overgroup_join_le_borel_sup
    T K hn q hq (by rw [hk]; exact pCore_isPGroup) Y hY.1.2 (lt_of_le_not_ge hYH hHY)).trans
      (sup_le hB hTM))

/-- Transport the independently supplied core quotient along the actual
embedded residual equality, rather than identifying only a dotted image. -/
theorem eight_join_residual_quotient
    {T : Sylow 2 G} {M : Subgroup G}
    {F : InvariantFlag T (rankTwoSeed T M) 2} {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) (h8 : EightImageRow F K) (hout : ¬ K ≤ M)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3) :
    Nonempty (((pResidual 2 (K ⊔ (T : Subgroup G) : Subgroup G)) ⧸
      pCore 2 (pResidual 2 (K ⊔ (T : Subgroup G) : Subgroup G))) ≃*
        Theory.PSL2.BinaryGroup 3) := by
  let H := K ⊔ (T : Subgroup G)
  have he : (pResidual 2 H).map H.subtype = K :=
    (eight_join_source_applicability hK h8 hout).2.2.2
  let a : pResidual 2 H ≃* K :=
    ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr he)
  exact ⟨(a.toMonoidHom.pCoreQuotientEquiv (p := 2) a.surjective
    (IsPGroup.ker_isPGroup_of_injective a.injective)).trans eK⟩

/-- Conditional 14.3.6(1) for the eight row. The remaining premise is the
specialized earlier 14.2.7 classification of actual minimal parabolics.
It is not discharged by the applicability or amalgam constructions. -/
theorem eight_borel_not_le_of_large_parabolic
    {T : Sylow 2 G} {M : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    {F : InvariantFlag T (rankTwoSeed T M) 2} {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) (h8 : EightImageRow F K) (hout : ¬ K ≤ M)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (hlarge : ∀ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) M →
      Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃*
        Theory.PSL2.BinaryGroup 3) → ClassificationModels.IsTheoremEModel G) :
    ¬ (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype ≤ M := by
  intro hB
  exact hnot (hlarge _ (eight_join_mem_HStar_of_borel_le hTM hK h8 hout eK hB)
    (eight_join_residual_quotient hK h8 hout eK))

/-- Apply the genuine original normal-Bender theorem to the actual eight-row
join. All F.1.1 clauses, the residual commutator and both Borel identities
are obtained from the original source hypotheses. Recognition remains open. -/
theorem source_eight_join_amalgam
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    {F : InvariantFlag T (rankTwoSeed T M) 2} {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) (h8 : EightImageRow F K) (hout : ¬ K ≤ M)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3) :
    K ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) M ∧
      let Y := sourceResidual M Mc
      let S₂ := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K)
      ChapterF.Source.HypothesisF11 ![K,Y ⊔ S₂] (T : Subgroup G) ∧
        Y = ⁅Y,S₂⁆ ∧ ChapterF.Source.borel K (T : Subgroup G) = M ⊓ K ∧
        ChapterF.Source.borel (Y ⊔ S₂) (T : Subgroup G) = S₂ := by
  obtain ⟨hn,_,_,hres⟩ := eight_join_source_applicability hK h8 hout
  have hB := (source_eight_borel_placement hG T hempty hM hu hmany hcard e K hn eK).trans inf_le_left
  have hstar := eight_join_mem_HStar_of_borel_le hM.1.2 hK h8 hout eK hB
  refine ⟨hstar,?_⟩
  dsimp only
  let H := K ⊔ (T : Subgroup G)
  let KH := K.subgroupOf H
  have hKH : K ≤ H := le_sup_left
  have hTH : (T : Subgroup G) ≤ H := le_sup_right
  have hres' : pResidual 2 H = KH := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hKH]
    exact hres
  let : KH.Normal := hres' ▸ inferInstance
  have hgen : KH ⊔ (T.subtype hstar.1.1.2 : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hKH,
      show (T.subtype hstar.1.1.2 : Subgroup H) = (T : Subgroup G).subgroupOf H from rfl,
      map_subgroupOf_eq_of_le hTH, ← MonoidHom.range_eq_map, range_subtype]
  let a : KH ≃* K := subgroupOfEquivOfLe hKH
  let aq := a.toMonoidHom.pCoreQuotientEquiv (p := 2) a.surjective
    (IsPGroup.ker_isPGroup_of_injective a.injective)
  have hq : ChapterF.Source.IsRankOneModel (KH ⧸ pCore 2 KH) :=
    .linear 3 (by decide) ⟨GaloisField 2 3,inferInstance,inferInstance,
      GaloisField.card 2 3 (by decide),⟨aq.trans eK⟩⟩
  have hF := source_normal_bender_hypothesis_F_1_1
    hG T hempty hM hu hmany hcard e H hstar KH hgen hres' hq
  have hmap : KH.map H.subtype = K := map_subgroupOf_eq_of_le hKH
  simpa only [hmap, inf_eq_left.mpr hn] using And.intro hF.1 hF.2.2

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
