module
public import CFSG.Quasithin.Chapter14.Section03.EmptyFamilySieve.InvariantCubicPlacement
public import Theory.SpecificGroups.Alternating.FiveSylowMaximal
public import CFSG.Quasithin.Chapter14.Section02.OutsideParabolic
public import Theory.GroupTheory.PResidual.SylowSupplement
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.Preparation

/-!
# The original normalized A₅ component and its minimal parabolic

The A₅ Sylow normalizer has relative index three and is invariant under
all automorphisms preserving the Sylow subgroup. The proved original
14.3.5 therefore places its literal lift in M. Every proper overgroup
of T in KT lies in this Borel times T, by the unique maximal overgroup
property of the A₅ Sylow subgroup. Consequently KT is minimal outside M
when K is outside M. Perfectness identifies its embedded two-residual
with K, and the original minimal-parabolic theorem supplies its local
characteristic-two condition.

The terminal consumer obtains the A₅ marking from the canonical radical
quotient and an explicit radical/two-core equality. This equality and
the rank-one Borel noncontainment of 14.3.6(1) remain source obligations.
These reductions do not assert the completed A₅ exclusion in 14.3.15.
At no point does T-normalization of K become the false containment T ≤ K.

Source: Aschbacher--Smith, original 14.2.2(8), 14.3.5--6 and 14.3.15,
printed pp.981--982, 991--992 and 994; A₅ = L₂(4) and its Sylow Borel.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open EmptyFamilySieve
variable {G : Type*} [Group G] [Finite G]

private theorem five_sylow_normalizer_index (P : Sylow 2 (alternatingGroup (Fin 5))) :
    (P : Subgroup (alternatingGroup (Fin 5))).relIndex (normalizer ((P : Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5)))) = 3 := by
  have hcP : Nat.card P = 4 := by
    rw [P.card_eq_multiplicity,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
    decide +kernel
  obtain ⟨i, hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer P
  change normalizer ((P : Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5))) = _ at hi
  have hcN : Nat.card (normalizer ((P : Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5)))) = 12 := by
    rw [hi,Nat.card_eq_fintype_card]
    have h : ∀ j : Fin 5, Fintype.card (MulAction.stabilizer (alternatingGroup (Fin 5)) j) = 12 := by
      decide +kernel
    exact h i
  have hc := ((P : Subgroup (alternatingGroup (Fin 5))).subgroupOf
    (normalizer ((P : Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5))))).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show (P : Subgroup (alternatingGroup (Fin 5))) ≤ normalizer ((P : Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5))) from (P : Subgroup (alternatingGroup (Fin 5))).le_normalizer)).toEquiv,hcP,hcN] at hc
  change 4 * (P : Subgroup (alternatingGroup (Fin 5))).relIndex (normalizer ((P : Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5)))) = 12 at hc
  omega

/-- Original index-three placement for the literal Borel of a normalized A₅ section. -/
theorem source_single_a5_borel_le
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (K : Subgroup G) (hK : K ∈ MainForward.localComponents T)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype ≤ M := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hn
  let q : K →* alternatingGroup (Fin 5) := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  let S : Sylow 2 (alternatingGroup (Fin 5)) := P.mapSurjective hq
  have hB := source_invariant_cubic_le_image hG T hempty hM hu hmany hcard e hnot
    K hK hn eK P hP (normalizer ((S : Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5)))) (by
      change (S : Subgroup (alternatingGroup (Fin 5))) ≤ normalizer ((S : Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5)))
      exact (S : Subgroup (alternatingGroup (Fin 5))).le_normalizer)
    (five_sylow_normalizer_index S) (by
      intro a ha
      change (normalizer (((P : Subgroup K).map q) : Set _)).map a.toMonoidHom = _
      rw [map_equiv_normalizer_eq,ha]
      rfl)
  have hk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
  have hkM : q.ker ≤ M.subgroupOf K := by
    rw [hk]
    apply (pCore_isPGroup.le_sylow_of_normal P).trans
    rw [hP]
    exact fun _ hx => hM.1.2 hx
  apply map_le_iff_le_comap.mpr
  change normalizer ((T : Subgroup G).subgroupOf K : Set K) ≤ M.subgroupOf K
  rw [←hP]
  have hb : (normalizer (P : Set K)).map q ≤ (M.subgroupOf K).map q := by
    rw [P.normalizer_map_surjective q hq]
    exact hB
  have hh := map_le_iff_le_comap.mp hb
  rwa [comap_map_eq,sup_eq_left.mpr hkM] at hh

/-- Every proper overgroup of T in KT lies in the literal Borel times T. -/
theorem single_a5_proper_overgroup_le_borel_join
    (T : Sylow 2 G) (K : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (J : Subgroup G) (hTJ : (T : Subgroup G) ≤ J) (hJ : J < K ⊔ (T : Subgroup G)) :
    J ≤ (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype ⊔
      (T : Subgroup G) := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hn
  let q : K →* alternatingGroup (Fin 5) := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker ≤ (P : Subgroup K) := by
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal P
  have hPJ : (P : Subgroup K) ≤ J.subgroupOf K := by
    rw [hP]
    exact fun _ hx => hTJ hx
  have hjq : (J.subgroupOf K).map q ≠ ⊤ := by
    intro he
    have hjtop : J.subgroupOf K = ⊤ := by
      have hh := congrArg (Subgroup.comap q) he
      rwa [comap_map_eq,sup_eq_left.mpr (hk.trans hPJ),comap_top] at hh
    apply hJ.not_ge
    refine sup_le ?_ hTJ
    intro k hk
    exact show (⟨k,hk⟩ : K) ∈ J.subgroupOf K from hjtop ▸ mem_top _
  have hjN := Theory.SpecificGroups.Alternating.FiveSylowMaximal.overgroup_le_sylow_normalizer
    (P.mapSurjective hq) ((J.subgroupOf K).map q) (map_mono hPJ) hjq
  have hjB : J.subgroupOf K ≤ normalizer (P : Set K) := by
    change (J.subgroupOf K).map q ≤ normalizer ((P : Subgroup K).map q : Set _) at hjN
    rw [←P.normalizer_map_surjective q hq] at hjN
    have hh := map_le_iff_le_comap.mp hjN
    change J.subgroupOf K ≤ ((normalizer ((P : Subgroup K) : Set K)).map q).comap q at hh
    rwa [comap_map_eq,sup_eq_left.mpr (hk.trans (P : Subgroup K).le_normalizer)] at hh
  intro x hx
  have hxKT : x ∈ (K : Set G) * ((T : Subgroup G) : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left K (T : Subgroup G) hn]
    exact hJ.le hx
  obtain ⟨k,hk,t,ht,rfl⟩ := hxKT
  have hkJ : k ∈ J := by
    simpa only [mul_inv_cancel_right] using J.mul_mem hx (J.inv_mem (hTJ ht))
  apply mul_mem_sup ?_ ht
  apply mem_map.mpr
  refine ⟨⟨k,hk⟩,?_,rfl⟩
  rw [←hP]
  exact hjB hkJ

/-- The literal KT is minimal outside M once the cubic Borel is placed. -/
theorem source_single_a5_join_mem_HStar
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (K : Subgroup G) (hK : K ∈ MainForward.localComponents T)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) (hout : ¬K ≤ M) :
    K ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) M := by
  have hb := source_single_a5_borel_le hG T hempty hM hu hmany hcard e hnot K hK hn eK
  refine ⟨⟨⟨?_,show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right⟩,fun hh => hout (le_sup_left.trans hh)⟩,?_⟩
  · intro he
    exact hK.2 ((map_eq_bot_iff_of_injective (pCore 2 ↥(K ⊔ (T : Subgroup G)))
      (K ⊔ (T : Subgroup G)).subtype_injective).mp he)
  · intro J hJ hJK
    by_contra hne
    exact hJ.2 ((single_a5_proper_overgroup_le_borel_join T K hn eK J hJ.1.2
      (lt_of_le_of_ne hJK (fun he => hne he.ge))).trans (sup_le hb hM.1.2))

/-- The original normalized component is the embedded two-residual of KT. -/
theorem single_component_join_residual
    (T : Sylow 2 G) (K : Subgroup G) (hK : K ∈ MainForward.localComponents T)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    (pResidual 2 (K ⊔ (T : Subgroup G) : Subgroup G)).map
      (K ⊔ (T : Subgroup G)).subtype = K := by
  let d := subgroupOfEquivOfLe (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)
  let : Group.IsPerfect (K.subgroupOf (K ⊔ (T : Subgroup G))) := hK.1.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := d.toMonoidHom) d.surjective
  apply embedded_pResidual_join_pGroup K (T : Subgroup G) ?_ T.isPGroup' hn
  intro N hN hp
  let := hN
  let := hp.isNilpotent
  exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)


open Chapter12.Section08 Chapter12.Section08.InvariantFlag

/-- The literal terminal A₅ component gives an original minimal outside
parabolic as soon as its radical is identified with its intrinsic two-core.
The quotient marking is constructed from the canonical terminal map. -/
theorem source_terminal_single_a5_parabolic_of_radical
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    {F : InvariantFlag T (rankTwoSeed T M) 2} {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hR : solvableRadical K = pCore 2 K) :
    let H := K ⊔ (T : Subgroup G)
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧
      H ∈ Chapter3.HStar (T : Subgroup G) M ∧
      (pResidual 2 H).map H.subtype = K ∧ (K.subgroupOf H).Normal ∧
      ChapterB.IsMinimalParabolicOver T H ∧ generalizedFitting H = pCore 2 H ∧
      (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype ≤ M := by
  let eK := ((QuotientGroup.quotientMulEquivOfEq hR.symm).trans
    (hK.radicalQuotientEquiv (Or.inl ⟨e5⟩))).trans e5
  have hn : (T : Subgroup G) ≤ normalizer (K : Set G) := by
    have hh := le_normalizer_conjugateSpanBy K (T : Subgroup G)
    rwa [←hspan] at hh
  have hs := source_single_a5_join_mem_HStar hG T hempty hM hu hmany hcard e hnot
    K hK.local_component hn eK (hK.not_le hM.1.2 e)
  have hp := source_lemma_14_2_2_8_minimal hG T hempty hM hu hmany hcard e _ hs
  exact ⟨⟨eK⟩,hs,single_component_join_residual T K hK.local_component hn,
    (normal_subgroupOf_iff_le_normalizer (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)).mpr
      (sup_le K.le_normalizer hn),hp.1,hp.2.2.2.2.1,
    source_single_a5_borel_le hG T hempty hM hu hmany hcard e hnot
      K hK.local_component hn eK⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
