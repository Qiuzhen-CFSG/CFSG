module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondaryComponentSource
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentActionNormalizer
public import Theory.SpecificGroups.Alternating.FourPairCore
public import Theory.ElementaryAbelian.Injective

/-!
# Faithful residual action in the secondary alternating-five centralizer

The residual A4 normalizes each ordinary component of the distinguished
involution centralizer. Its marked core involution induces the original
nontrivial 1.1.5 automorphism, so the action is faithful. The actual subgroup
of index at most two in the secondary Sylow controls its action normalizer.
The final theorem applies this action to the original selected source data.

Source: Aschbacher--Smith, proof of 2.4.29, printed pp.545--546.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter2
open ChapterC

private theorem cubic_block_of_equiv
    {A : Type*} [Group A] [Finite A] (hp : IsPPerfect 2 A)
    (e : A ≃* alternatingGroup (Fin 4)) :
    IsAlternatingBlock A 3 ∧ pCore 2 A = blockU A := by
  let eC : pCore 2 A ≃* pCore 2 (alternatingGroup (Fin 4)) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  have hc : Nat.card (pCore 2 A) = 4 := by
    rw [Nat.card_congr eC.toEquiv,AlternatingFourPair.twoCore_eq_kleinFour]
    exact alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num)
  have he4 : IsElementaryAbelian 2 (pCore 2 (alternatingGroup (Fin 4))) := by
    rw [AlternatingFourPair.twoCore_eq_kleinFour]
    let hk := alternatingGroup.kleinFour_isKleinFour (by norm_num : Nat.card (Fin 4)=4)
    exact { toIsMulCommutative := hk.isMulCommutative
            exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  let := he4
  have he : IsElementaryAbelian 2 (pCore 2 A) :=
    IsElementaryAbelian.of_injective eC.toMonoidHom eC.injective
  have hq : Nat.card (A ⧸ pCore 2 A) = 3 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (pCore 2 A)
    rw [hc,Nat.card_congr e.toEquiv,alternatingGroup.card_of_card_eq_four (by norm_num)] at hh
    omega
  have hb := ChapterC.RankOne.Solvable.MinimalParabolic.alternatingThree_of_elementary_four_core
    hp he hc hq
  exact ⟨hb,hb.2.1.core_eq_blockU_of_quotient_three hq⟩

variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (u : G) (hu : orderOf u=2)

include hG hu in
/-- The actual two-residual of the marked centralizer normalizes every ordinary component. -/
theorem secondary_component_residual_normalizes
    (L K : Subgroup (centralizer ({u} : Set G)))
    (hL : IsPPerfect 2 L) (hK : IsComponent (centralizer ({u} : Set G)) K) :
    L ≤ normalizer (K : Set (centralizer ({u} : Set G))) := by
  let C := centralizer ({u} : Set G)
  have hs := hG.twoLocal_sqtk (isTwoLocal_involution_centralizer hu)
  have hQ : IsSQTK KnownSimple.IsKnownSimple (C ⧸ pCore 2 C) := by
    refine ⟨?_,hs.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hs.stronglyQuasithin p hp ho)
  exact Chapter1.Section02.twoPerfect_normalizes_cComponent_source hQ hK.isCComponent hL

/-- The marked involution in the residual four makes the canonical A4 action faithful. -/
theorem secondary_component_faithful_residual_action
    (P : Sylow 2 (centralizer ({u} : Set G))) (M : Subgroup G) (z : G)
    (h115 : Chapter1.Lemma115Hypotheses (centralizer ({u} : Set G)) P M z)
    (L K : Subgroup (centralizer ({u} : Set G)))
    (hL : IsPPerfect 2 L) (hK : IsComponent (centralizer ({u} : Set G)) K)
    (e : L ≃* alternatingGroup (Fin 4))
    (a : L) (ha : a ∈ pCore 2 L) (hz : z=((a : centralizer ({u} : Set G)):G)*u) :
    let hn := secondary_component_residual_normalizes hG u hu L K hL hK
    let f := K.normalizerMonoidHom.comp (inclusion hn)
    Function.Injective f ∧ ∀ (l : L) (k : K),
      ((f l k : centralizer ({u} : Set G)):G)=(l:G)*(k:G)*(l:G)⁻¹ := by
  dsimp only
  let C := centralizer ({u} : Set G)
  have hn := secondary_component_residual_normalizes hG u hu L K hL hK
  let f : L →* MulAut K := K.normalizerMonoidHom.comp (inclusion hn)
  have hact (l : L) (k : K) : ((f l k : C):G)=(l:G)*(k:G)*(l:G)⁻¹ := rfl
  obtain ⟨_,α,_,hα,mark,_⟩ := h115.component_inputs K hK
  have hfa : f a=α := by
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    apply Subtype.ext
    have hku : u*(k:G)*u⁻¹=(k:G) := by
      rw [←mem_centralizer_singleton_iff.mp (k:C).property,mul_inv_cancel_right]
    calc
      ((f a k:C):G)=(a:G)*(k:G)*(a:G)⁻¹ := hact a k
      _=(a:G)*(u*(k:G)*u⁻¹)*(a:G)⁻¹ := by rw [hku]
      _=((α k:C):G) := by rw [hα,hz]; group
  have hm : f a≠1 := by
    intro hh
    have ho := mark.order_two
    rw [←hfa,hh,orderOf_one] at ho
    norm_num at ho
  obtain ⟨hb,hcore⟩ := cubic_block_of_equiv hL e
  exact ⟨hb.injective_of_moves_module f a (hcore ▸ ha) hm,hact⟩

include hG hu in
/-- The original index-two subgroup controls the canonical actor normalizer before absorption. -/
theorem secondary_component_residual_action_normalizer_bound
    (P : Sylow 2 (centralizer ({u} : Set G)))
    (L R K : Subgroup (centralizer ({u} : Set G)))
    (hL : IsPPerfect 2 L) (hK : IsComponent (centralizer ({u} : Set G)) K)
    (hRL : R ≤ normalizer (L : Set (centralizer ({u} : Set G))))
    (hri : R.relIndex (P : Subgroup (centralizer ({u} : Set G))) ≤ 2) :
    let C := centralizer ({u} : Set G)
    let N := normalizer (K : Set C)
    let B := (L.subgroupOf N).map K.normalizerMonoidHom
    ∃ Q : Sylow 2 N, (Q : Subgroup N)=(P : Subgroup C).subgroupOf N ∧
      (normalizer (B : Set (MulAut K))).relIndex
        ((Q : Subgroup N).map K.normalizerMonoidHom)≤2 := by
  dsimp only
  let C := centralizer ({u} : Set G)
  let N := normalizer (K : Set C)
  have hs := hG.twoLocal_sqtk (isTwoLocal_involution_centralizer hu)
  have hQ : IsSQTK KnownSimple.IsKnownSimple (C ⧸ pCore 2 C) := by
    refine ⟨?_,hs.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hs.stronglyQuasithin p hp ho)
  have hn : N.Normal := by
    rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ hK.isCComponent with hk | hi
    · let := hk
      change (normalizer (K : Set C)).Normal
      rw [normalizer_eq_top]
      infer_instance
    · exact N.normal_of_index_eq_two hi
  let := hn
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_normal N
  have hLN := secondary_component_residual_normalizes hG u hu L K hL hK
  have hRN : R.subgroupOf N ≤ normalizer (L.subgroupOf N : Set N) := by
    rw [←subgroupOf_normalizer_eq hLN]
    exact comap_mono hRL
  have hir : (R.subgroupOf N).relIndex (Q : Subgroup N)≤2 := by
    rw [hQ]
    change (R.comap N.subtype).relIndex ((P : Subgroup C).subgroupOf N)≤2
    rw [relIndex_comap]
    exact (relIndex_le_of_le_right
      (show ((P : Subgroup C).subgroupOf N).map N.subtype≤(P : Subgroup C) from by
        rintro _ ⟨x,hx,rfl⟩
        exact hx)
      (show R.relIndex (P : Subgroup C)≠0 from index_ne_zero_of_finite)).trans hri
  refine ⟨Q,hQ,?_⟩
  rw [←relIndex_comap]
  apply le_trans (relIndex_le_of_le_left ?_
    (show (R.subgroupOf N).relIndex (Q : Subgroup N)≠0 from index_ne_zero_of_finite)) hir
  intro r hr
  exact (L.subgroupOf N).le_normalizer_map K.normalizerMonoidHom
    (mem_map_of_mem K.normalizerMonoidHom (hRN hr))

include hG hu in
/-- The faithful action on an actual selected component uses the original marked 1.1.5 producer. -/
theorem MinimalBlockSetup.single_alternating_secondary_faithful_residual_of_marks
    {M : Subgroup G} (d : MinimalBlockSetup M)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N=M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0=d.block) (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (huR : u ∈ (center (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))).map
      (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).subtype)
    (hout : ¬d.H ⊓ centralizer ({u}:Set G) ≤ M)
    (hMu : M ⊓ centralizer ({u}:Set G)=(T : Subgroup G) ⊓ centralizer ({u}:Set G))
    (hi : ((T : Subgroup G) ⊓ centralizer ({u}:Set G)).relIndex (T : Subgroup G)=2)
    (P : Sylow 2 (centralizer ({u}:Set G)))
    (hP : (P : Subgroup (centralizer ({u}:Set G))).map (centralizer ({u}:Set G)).subtype=
      (T : Subgroup G) ⊓ centralizer ({u}:Set G))
    (z : G) (hz : z ∈ (center (T : Subgroup G)).map (T : Subgroup G).subtype)
    (hz2 : orderOf z=2)
    (L K : Subgroup (centralizer ({u}:Set G)))
    (hL : IsPPerfect 2 L) (hK : IsComponent (centralizer ({u}:Set G)) K)
    (e : L ≃* alternatingGroup (Fin 4))
    (a : L) (ha : a ∈ pCore 2 L) (hza : z=(a:G)*u) :
    ∃ f : L →* MulAut K, Function.Injective f ∧ ∀ (l : L) (k : K),
      ((f l k : centralizer ({u}:Set G)):G)=(l:G)*(k:G)*(l:G)⁻¹ := by
  have h115 := d.single_alternating_secondary_lemma115_of_marks hG T hM hTM hunique hST
    hsingle hA u hu huR hout hMu hi P hP z hz hz2
  have hh := secondary_component_faithful_residual_action hG u hu P M z h115 L K hL hK e a ha hza
  exact ⟨_,hh⟩

end CFSG.Quasithin.Chapter2
