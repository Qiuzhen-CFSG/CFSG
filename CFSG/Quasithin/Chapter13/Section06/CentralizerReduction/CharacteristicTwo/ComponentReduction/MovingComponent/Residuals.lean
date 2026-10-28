module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.Actions
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PPerfectHom
public import Theory.SpecificGroups.PSL2.RankOneRoots
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Residual identities and the binary linear exclusion

The superscript residual identities in alternatives (i) and (iii) make the
component normal. A two-perfect group with cubic two-core quotient lies in
O^{3'} of its overgroup. For two commuting components, the second factor
vanishes in the first component's literal normalizer action. A two-perfect
action image centralizing a PSL2 involution is trivial because the actual
involution centralizer is a two-group. This contradicts [K,Lv] = K.

These deductions retain the residual equality supplied by source 1.2.2(a)
as a separate assembly obligation. They assert no model classification.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, 13.6.6, p.927.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent
variable {H : Type*} [Group H]

private theorem layer_characteristic : (componentLayer H).Characteristic := by
  apply characteristic_iff_map_le.mpr
  intro e
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro K hK
  exact map_le_iff_le_comap.mp (le_sSup (hK.map_equiv e))

theorem not_residual_identities (K T : Subgroup H)
    (hm : ¬ T ≤ normalizer (K : Set H)) :
    primeToResidual 3 H ≠ K ∧
      (primeToResidual 3 (componentLayer H)).map (componentLayer H).subtype ≠ K := by
  constructor
  · intro he
    exact hm (he ▸ (show T ≤ normalizer (primeToResidual 3 H : Set H) from
      le_normalizer_of_normal))
  · intro he
    let : (componentLayer H).Characteristic := layer_characteristic
    have : ((primeToResidual 3 (componentLayer H)).map (componentLayer H).subtype).Characteristic :=
      inferInstance
    exact hm (he ▸ (show T ≤ normalizer
      ((primeToResidual 3 (componentLayer H)).map (componentLayer H).subtype : Set H) from
        le_normalizer_of_normal))

theorem twoPerfect_cubic_le_residual [Finite H] (D : Subgroup H)
    (hD : IsPPerfect 2 D) (hc : Nat.card (D ⧸ pCore 2 D) = 3) :
    D ≤ primeToResidual 3 H := by
  let : IsSimpleGroup (D ⧸ pCore 2 D) := isSimpleGroup_of_prime_card hc
  exact le_primeToResidual_of_eq_top 3 D
    (primeToResidual_eq_top_of_simple_quotient 3 2 (pCore 2 D) pCore_isPGroup hD
      (by rw [hc]))

variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
open A5Module

theorem residual_twoPerfect (s : Marking L V) : IsPPerfect 2 (residual s) := by
  let e := subgroupOfEquivOfLe (Lv_le_Gv L (markedV s))
  exact (isPPerfect_embedded_pResidual 2 (L ⊓ Gv (markedV s))).of_surjective
    e.symm.toMonoidHom e.symm.surjective

theorem residual_le_cubic_residual (s : Marking L V)
    (hc : Nat.card (residual s ⧸ pCore 2 (residual s)) = 3) :
    residual s ≤ primeToResidual 3 (Gv (markedV s)) :=
  twoPerfect_cubic_le_residual (residual s) (residual_twoPerfect s) hc

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A two-perfect subgroup centralizing a binary PSL2 involution has trivial image. -/
theorem psl2_centralizing_image_trivial {D : Type*} [Group D]
    (hD : IsPPerfect 2 D) (f : D →* BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)
    (a : BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) (ha : orderOf a = 2)
    (hC : ∀ d, Commute (f d) a) : f = 1 := by
  obtain ⟨_, _, _, _, _, hp⟩ := Theory.PSL2.involution_root_geometry a ha
  let fC := f.codRestrict (centralizer {a}) (fun d =>
    mem_centralizer_singleton_iff.mpr (hC d).eq)
  have hf := hD.hom_eq_one_of_isPGroup hp fC
  ext d
  exact congrArg Subtype.val (DFunLike.congr_fun hf d)

omit [Finite G] in
/-- The image of the commuting second component vanishes in the literal action quotient. -/
theorem pair_image_le_component (K J D : Subgroup G) (hc : ⁅K, J⁆ = ⊥)
    (hDK : D ≤ K ⊔ J) :
    (D.subgroupOf (normalizer (K : Set G))).map (NormalizerAction.quotient K) ≤
      NormalizerAction.componentImage K := by
  rintro _ ⟨d, hd, rfl⟩
  apply NormalizerAction.quotient_mem_componentImage_of_central_supplement K J K
    (commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm J K).trans hc))
    K.le_normalizer (le_refl _) d
  rw [sup_comm]
  exact hDK hd

omit [Finite G] in
/-- Triviality of the genuine action image is centralization of K. -/
theorem centralizes_of_action_image_bot (K D : Subgroup G)
    (hDN : D ≤ normalizer (K : Set G))
    (himage : (D.subgroupOf (normalizer (K : Set G))).map
      (NormalizerAction.quotient K) = ⊥) : ⁅K, D⁆ = ⊥ := by
  rw [commutator_comm]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro d hd
  apply (NormalizerAction.quotient_eq_one_iff K ⟨d, hDN hd⟩).mp
  exact mem_bot.mp (himage ▸ (mem_map_of_mem (NormalizerAction.quotient K)
    (show (⟨d, hDN hd⟩ : normalizer (K : Set G)) ∈ D.subgroupOf _ from hd)))

/-- PSL2 is impossible once the actual residual lies in the two-component orbit. -/
theorem exclude_psl2_of_pair (s : Marking L V)
    (K J : Subgroup (Gv (markedV s))) (hc : ⁅K, J⁆ = ⊥)
    (hDN : residual s ≤ X K) (hDK : residual s ≤ K ⊔ J)
    (hKD : ⁅K, residual s⁆ ≠ ⊥)
    (a : NormalizerAction.componentImage K) (ha : orderOf a = 2)
    (haC : ∀ d : X K, (d : Gv (markedV s)) ∈ residual s →
      Commute (NormalizerAction.quotient K d) (a : XStar K))
    (e : NormalizerAction.componentImage K ≃*
      BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) : False := by
  have himage := pair_image_le_component K J (residual s) hc hDK
  let D := (residual s).subgroupOf (X K)
  let f : D →* NormalizerAction.componentImage K :=
    ((NormalizerAction.quotient K).comp D.subtype).codRestrict _
      (fun d => himage (mem_map_of_mem _ d.property))
  have hD : IsPPerfect 2 D := (residual_twoPerfect s).of_surjective
    (subgroupOfEquivOfLe hDN).symm.toMonoidHom (subgroupOfEquivOfLe hDN).symm.surjective
  have hf : e.toMonoidHom.comp f = 1 := psl2_centralizing_image_trivial hD
    (e.toMonoidHom.comp f) (e a) (by rw [e.orderOf_eq, ha]) (fun d =>
      (show Commute (f d) a from Subtype.ext (haC d d.property).eq).map e)
  apply hKD
  apply centralizes_of_action_image_bot K (residual s) hDN
  apply eq_bot_iff.mpr
  rintro _ ⟨d, hd, rfl⟩
  have he : f ⟨d, hd⟩ = 1 := e.injective
    ((DFunLike.congr_fun hf ⟨d, hd⟩).trans (map_one e).symm)
  exact congrArg Subtype.val he

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent
