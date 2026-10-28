module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsIntersectionResidual
public import Theory.SpecificGroups.Alternating.FourNormalProduct

/-!
# The first block of the literal quotient-centralizer residual

The original point action restricts to L_e with image A₄×A₃ and a two-group
kernel. The residual L₂ is normal in the full point normalizer. If its
first projection were not a two-group, the normal-product calculation
would put A₄×1 in its image. Two-perfection would then force L₁ into
C_G(K/O₂(K)), contradicting its nontrivial A₄ image in the centerless A₅.
Thus L₂ has trivial first-block action.

The cubic count and identification with the second block residual are
completed in TerminalProductLocalFactorsIdentification. ComponentAnalysis
remains the allowed premise discharged by qt-d-1231-terminal.
Source: Aschbacher--Smith, completion of 12.3.1, printed p.811.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

theorem Le_le_pointNormalizer
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (C : P.ComponentAnalysis) :
    P.Le ≤ P.pointNormalizer := by
  rw [P.Le_eq_pointNormalizer_primeToResidual structural C]
  exact map_subtype_le _

theorem pointNormalizer_normalizes_Le
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (C : P.ComponentAnalysis) :
    P.pointNormalizer ≤ normalizer (P.Le : Set G) := by
  rw [P.Le_eq_pointNormalizer_primeToResidual structural C]
  exact P.pointNormalizer.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ _)

theorem pointNormalizer_normalizes_L2
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (C : P.ComponentAnalysis) :
    P.pointNormalizer ≤ normalizer (P.L2 : Set G) :=
  ((le_inf (P.pointNormalizer_normalizes_Le structural C)
    ((inf_le_right.trans C.normalizes).trans P.quotientCentralizer_normalized)).trans
      inf_normalizer_le_normalizer_inf).trans
    (normalizer_le_normalizer_characteristic_image _ _)

theorem secondPointResidual_twoPerfect : IsPPerfect 2 P.secondPointResidual :=
  (isPPerfect_primeToResidual 3 2 (by decide)).of_surjective
    ((primeToResidual 3 P.secondPointFactor).equivMapOfInjective P.secondPointFactor.subtype
      P.secondPointFactor.subtype_injective).toMonoidHom
    ((primeToResidual 3 P.secondPointFactor).equivMapOfInjective P.secondPointFactor.subtype
      P.secondPointFactor.subtype_injective).surjective

theorem L2_twoPerfect : IsPPerfect 2 P.L2 :=
  isPPerfect_embedded_pResidual_of_finite 2 _

/-- The literal point-block map restricted to the two-residual. -/
def LeBlockAction
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (C : P.ComponentAnalysis) :
    P.Le →* (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 3)) :=
  P.pointBlockAction.comp (inclusion (P.Le_le_pointNormalizer structural C))

theorem LeBlockAction_twoKernel
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (C : P.ComponentAnalysis) :
    IsPGroup 2 (P.LeBlockAction structural C).ker := by
  have hRL : P.Le ≤ L := (map_subtype_le _).trans inf_le_left
  let f := P.LeBlockAction structural C
  have hπ (r : f.ker) : S.projection (inclusion hRL r.val) = 1 := by
    let n := inclusion (P.Le_le_pointNormalizer structural C) r.val
    have hn : D.model.pointPermutation P.point n = 1 :=
      (WeightFourLocal.pointEquiv _ P.weight_four).injective (r.property.trans (map_one _).symm)
    have hperm : D.model.permutation ⟨n,n.property.1⟩ = 1 := congrArg Subtype.val hn
    exact Subtype.ext ((D.component_action (inclusion hRL r.val)).symm.trans hperm)
  let j : f.ker →* pCore 2 L := ((inclusion hRL).comp f.ker.subtype).codRestrict _
    (fun r => (QuotientGroup.eq_one_iff _).mp
      ((P.twoCoreQuotientEquiv C).injective ((hπ r).trans (map_one _).symm)))
  exact pCore_isPGroup.of_injective j (by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 L => ((x : L) : G)) h)

theorem component_inf_quotientCentralizer_le_core (C : P.ComponentAnalysis) :
    P.K ⊓ P.quotientCentralizer ≤ P.K.pCoreIn 2 := by
  rintro x ⟨hxK,n,hn,he⟩
  have hxcenter : QuotientGroup.mk' (pCore 2 P.K) ⟨x,hxK⟩ ∈ center (P.K ⧸ pCore 2 P.K) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 P.K) y
    have h := DFunLike.congr_fun hn (QuotientGroup.mk' (pCore 2 P.K) k)
    change quotientAut (pCore 2 P.K) (P.K.normalizerMonoidHom n) _ = _ at h
    rw [quotientAut_apply_mk] at h
    have heq : P.K.normalizerMonoidHom n k = ⟨x,hxK⟩ * k * ⟨x,hxK⟩⁻¹ := by
      apply Subtype.ext
      change (n : G) * k * (n : G)⁻¹ = x * k * x⁻¹
      change (n : G) = x at he
      rw [he]
    rw [heq,map_mul,map_mul,map_inv] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  have hz : center (P.K ⧸ pCore 2 P.K) = ⊥ := by
    apply le_bot_iff.mp
    intro q hq
    apply mem_bot.mpr
    apply C.quotient.injective
    rw [map_one]
    have hm : C.quotient q ∈ center (alternatingGroup (Fin 5)) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨z,rfl⟩ := C.quotient.surjective y
      simpa only [map_mul] using congrArg C.quotient ((mem_center_iff.mp hq) z)
    rw [alternatingGroup.center_eq_bot (by simp)] at hm
    exact mem_bot.mp hm
  exact mem_map_of_mem P.K.subtype ((QuotientGroup.eq_one_iff _).mp (mem_bot.mp (hz ▸ hxcenter)))

theorem firstPointResidual_not_le_quotientCentralizer
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    ¬ P.firstPointResidual ≤ P.quotientCentralizer := by
  intro h
  have hK : P.firstPointResidual ≤ P.K := by
    rw [P.firstPointResidual_eq_L1 structural escape C]
    exact P.L1_le_component structural escape C
  have hp := (pCore_isPGroup.map P.K.subtype).to_le
    ((le_inf hK h).trans (P.component_inf_quotientCentralizer_le_core C))
  have ha := hp.of_surjective (P.firstResidualProjection structural escape)
    (P.firstResidualProjection_surjective structural escape)
  have hc : Nat.card (alternatingGroup (Fin 4)) = 12 := by
    rw [Nat.card_eq_fintype_card,card_alternatingGroup]; decide
  obtain ⟨n,hn⟩ := ha.exists_card_eq
  have hcop := (by decide : Nat.Coprime 3 2).pow_right n
  rw [←hn,hc] at hcop
  norm_num at hcop

theorem firstPointResidual_block_image
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    (P.firstPointResidual.subgroupOf P.pointNormalizer).map P.pointBlockAction =
      (alternatingGroup (Fin 4)).prod (⊥ : Subgroup (Equiv.Perm (Fin 3))) := by
  apply le_antisymm
  · rintro x ⟨n,hn,rfl⟩
    exact ⟨P.firstResidualPermutation_mem structural escape ⟨n,hn⟩,
      P.firstResidual_second_eq_one ⟨n,hn⟩⟩
  · rintro ⟨a,b⟩ ⟨ha,hb⟩
    obtain ⟨r,hr⟩ := P.firstResidualProjection_surjective structural escape ⟨a,ha⟩
    refine ⟨inclusion P.firstPointResidual_le_pointNormalizer r,r.property,?_⟩
    exact Prod.ext (congrArg Subtype.val hr)
      ((P.firstResidual_second_eq_one r).trans (mem_bot.mp hb).symm)

theorem secondPointResidual_block_image
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    (P.secondPointResidual.subgroupOf P.pointNormalizer).map P.pointBlockAction =
      (⊥ : Subgroup (Equiv.Perm (Fin 4))).prod (alternatingGroup (Fin 3)) := by
  apply le_antisymm
  · rintro x ⟨n,hn,rfl⟩
    exact ⟨P.secondResidual_first_eq_one ⟨n,hn⟩,
      P.secondResidualPermutation_mem structural escape ⟨n,hn⟩⟩
  · rintro ⟨a,b⟩ ⟨ha,hb⟩
    obtain ⟨r,hr⟩ := P.secondResidualProjection_surjective structural escape ⟨b,hb⟩
    refine ⟨inclusion P.secondPointResidual_le_pointNormalizer r,r.property,?_⟩
    exact Prod.ext ((P.secondResidual_first_eq_one r).trans (mem_bot.mp ha).symm)
      (congrArg Subtype.val hr)

theorem Le_block_image
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    (P.Le.subgroupOf P.pointNormalizer).map P.pointBlockAction =
      (alternatingGroup (Fin 4)).prod (alternatingGroup (Fin 3)) := by
  rw [P.Le_eq_pointResidual_sup structural escape C,
    subgroupOf_sup P.firstPointResidual_le_pointNormalizer P.secondPointResidual_le_pointNormalizer,
    Subgroup.map_sup,P.firstPointResidual_block_image structural escape,
    P.secondPointResidual_block_image structural escape]
  apply le_antisymm (sup_le (prod_mono le_rfl bot_le) (prod_mono bot_le le_rfl))
  rintro ⟨a,b⟩ ⟨ha,hb⟩
  have h := mul_mem_sup (show (a,1) ∈ (alternatingGroup (Fin 4)).prod
    (⊥ : Subgroup (Equiv.Perm (Fin 3))) from ⟨ha,one_mem _⟩)
    (show (1,b) ∈ (⊥ : Subgroup (Equiv.Perm (Fin 4))).prod (alternatingGroup (Fin 3)) from
      ⟨one_mem _,hb⟩)
  simpa only [Prod.mk_mul_mk,mul_one,one_mul] using h

theorem LeBlockAction_range
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    (P.LeBlockAction structural C).range =
      (alternatingGroup (Fin 4)).prod (alternatingGroup (Fin 3)) := by
  rw [LeBlockAction,MonoidHom.range_comp,inclusion_range]
  exact P.Le_block_image structural escape C

theorem L2_first_block_trivial
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) (r : P.L2) :
    (P.pointBlockAction (inclusion (P.L2_le_Le.trans
      (P.Le_le_pointNormalizer structural C)) r)).1 = 1 := by
  let M := P.pointNormalizer
  let N := P.L2.subgroupOf M
  let : N.Normal := normal_subgroupOf_of_le_normalizer (P.pointNormalizer_normalizes_L2 structural C)
  let I := N.map P.pointBlockAction
  let : I.Normal := Normal.map inferInstance _ (P.pointBlockAction_surjective structural escape)
  have hi : I ≤ (alternatingGroup (Fin 4)).prod (alternatingGroup (Fin 3)) := by
    rw [←P.Le_block_image structural escape C]
    exact map_mono (subgroupOf_mono _ P.L2_le_Le)
  have hfirst : I.map (MonoidHom.fst _ _) ≤ alternatingGroup (Fin 4) := by
    rintro a ⟨x,hx,rfl⟩
    exact (hi hx).1
  rcases Theory.SpecificGroups.Alternating.normal_four_product_first I hfirst with hp | hcontain
  · let f : P.L2 →* I.map (MonoidHom.fst _ _) :=
      (((MonoidHom.fst _ _).comp P.pointBlockAction).comp
        (inclusion (P.L2_le_Le.trans (P.Le_le_pointNormalizer structural C)))).codRestrict _
        (fun x => mem_map_of_mem _ (mem_map_of_mem P.pointBlockAction x.property))
    have he := DFunLike.congr_fun (P.L2_twoPerfect.hom_eq_one_of_isPGroup hp f) r
    exact congrArg Subtype.val he
  · exfalso
    apply P.firstPointResidual_not_le_quotientCentralizer structural escape C
    apply le_trans ?_ P.L2_le_quotientCentralizer
    let A := P.firstPointResidual.subgroupOf P.Le
    let B := P.L2.subgroupOf P.Le
    have haL := P.firstPointResidual_le_Le structural escape C
    have hAL : IsPPerfect 2 A := P.firstPointResidual_twoPerfect.of_surjective
      (subgroupOfEquivOfLe haL).symm.toMonoidHom (subgroupOfEquivOfLe haL).symm.surjective
    have hnB : P.Le ≤ normalizer (P.L2 : Set G) := P.Le_normalizes_L2 C
    let : B.Normal := normal_subgroupOf_of_le_normalizer hnB
    have hmaps : A.map (P.LeBlockAction structural C) ≤ B.map (P.LeBlockAction structural C) := by
      have hm (X : Subgroup G) (hX : X ≤ P.Le) :
          (X.subgroupOf P.Le).map (P.LeBlockAction structural C) =
            (X.subgroupOf M).map P.pointBlockAction := by
        rw [LeBlockAction,←map_map]
        congr 1
        ext x
        constructor
        · rintro ⟨y,hy,rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x,hX hx⟩,hx,Subtype.ext rfl⟩
      rw [hm _ haL,hm _ P.L2_le_Le,P.firstPointResidual_block_image structural escape]
      exact hcontain
    have hab := isPPerfect_le_of_map_le_of_kernel_normalizes (P.LeBlockAction structural C)
      A B hAL (P.LeBlockAction_twoKernel structural C) le_normalizer_of_normal hmaps
    intro x hx
    exact hab (show (⟨x,haL hx⟩ : P.Le) ∈ A from hx)

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
