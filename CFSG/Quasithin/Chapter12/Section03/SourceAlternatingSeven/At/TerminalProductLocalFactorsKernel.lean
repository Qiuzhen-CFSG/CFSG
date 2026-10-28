module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsKernel
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalProductLocalFactorsIntersectionResidual

/-!
# TerminalProductLocalFactorsKernel at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalProductLocalFactorsKernel`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
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

theorem Le_le_pointNormalizer_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (C : P.ComponentAnalysis) :
    P.Le ≤ P.pointNormalizer := by
  rw [P.Le_eq_pointNormalizer_primeToResidual_at structural C]
  exact map_subtype_le _

theorem pointNormalizer_normalizes_Le_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (C : P.ComponentAnalysis) :
    P.pointNormalizer ≤ normalizer (P.Le : Set G) := by
  rw [P.Le_eq_pointNormalizer_primeToResidual_at structural C]
  exact P.pointNormalizer.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ _)

theorem pointNormalizer_normalizes_L2_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (C : P.ComponentAnalysis) :
    P.pointNormalizer ≤ normalizer (P.L2 : Set G) :=
  ((le_inf (P.pointNormalizer_normalizes_Le_at structural C)
    ((inf_le_right.trans C.normalizes).trans P.quotientCentralizer_normalized)).trans
      inf_normalizer_le_normalizer_inf).trans
    (normalizer_le_normalizer_characteristic_image _ _)

def LeBlockAction_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (C : P.ComponentAnalysis) :
    P.Le →* (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 3)) :=
  P.pointBlockAction.comp (inclusion (P.Le_le_pointNormalizer_at structural C))

theorem LeBlockAction_twoKernel_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (C : P.ComponentAnalysis) :
    IsPGroup 2 (P.LeBlockAction_at structural C).ker := by
  have hRL : P.Le ≤ L := (map_subtype_le _).trans inf_le_left
  let f := P.LeBlockAction_at structural C
  have hπ (r : f.ker) : S.projection (inclusion hRL r.val) = 1 := by
    let n := inclusion (P.Le_le_pointNormalizer_at structural C) r.val
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

theorem firstPointResidual_not_le_quotientCentralizer_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    ¬ P.firstPointResidual ≤ P.quotientCentralizer := by
  intro h
  have hK : P.firstPointResidual ≤ P.K := by
    rw [P.firstPointResidual_eq_L1_at structural escape C]
    exact P.L1_le_component_at structural escape C
  have hp := (pCore_isPGroup.map P.K.subtype).to_le
    ((le_inf hK h).trans (P.component_inf_quotientCentralizer_le_core C))
  have ha := hp.of_surjective (P.firstResidualProjection_at structural escape)
    (P.firstResidualProjection_surjective_at structural escape)
  have hc : Nat.card (alternatingGroup (Fin 4)) = 12 := by
    rw [Nat.card_eq_fintype_card,card_alternatingGroup]; decide
  obtain ⟨n,hn⟩ := ha.exists_card_eq
  have hcop := (by decide : Nat.Coprime 3 2).pow_right n
  rw [←hn,hc] at hcop
  norm_num at hcop

theorem firstPointResidual_block_image_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) :
    (P.firstPointResidual.subgroupOf P.pointNormalizer).map P.pointBlockAction =
      (alternatingGroup (Fin 4)).prod (⊥ : Subgroup (Equiv.Perm (Fin 3))) := by
  apply le_antisymm
  · rintro x ⟨n,hn,rfl⟩
    exact ⟨P.firstResidualPermutation_mem_at structural escape ⟨n,hn⟩,
      P.firstResidual_second_eq_one ⟨n,hn⟩⟩
  · rintro ⟨a,b⟩ ⟨ha,hb⟩
    obtain ⟨r,hr⟩ := P.firstResidualProjection_surjective_at structural escape ⟨a,ha⟩
    refine ⟨inclusion P.firstPointResidual_le_pointNormalizer r,r.property,?_⟩
    exact Prod.ext (congrArg Subtype.val hr)
      ((P.firstResidual_second_eq_one r).trans (mem_bot.mp hb).symm)

theorem secondPointResidual_block_image_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) :
    (P.secondPointResidual.subgroupOf P.pointNormalizer).map P.pointBlockAction =
      (⊥ : Subgroup (Equiv.Perm (Fin 4))).prod (alternatingGroup (Fin 3)) := by
  apply le_antisymm
  · rintro x ⟨n,hn,rfl⟩
    exact ⟨P.secondResidual_first_eq_one ⟨n,hn⟩,
      P.secondResidualPermutation_mem_at structural escape ⟨n,hn⟩⟩
  · rintro ⟨a,b⟩ ⟨ha,hb⟩
    obtain ⟨r,hr⟩ := P.secondResidualProjection_surjective_at structural escape ⟨b,hb⟩
    refine ⟨inclusion P.secondPointResidual_le_pointNormalizer r,r.property,?_⟩
    exact Prod.ext ((P.secondResidual_first_eq_one r).trans (mem_bot.mp ha).symm)
      (congrArg Subtype.val hr)

theorem Le_block_image_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    (P.Le.subgroupOf P.pointNormalizer).map P.pointBlockAction =
      (alternatingGroup (Fin 4)).prod (alternatingGroup (Fin 3)) := by
  rw [P.Le_eq_pointResidual_sup_at structural escape C,
    subgroupOf_sup P.firstPointResidual_le_pointNormalizer P.secondPointResidual_le_pointNormalizer,
    Subgroup.map_sup,P.firstPointResidual_block_image_at structural escape,
    P.secondPointResidual_block_image_at structural escape]
  apply le_antisymm (sup_le (prod_mono le_rfl bot_le) (prod_mono bot_le le_rfl))
  rintro ⟨a,b⟩ ⟨ha,hb⟩
  have h := mul_mem_sup (show (a,1) ∈ (alternatingGroup (Fin 4)).prod
    (⊥ : Subgroup (Equiv.Perm (Fin 3))) from ⟨ha,one_mem _⟩)
    (show (1,b) ∈ (⊥ : Subgroup (Equiv.Perm (Fin 4))).prod (alternatingGroup (Fin 3)) from
      ⟨one_mem _,hb⟩)
  simpa only [Prod.mk_mul_mk,mul_one,one_mul] using h

theorem LeBlockAction_range_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    (P.LeBlockAction_at structural C).range =
      (alternatingGroup (Fin 4)).prod (alternatingGroup (Fin 3)) := by
  rw [LeBlockAction_at,MonoidHom.range_comp,inclusion_range]
  exact P.Le_block_image_at structural escape C

theorem L2_first_block_trivial_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) (r : P.L2) :
    (P.pointBlockAction (inclusion (P.L2_le_Le.trans
      (P.Le_le_pointNormalizer_at structural C)) r)).1 = 1 := by
  let M := P.pointNormalizer
  let N := P.L2.subgroupOf M
  let : N.Normal := normal_subgroupOf_of_le_normalizer (P.pointNormalizer_normalizes_L2_at structural C)
  let I := N.map P.pointBlockAction
  let : I.Normal := Normal.map inferInstance _ (P.pointBlockAction_surjective_at structural escape)
  have hi : I ≤ (alternatingGroup (Fin 4)).prod (alternatingGroup (Fin 3)) := by
    rw [←P.Le_block_image_at structural escape C]
    exact map_mono (subgroupOf_mono _ P.L2_le_Le)
  have hfirst : I.map (MonoidHom.fst _ _) ≤ alternatingGroup (Fin 4) := by
    rintro a ⟨x,hx,rfl⟩
    exact (hi hx).1
  rcases Theory.SpecificGroups.Alternating.normal_four_product_first I hfirst with hp | hcontain
  · let f : P.L2 →* I.map (MonoidHom.fst _ _) :=
      (((MonoidHom.fst _ _).comp P.pointBlockAction).comp
        (inclusion (P.L2_le_Le.trans (P.Le_le_pointNormalizer_at structural C)))).codRestrict _
        (fun x => mem_map_of_mem _ (mem_map_of_mem P.pointBlockAction x.property))
    have he := DFunLike.congr_fun (P.L2_twoPerfect.hom_eq_one_of_isPGroup hp f) r
    exact congrArg Subtype.val he
  · exfalso
    apply P.firstPointResidual_not_le_quotientCentralizer_at structural escape C
    apply le_trans ?_ P.L2_le_quotientCentralizer
    let A := P.firstPointResidual.subgroupOf P.Le
    let B := P.L2.subgroupOf P.Le
    have haL := P.firstPointResidual_le_Le_at structural escape C
    have hAL : IsPPerfect 2 A := P.firstPointResidual_twoPerfect.of_surjective
      (subgroupOfEquivOfLe haL).symm.toMonoidHom (subgroupOfEquivOfLe haL).symm.surjective
    have hnB : P.Le ≤ normalizer (P.L2 : Set G) := P.Le_normalizes_L2 C
    let : B.Normal := normal_subgroupOf_of_le_normalizer hnB
    have hmaps : A.map (P.LeBlockAction_at structural C) ≤ B.map (P.LeBlockAction_at structural C) := by
      have hm (X : Subgroup G) (hX : X ≤ P.Le) :
          (X.subgroupOf P.Le).map (P.LeBlockAction_at structural C) =
            (X.subgroupOf M).map P.pointBlockAction := by
        rw [LeBlockAction_at,←map_map]
        congr 1
        ext x
        constructor
        · rintro ⟨y,hy,rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x,hX hx⟩,hx,Subtype.ext rfl⟩
      rw [hm _ haL,hm _ P.L2_le_Le,P.firstPointResidual_block_image_at structural escape]
      exact hcontain
    have hab := isPPerfect_le_of_map_le_of_kernel_normalizes (P.LeBlockAction_at structural C)
      A B hAL (P.LeBlockAction_twoKernel_at structural C) le_normalizer_of_normal hmaps
    intro x hx
    exact hab (show (⟨x,haL hx⟩ : P.Le) ∈ A from hx)

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

