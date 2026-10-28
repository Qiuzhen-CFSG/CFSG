module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalLeftCore
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.QuotientCardSixtyModule
public import Theory.SpecificGroups.Alternating.FiveResidualSylowBound

/-!
# The degree-two left block exhausts the right two-core

The whole left core is its intrinsic block layer, and its residual-fixed
subgroup is trivial. The actual A5 quotient therefore makes that core have
order sixteen. The A5 automizer bounds the original Sylow by 2^7. On the
right, the actual A7 quotient has Sylow order eight, so its core has order
at most sixteen and must equal the entire natural four-space.

This is the order argument in Aschbacher–Smith 5.1.13, printed p.638,
refs/quasithin.pdf. The companion LocalA7Exclusion uses the equality to
construct the forbidden right block, retaining the literal residual.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
/-- The whole original left core has sixteen elements. -/
theorem LocalA7Configuration.left_core_card
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    Nat.card ((L ⊔ (T : Subgroup G)).pCoreIn 2) = 16 := by
  let M := L ⊔ (T : Subgroup G)
  let R := L.subgroupOf M
  let eR : R ≃* L := subgroupOfEquivOfLe le_sup_left
  have hn := a.degree_two h hH hgen c d
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := h.linear
  rw [hn] at hF
  obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let e := (QuotientGroup.congr _ _ eR (pCore_map_iso 2 eR)).trans (eF.trans e5)
  have hq : Nat.card (R ⧸ pCore 2 R) = 60 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hb := a.left_block h hH hgen c d
  have hm : Nat.card (ChapterC.BlockModule R) = 16 := hb.2.module_card_of_quotient_card_sixty hq
  have hfix : ChapterC.blockFixed R = ⊥ := by
    apply bot_unique
    intro x hx
    have hU : ((x.val : R).val : G) ∈ M.pCoreIn 2 := by
      rw [a.left_core_block_layer h hH hgen c d]
      exact mem_map_of_mem (M.subtype.comp R.subtype) x.property
    have ht : ((x.val : R).val : G) ∈ (T : Subgroup G) :=
      (a.left_core_input h hH hgen c d).reduced_le_sylow hU
    have hc : ((x.val : R).val : G) ∈ centralizer (L : Set G) := by
      intro l hl
      exact congrArg (M.subtype.comp R.subtype) (mem_center_iff.mp hx (eR.symm ⟨l,hl⟩))
    have he := (a.left_fixed_eq_bot h hH hgen c d).1.le ⟨ht,hc⟩
    exact Subtype.ext (Subtype.ext (Subtype.ext (mem_bot.mp he)))
  have huc : Nat.card (ChapterC.blockU R) = 16 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (ChapterC.blockFixed R)
    rw [hm,hfix,card_bot,mul_one] at hh
    exact hh
  rw [a.left_core_block_layer h hH hgen c d]
  change Nat.card ((ChapterC.blockU R).map (M.subtype.comp R.subtype)) = 16
  rw [card_map_of_injective (f := M.subtype.comp R.subtype)
    (M.subtype_injective.comp R.subtype_injective)]
  exact huc
/-- The original Sylow has order at most 2^7 in the surviving left-block case. -/
theorem LocalA7Configuration.sylow_card_le
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) : Nat.card T ≤ 128 := by
  let M := L ⊔ (T : Subgroup G)
  let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  let eR : pResidual 2 M ≃* L :=
    ((pResidual 2 M).equivMapOfInjective M.subtype M.subtype_injective).trans
      (MulEquiv.subgroupCongr h.local_residual_eq)
  have hn := a.degree_two h hH hgen c d
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := h.linear
  rw [hn] at hF
  obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let e := (QuotientGroup.congr _ _ eR (pCore_map_iso 2 eR)).trans (eF.trans e5)
  have hh := Theory.SpecificGroups.Alternating.FiveResidualSylowBound.sylow_card_le_eight_mul_core P e
  have hP : Nat.card P = Nat.card T :=
    Nat.card_congr (subgroupOfEquivOfLe (show (T : Subgroup G) ≤ M from le_sup_right)).toEquiv
  have hQ : Nat.card (pCore 2 M) = 16 := by
    have hh := a.left_core_card h hH hgen c d
    change Nat.card ((pCore 2 M).map M.subtype) = 16 at hh
    rwa [card_map_of_injective M.subtype_injective] at hh
  rw [hP,hQ] at hh
  exact hh

/-- The right four-space exhausts its ambient two-core. -/
theorem LocalA7Configuration.right_core_eq_four
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    (K ⊔ (T : Subgroup G)).pCoreIn 2 = localOmegaModule T K := by
  let M := K ⊔ (T : Subgroup G)
  let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  let U := (localOmegaModule T K).subgroupOf M
  let Q := pCore 2 M
  have hr : IsPReduced 2 U := LocalOmega.reduced_internal a.reduced
  have hUQ : U ≤ Q := hr.le_pCore
  obtain ⟨q,hq,_,hk⟩ := a.four_action h (a.four h hH hgen c d)
  have hpq : Nat.card (P.mapSurjective hq) = 8 := by
    rw [Sylow.card_eq_multiplicity,nat_card_alternatingGroup,Nat.card_fin]
    norm_num [Nat.factorial]
    rw [show (2520 : ℕ).factorization 2 = 3 by
      rw [show 2520 = 2^3*315 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),Nat.factorization_pow]
      simp [Nat.prime_two.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2 ∣ 315)]]
    norm_num
  have he := card_eq_card_quotient_mul_card_subgroup (q.subgroupMap (P : Subgroup M)).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    (q.subgroupMap (P : Subgroup M)) (q.subgroupMap_surjective _)).toEquiv,
    ker_subgroupMap,hk,
    Nat.card_congr (subgroupOfEquivOfLe (pCore_isPGroup.le_sylow_of_normal P)).toEquiv] at he
  change Nat.card P = Nat.card (P.mapSurjective hq) * Nat.card Q at he
  rw [hpq] at he
  have hP : Nat.card P ≤ 128 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show (T : Subgroup G) ≤ M from le_sup_right)).toEquiv).trans_le
      (a.sylow_card_le h hH hgen c d)
  have hUc : Nat.card U = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe a.reduced.1).toEquiv).trans (a.four h hH hgen c d)
  have heq : U = Q := eq_of_le_of_card_ge hUQ (by omega)
  have hh := congrArg (map M.subtype) heq.symm
  rwa [map_subgroupOf_eq_of_le a.reduced.1] at hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
