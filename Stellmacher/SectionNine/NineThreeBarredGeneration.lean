module
public import Stellmacher.SectionNine.NineThreeBarredExclusion
public import Stellmacher.SectionOne.TwoFactorWreathRecognition

/-!
# Generation by the actual barred mixed actor

The canonical Baumann subgroup has order four in the order-eight barred
Sylow. The geometric exclusion of the actual mixed actor from that subgroup
therefore gives the source's barred Sylow generation identity.

Source: Stellmacher (9.3), printed p.50/PDF p.40,
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem two_factor_generation_of_not_le_baumann
    {K V : Type u} [Group K] [Finite K] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (hyp : SectionOne.Hypotheses K V) (sylow : Sylow 2 K)
    (hgen : SectionOne.oneE (V := V) (sylow : Subgroup K) ⊔
      (sylow : Subgroup K) = ⊤)
    (hunique : IsUniqueMaximalContaining (sylow : Subgroup K) ⊤)
    (hcount : (SectionOne.oneSevenFactors (G := K) (V := V)).card = 2)
    (actor : Subgroup K) (hactor : actor ≤ (sylow : Subgroup K))
    (houtside : ¬ actor ≤ SectionOne.oneB (V := V) (sylow : Subgroup K)) :
    (sylow : Subgroup K) =
      SectionOne.oneB (V := V) (sylow : Subgroup K) ⊔ actor := by
  classical
  let baumann := SectionOne.oneB (V := V) (sylow : Subgroup K)
  let product := SectionOne.oneSevenGenerated (G := K) (V := V)
  let factors := SectionOne.oneSevenFactors (G := K) (V := V)
  have hbaumann : baumann = (sylow : Subgroup K) ⊓ product :=
    (SectionOne.oneSeven_baumann_eq_j hyp sylow).trans
      (SectionOne.oneSeven_global_identification hyp sylow).1
  obtain ⟨hnormal, hproduct, _⟩ := SectionOne.oneSeven_global_product hyp sylow
  have hbaumannCard : Nat.card baumann = 4 := by
    rw [hbaumann]
    have hcard := (SectionOne.sl2_product_sylow_coordinates sylow product hnormal
      factors hproduct (fun factor hfactor =>
        ((SectionOne.mem_oneSevenFactors_iff factor).mp hfactor).1)).2.2.1
    simpa [factors, hcount] using hcard
  obtain ⟨equiv⟩ := SectionOne.oneSeven_wreath_of_two_factors hyp sylow hgen hunique hcount
  have hgroupCard : Nat.card K = 72 := by
    rw [Nat.card_congr equiv.toEquiv, RegularWreathProduct.card]
    have hsl : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 :=
      SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
    rw [hsl]
    norm_num [Nat.card_eq_fintype_card]
  have hsylowCard : Nat.card sylow = 8 := by
    rw [sylow.card_eq_multiplicity, hgroupCard]
    decide +kernel
  have hle : baumann ⊔ actor ≤ (sylow : Subgroup K) :=
    sup_le (hbaumann ▸ inf_le_left) hactor
  have hlarge : 4 < Nat.card (baumann ⊔ actor : Subgroup K) := by
    by_contra hsmall
    have heq : baumann = baumann ⊔ actor := Subgroup.eq_of_le_of_card_ge
      le_sup_left (by rw [hbaumannCard]; omega)
    exact houtside (le_sup_right.trans heq.ge)
  have hdiv := Subgroup.card_dvd_of_le hle
  change Nat.card (baumann ⊔ actor : Subgroup K) ∣ Nat.card sylow at hdiv
  rw [hsylowCard] at hdiv
  have hbound := Nat.le_of_dvd (by decide : 0 < 8) hdiv
  have hcard : Nat.card (baumann ⊔ actor : Subgroup K) = 8 := by
    interval_cases hsize : Nat.card (baumann ⊔ actor : Subgroup K) <;> omega
  exact (Subgroup.eq_of_le_of_card_ge hle (by
    rw [hsylowCard, hcard])).symm

public theorem nine_three_mixed_barred_generation
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (rank : NineThreeNativeActionRankData ctx) :
    letI := rank.elementary
    letI := sectionSixQuotientAction ctx.hypothesisTwo
    let m := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let Y := ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a
    let barY := ((Y.map embedding).subgroupOf P1).map
      (sectionSixQuotientMap ctx.hypothesisTwo)
    let U := sectionSixBarSylow ctx.hypothesisTwo
    (U : Subgroup (SectionSixBarP1 ctx.hypothesisTwo)) =
      SectionOne.oneB (V := sectionSixLocalV ctx.hypothesisTwo)
        (U : Subgroup (SectionSixBarP1 ctx.hypothesisTwo)) ⊔ barY := by
  let _ := rank.elementary
  let _ := sectionSixQuotientAction ctx.hypothesisTwo
  let m := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let Y := ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a
  have hYT : Y ≤ T := (nine_three_mixed_actor_quadratic ctx hb first second config).1
  exact two_factor_generation_of_not_le_baumann rank.action_hypotheses
    (sectionSixBarSylow ctx.hypothesisTwo) rank.generated rank.unique_maximal
    rank.factor_count _ (nine_three_barred_actor_action_transport ctx Y hYT).1
    (nine_three_mixed_barred_actor_not_le_oneB ctx hb hlarge first second config rank)

end Stellmacher.SectionNine
