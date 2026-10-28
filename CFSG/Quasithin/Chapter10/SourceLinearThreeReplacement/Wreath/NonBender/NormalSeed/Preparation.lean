module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.NonBender.NormalSeed.Inputs
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Centralizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Inputs
public import Theory.GroupTheory.WreathTwoResidual
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.GroupTheory.PResidual.PCoreQuotient

/-!
# The actual elementary-nine seed quotient in the involution centralizer

The recognized parabolic maps onto the concrete wreath actor through its
two-core. Residual transport through this two-group kernel, followed by
the original embedded residual equality, identifies X/O₂(X) with C₃².
Restricting X to G_z preserves this literal quotient. When X=K_z, the
conjugate-span definition gives normality in G_z, not in ambient G.

Source: Aschbacher--Smith 10.2.4 and the normal-seed paragraph of 10.3.3,
printed pp.747 and756. The rank obstruction and recognition are separate
obligations in `Inputs`; this module proves their original seed data.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender.NormalSeed
open Chapter3.Section02 Overgroups.Closure

private theorem elementaryNine_core : pCore 2 ElementaryNine = ⊥ := by
  have h3 : IsPGroup 3 ElementaryNine := IsPGroup.of_card (n := 2) (by
    change Nat.card (Fin 2 → ZMod 3) = 3 ^ 2
    simp)
  have hd := IsPGroup.disjoint_of_ne 2 3 (by decide) (pCore 2 ElementaryNine) ⊤
    pCore_isPGroup (h3.to_subgroup ⊤)
  simpa only [disjoint_top] using hd

private noncomputable def residualModel :
    (pResidual 2 WreathTwoResidual.Actor ⧸
      pCore 2 (pResidual 2 WreathTwoResidual.Actor)) ≃* ElementaryNine := by
  let e := WreathTwoResidual.residual_equiv_elementaryNine.some
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    ((QuotientGroup.quotientMulEquivOfEq elementaryNine_core).trans
      QuotientGroup.quotientBot)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G} {z : G}

/-- The parabolic residual equality identifies the seed's own two-core
quotient, without assuming that the whole parabolic core lies in X. -/
theorem seed_quotient_elementaryNine (r : ParabolicSeedData T L z) :
    Nonempty ((centralizerSeed T L z ⧸ pCore 2 (centralizerSeed T L z)) ≃*
      ElementaryNine) := by
  obtain ⟨ew⟩ := r.wreath
  obtain ⟨es⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let e := ew.trans (RegularWreathProduct.congr es.symm (MulEquiv.refl _))
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 r.parabolic))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let a : pResidual 2 r.parabolic ≃* centralizerSeed T L z :=
    ((pResidual 2 r.parabolic).equivMapOfInjective r.parabolic.subtype
      r.parabolic.subtype_injective).trans (MulEquiv.subgroupCongr r.residual)
  exact ⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans
    ((f.pResidualCoreQuotientEquiv hf hk).trans residualModel)⟩

/-- The same quotient on the seed as a subgroup of the original centralizer. -/
theorem restricted_seed_quotient_elementaryNine (r : ParabolicSeedData T L z) :
    let X := (centralizerSeed T L z).subgroupOf (centralizer ({z} : Set G))
    Nonempty ((X ⧸ pCore 2 X) ≃* ElementaryNine) := by
  dsimp only
  let a := subgroupOfEquivOfLe
    (show centralizerSeed T L z ≤ centralizer ({z} : Set G) from
      (map_subtype_le _).trans inf_le_right)
  obtain ⟨e⟩ := seed_quotient_elementaryNine r
  exact ⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e⟩

variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D}

/-- Equality with its G_z-conjugate span gives precisely relative normality. -/
theorem seed_normal_in_centralizer (d : CentralizerData T D s)
    (he : centralizerSeed T L (d.first * d.second) =
      componentSpan T L (d.first * d.second)) :
    ((centralizerSeed T L (d.first * d.second)).subgroupOf
      (centralizer ({d.first * d.second} : Set G))).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  rw [he]
  exact le_normalizer_conjugateSpanBy _ _

/-- The rank budget is on the actual involution centralizer. -/
theorem centralizer_three_rank_le_two (d : CentralizerData T D s) :
    primeRank 3 (centralizer ({d.first * d.second} : Set G)) ≤ 2 :=
  (D.simpleQTKE.involution_centralizer_sqtk d.order).stronglyQuasithin
    3 Nat.prime_three (by decide)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender.NormalSeed
