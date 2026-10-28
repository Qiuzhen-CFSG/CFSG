module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsIntersectionResidual
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalProductLocalFactorsFirstAction
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalProductLocalFactorsIntersection
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalProductLocalFactorsSecondNatural

/-!
# TerminalProductLocalFactorsIntersectionResidual at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalProductLocalFactorsIntersectionResidual`, with structural
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

theorem component_intersection_image_card_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (C : P.ComponentAnalysis) :
    Nat.card (((normalizer (L : Set G)).subgroupOf P.K).map (P.componentProjection C)) = 12 := by
  obtain ⟨R,hR⟩ := P.exists_component_sylow
  rw [P.component_intersection_image_eq_borel_at structural C R hR]
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer
    (R.mapSurjective (P.componentProjection_surjective C))
  rw [hi,Nat.card_eq_fintype_card]
  have hc : ∀ i : Fin 5, Fintype.card
      (MulAction.stabilizer (alternatingGroup (Fin 5)) i) = 12 := by decide +kernel
  exact hc i

theorem component_intersection_residual_not_twoGroup_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (C : P.ComponentAnalysis) :
    ¬ IsPGroup 2 ((primeToResidual 3 (P.K ⊓ normalizer (L : Set G) : Subgroup G)).map
      (P.K ⊓ normalizer (L : Set G)).subtype) := by
  let X := P.K ⊓ normalizer (L : Set G)
  have hcard : Nat.card ((normalizer (L : Set G)).subgroupOf P.K) = Nat.card X := by
    rw [Nat.card_congr (((normalizer (L : Set G)).subgroupOf P.K).equivMapOfInjective
      P.K.subtype P.K.subtype_injective).toEquiv,subgroupOf_map_subtype,inf_comm]
  have hdiv : 3 ∣ Nat.card X := by
    have hh := ((normalizer (L : Set G)).subgroupOf P.K).card_map_dvd (P.componentProjection C)
    rw [P.component_intersection_image_card_at structural C,hcard] at hh
    exact dvd_trans (by decide : 3 ∣ 12) hh
  intro hp
  have hp' : IsPGroup 2 (primeToResidual 3 X) := hp.of_equiv
    ((primeToResidual 3 X).equivMapOfInjective X.subtype X.subtype_injective).symm
  obtain ⟨n,hn⟩ := hp'.exists_card_eq
  have hc : Nat.Coprime 3 (Nat.card X) := by
    rw [← (primeToResidual 3 X).card_mul_index,hn]
    exact ((by decide : Nat.Coprime 3 2).pow_right n).mul_right (primeToResidual_index_coprime 3)
  exact (Nat.prime_three.coprime_iff_not_dvd.mp hc) hdiv

theorem L1_eq_component_intersection_residual_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.L1 = (primeToResidual 3 (P.K ⊓ normalizer (L : Set G) : Subgroup G)).map
      (P.K ⊓ normalizer (L : Set G)).subtype := by
  let X := P.K ⊓ normalizer (L : Set G)
  let B := (primeToResidual 3 X).map X.subtype
  have hBF : B ≤ P.firstPointResidual := by
    rw [P.firstPointResidual_eq_L1_at structural escape C]
    exact P.component_intersection_residual_le_L1_at structural C
  have hn : P.pointNormalizer ≤ normalizer (B : Set G) :=
    (P.component_intersection_normalized_at structural C).trans
      (normalizer_le_normalizer_characteristic_image X (primeToResidual 3 X))
  let : (B.subgroupOf P.firstPointResidual).Normal := normal_subgroupOf_of_le_normalizer
    (P.firstPointResidual_le_pointNormalizer.trans hn)
  have hnot : ¬ IsPGroup 2 (B.subgroupOf P.firstPointResidual) := by
    intro hh
    exact P.component_intersection_residual_not_twoGroup_at structural C
      (hh.of_equiv (subgroupOfEquivOfLe hBF))
  have he := Theory.SpecificGroups.Alternating.normal_eq_top_of_four_quotient_not_twoGroup
    (P.firstResidualProjection_at structural escape) (P.firstResidualProjection_surjective_at structural escape)
    (P.firstResidualProjection_twoKernel_at structural escape C) P.firstPointResidual_twoPerfect
    (B.subgroupOf P.firstPointResidual) hnot
  rw [← P.firstPointResidual_eq_L1_at structural escape C]
  apply le_antisymm ?_ hBF
  intro x hx
  exact show (⟨x,hx⟩ : P.firstPointResidual) ∈ B.subgroupOf P.firstPointResidual from
    he.symm ▸ mem_top _

theorem L1_le_component_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) : P.L1 ≤ P.K := by
  rw [P.L1_eq_component_intersection_residual_at structural escape C]
  exact (map_subtype_le _).trans inf_le_left

theorem localFactorAnalysis_of_second_identification_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis)
    (hR : P.secondPointResidual = P.L2)
    (hthompson : ⁅P.L2, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ = P.L2) :
    Nonempty P.LocalFactorAnalysis :=
  P.localFactorAnalysis_of_residual_identifications_at structural escape C hR
    (P.L1_eq_component_intersection_residual_at structural escape C) hthompson

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

