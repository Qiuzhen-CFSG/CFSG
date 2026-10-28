module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsIntersection
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsFirstAction
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsSecondNatural
public import Theory.SpecificGroups.Alternating.FourTwoKernel

/-!
# The literal first factor is the component-intersection residual

The intersection K∩N_G(L) has Borel image of order twelve in the supplied
A₅ quotient. Its prime-to-three residual is therefore not a two-group.
It is normal in the full point normalizer and lies in L₁. The original
four-letter action of L₁ has two-group kernel and image A₄, so normal
subgroup comparison forces equality. In particular L₁ is contained in K.

The final application discharges the intersection field of LocalFactorAnalysis.
The L₂ identification and Thompson generation remain with
qt-d-1231-terminal-product; ComponentAnalysis is discharged by the terminal
assembly owner qt-d-1231-terminal.
Source: Aschbacher--Smith, completion of 12.3.1, printed pp.811--812.
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

theorem component_intersection_image_card
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (C : P.ComponentAnalysis) :
    Nat.card (((normalizer (L : Set G)).subgroupOf P.K).map (P.componentProjection C)) = 12 := by
  obtain ⟨R,hR⟩ := P.exists_component_sylow
  rw [P.component_intersection_image_eq_borel structural C R hR]
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer
    (R.mapSurjective (P.componentProjection_surjective C))
  rw [hi,Nat.card_eq_fintype_card]
  have hc : ∀ i : Fin 5, Fintype.card
      (MulAction.stabilizer (alternatingGroup (Fin 5)) i) = 12 := by decide +kernel
  exact hc i

theorem component_intersection_residual_not_twoGroup
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (C : P.ComponentAnalysis) :
    ¬ IsPGroup 2 ((primeToResidual 3 (P.K ⊓ normalizer (L : Set G) : Subgroup G)).map
      (P.K ⊓ normalizer (L : Set G)).subtype) := by
  let X := P.K ⊓ normalizer (L : Set G)
  have hcard : Nat.card ((normalizer (L : Set G)).subgroupOf P.K) = Nat.card X := by
    rw [Nat.card_congr (((normalizer (L : Set G)).subgroupOf P.K).equivMapOfInjective
      P.K.subtype P.K.subtype_injective).toEquiv,subgroupOf_map_subtype,inf_comm]
  have hdiv : 3 ∣ Nat.card X := by
    have hh := ((normalizer (L : Set G)).subgroupOf P.K).card_map_dvd (P.componentProjection C)
    rw [P.component_intersection_image_card structural C,hcard] at hh
    exact dvd_trans (by decide : 3 ∣ 12) hh
  intro hp
  have hp' : IsPGroup 2 (primeToResidual 3 X) := hp.of_equiv
    ((primeToResidual 3 X).equivMapOfInjective X.subtype X.subtype_injective).symm
  obtain ⟨n,hn⟩ := hp'.exists_card_eq
  have hc : Nat.Coprime 3 (Nat.card X) := by
    rw [← (primeToResidual 3 X).card_mul_index,hn]
    exact ((by decide : Nat.Coprime 3 2).pow_right n).mul_right (primeToResidual_index_coprime 3)
  exact (Nat.prime_three.coprime_iff_not_dvd.mp hc) hdiv

theorem firstPointResidual_twoPerfect : IsPPerfect 2 P.firstPointResidual :=
  (isPPerfect_primeToResidual 3 2 (by decide)).of_surjective
    ((primeToResidual 3 P.firstPointFactor).equivMapOfInjective P.firstPointFactor.subtype
      P.firstPointFactor.subtype_injective).toMonoidHom
    ((primeToResidual 3 P.firstPointFactor).equivMapOfInjective P.firstPointFactor.subtype
      P.firstPointFactor.subtype_injective).surjective

theorem L1_eq_component_intersection_residual
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.L1 = (primeToResidual 3 (P.K ⊓ normalizer (L : Set G) : Subgroup G)).map
      (P.K ⊓ normalizer (L : Set G)).subtype := by
  let X := P.K ⊓ normalizer (L : Set G)
  let B := (primeToResidual 3 X).map X.subtype
  have hBF : B ≤ P.firstPointResidual := by
    rw [P.firstPointResidual_eq_L1 structural escape C]
    exact P.component_intersection_residual_le_L1 structural C
  have hn : P.pointNormalizer ≤ normalizer (B : Set G) :=
    (P.component_intersection_normalized structural C).trans
      (normalizer_le_normalizer_characteristic_image X (primeToResidual 3 X))
  let : (B.subgroupOf P.firstPointResidual).Normal := normal_subgroupOf_of_le_normalizer
    (P.firstPointResidual_le_pointNormalizer.trans hn)
  have hnot : ¬ IsPGroup 2 (B.subgroupOf P.firstPointResidual) := by
    intro hh
    exact P.component_intersection_residual_not_twoGroup structural C
      (hh.of_equiv (subgroupOfEquivOfLe hBF))
  have he := Theory.SpecificGroups.Alternating.normal_eq_top_of_four_quotient_not_twoGroup
    (P.firstResidualProjection structural escape) (P.firstResidualProjection_surjective structural escape)
    (P.firstResidualProjection_twoKernel structural escape C) P.firstPointResidual_twoPerfect
    (B.subgroupOf P.firstPointResidual) hnot
  rw [← P.firstPointResidual_eq_L1 structural escape C]
  apply le_antisymm ?_ hBF
  intro x hx
  exact show (⟨x,hx⟩ : P.firstPointResidual) ∈ B.subgroupOf P.firstPointResidual from
    he.symm ▸ mem_top _

theorem L1_le_component
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) : P.L1 ≤ P.K := by
  rw [P.L1_eq_component_intersection_residual structural escape C]
  exact (map_subtype_le _).trans inf_le_left

/-- The source intersection premise in LocalFactorAnalysis is discharged.
Only the second residual identification and its Thompson generation remain
with qt-d-1231-terminal-product. -/
theorem localFactorAnalysis_of_second_identification
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis)
    (hR : P.secondPointResidual = P.L2)
    (hthompson : ⁅P.L2, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ = P.L2) :
    Nonempty P.LocalFactorAnalysis :=
  P.localFactorAnalysis_of_residual_identifications structural escape C hR
    (P.L1_eq_component_intersection_residual structural escape C) hthompson

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
