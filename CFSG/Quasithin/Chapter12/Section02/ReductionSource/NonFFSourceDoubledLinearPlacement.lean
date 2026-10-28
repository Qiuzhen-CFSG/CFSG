module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearOuter
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearUniqueness
public import CFSG.Quasithin.Chapter4.Section04.OddActorQuotient
import all CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.ComponentPlacement
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearOrdinary
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticOddAction

/-!
# Literal outside-component placement for the original linear-three pair

The complete Theorem B outer-section exclusion makes the actual perfect
odd residual act by inner automorphisms. Original residual uniqueness then
places the complete doubled orbit in the literal outside component, whose
full central quotient retains rank six times the field degree.
Source: Aschbacher--Smith 4.4.10--12 and 7.3.4, printed pp.621--622,699.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open Chapter4.Section04.NormalizedRankOneOddControl
open Theory.SpecificGroups.SymplecticFour
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- An escaping abelian odd normalizer supplies its actual outside component;
the proved reciprocal uniqueness and full source-orbit size discharge selection. -/
theorem sourceOrbit_linear_oddNormalizer_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K,D.sourceOrbit.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ IsQuasithin K ∧ KnownSimple.IsKnownSimple (K ⧸ center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) ∧
      D.sourceOrbit.subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) := by
  apply D.sourceOrbit_whole_oddNormalizer_component_of_large h hd _ A hne hAC ho
    (D.sourceOrbit_linear_residual_uniqueness h hd F hF hmodel A hAC ho) hout
  apply D.sourceOrbit_card_gt_eight_of_rank
  rw [D.sourceOrbit_linear_dimension h hd F hmodel]
  omega

/-- The original linear-three odd fixed residual acts by inner automorphisms on
each actual component of its odd normalizer. No outer-solvability or model
premise is required, and the original two-core and covering center remain. -/
theorem sourceOrbit_linear_odd_residual_inner
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) :
    (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (A : Set G))) := by
  let R := oddActorResidual L A
  let N := normalizer (A : Set G)
  have hRN : R ≤ N := ((oddActorResidual_le L A).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  let a : R.subgroupOf N ≃* R := subgroupOfEquivOfLe hRN
  have hAN := hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le
  have hA : A ≤ normalizer (L : Set G) ⊓
      centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
    rw [←D.sourceOrbit_eq]
    exact le_inf hAN hAC
  have hAL := ((le_sectionCentralizer_iff A L).mp
    (hA.trans (D.doubledOrbit_relative_centralizer_le_sectionCentralizer h))).2
  have hAV : A ≤ centralizer (V : Set G) :=
    hAC.trans (centralizer_le (by rw [D.sourceOrbit_eq]; exact le_componentOrbit V T))
  obtain ⟨b,_⟩ := chosen_oddActorResidual_quotient h.toHypothesis1221 D A hAN hAL ho hAV
  obtain ⟨eL⟩ := D.linear_central_quotient h F hmodel
  let := h.quasisimple
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : IsSimpleGroup (PSL(3,F.Carrier)) := eL.symm.isSimpleGroup
  let : Group.IsPerfect (PSL(3,F.Carrier)) := Group.IsPerfect.ofSurjective
    (f := eL.toMonoidHom) eL.surjective
  let eR := (centerQuotientCongr b).trans eL
  let e := (centerQuotientCongr (QuotientGroup.congr _ _ a (pCore_map_iso 2 a))).trans eR
  let : Group.IsPerfect R := oddActorResidual_isPerfect L A
  let : Group.IsPerfect (R.subgroupOf N) := Group.IsPerfect.ofSurjective
    (f := a.symm.toMonoidHom) a.symm.surjective
  obtain ⟨_,hRK,_⟩ := chosen_oddNormalizer_component_normalization h.toHypothesis1221 D
    A hAN hAL ho hAV K hK
  let := hK.2
  have hqt := ((oddNormalizer_properQTK h.simpleQTKE A hne).2.1).subgroup K
  have hkg := ((oddNormalizer_properQTK h.simpleQTKE A hne).2.2).subgroup K
  have hm := ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple hqt hkg
  exact perfect_actor_inner_of_core_central_quotient K (R.subgroupOf N) e
    (fun U f hf => no_theoremB_linear_three_outer_section hm F.Carrier U f hf) hRK

/-- The selected nonbinary linear-three component contains the whole original
orbit and residual, has odd centralizer, and retains the full orbit rank 6n.
The prior reciprocal theorem supplies residual uniqueness. -/
theorem sourceOrbit_linear_oddNormalizer_placement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G)) :
    K.Normal ∧ D.sourceOrbit ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) =
        pPrimeCore 2 (normalizer (A : Set G)) ∧
      6 * F.degree ≤ primeRank 2 (K ⧸ center K) := by
  have hs : normalizer (L : Set G) ⊓ centralizer (V : Set G) ≤ sectionCentralizer L := by
    let := h.quasisimple
    apply relative_module_centralizer_le_sectionCentralizer L V D.normalizes _ D.ne_bot D.eq_commutator
    exact (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes
  have hA : A ≤ normalizer (L : Set G) ⊓
      centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
    rw [←D.sourceOrbit_eq]
    exact le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
  have hu := D.sourceOrbit_linear_residual_uniqueness h hd F hn hmodel A hAC ho
  have hi := D.sourceOrbit_linear_odd_residual_inner h hd F hmodel A hne hAC ho K hK
  obtain ⟨hKn,_,hr,hcent⟩ := normal_component_of_inner_action h.toHypothesis1221 D hs
    A (hA.trans inf_le_left)
    ((le_sectionCentralizer_iff A L).mp
      (hA.trans (D.doubledOrbit_relative_centralizer_le_sectionCentralizer h))).2 ho
    ((hA.trans inf_le_right).trans (centralizer_le (le_componentOrbit V T))) hu hout K hK houtK hi
  have hw : D.sourceOrbit ≤ K.map (normalizer (A : Set G)).subtype := by
    rw [D.sourceOrbit_eq]
    exact ((D.doubledOrbit_oddActorResidual_cover h A hA ho).2.2.1.trans (pCoreIn_le 2 _)).trans hr
  have hoC : Odd (Nat.card (centralizer (K : Set (normalizer (A : Set G))))) := by
    rw [hcent]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hrQ := module_rank_le_component_quotient A D.sourceOrbit K hw hoC
  have hc : Nat.card D.sourceOrbit = 2 ^ (6 * F.degree) := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)
    rw [Nat.card_congr Additive.toMul,Nat.card_zmod,D.sourceOrbit_linear_dimension h hd F hmodel] at hh
    exact hh
  let : IsElementaryAbelian 2 (⊤ : Subgroup D.sourceOrbit) :=
    IsElementaryAbelian.of_injective (⊤ : Subgroup D.sourceOrbit).subtype Subtype.val_injective
  have hb := IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup D.sourceOrbit)
    (by simpa only [card_top] using hc)
  exact ⟨hKn,hw,hr,hcent,hb.trans hrQ⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
