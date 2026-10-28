module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SixHallSource
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddSymplectic
public import CFSG.Quasithin.Chapter4.Section04.OddActorQuotient
import all CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.ComponentPlacement

/-!
# Actual A₆ Hall component placement or an outer A₆ section

The literal residual quotient retains the original two-core and covering
center. It yields either placement of the whole rank-eight orbit and residual
in the actual selected ordinary component, or an A₆ section of that component's
full outer group. Binary symplectic six-space has solvable outer group, so
its original component always satisfies the placement conclusion.
Source: Aschbacher--Smith 4.4.10--11, printed p.621, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open Chapter4.Section04.NormalizedRankOneOddControl
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem doubled_six_simple_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6))) :
    Nonempty (((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨m⟩ := hmodel
  exact ⟨(D.componentCentralQuotientEquiv h.quasisimple).trans
    ((centerQuotientCongr m.groupEquiv).trans
      ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
        QuotientGroup.quotientBot))⟩

/-- The original A6 odd fixed residual acts by inner automorphisms on
each actual component of its odd normalizer. No outer-solvability or model
premise is required, and the original two-core and covering center remain. -/
private theorem six_odd_residual_inner
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    (A : Subgroup G) [IsMulCommutative A] (_hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (hno : ∀ U : Subgroup (MulAut.Outer K), ∀ f : U →* alternatingGroup (Fin 6),
      ¬ Function.Surjective f) :
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
  obtain ⟨eL⟩ := D.doubled_six_simple_quotient h hmodel
  let := h.quasisimple
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := eL.symm.isSimpleGroup
  let : Group.IsPerfect (alternatingGroup (Fin 6)) := Group.IsPerfect.ofSurjective
    (f := eL.toMonoidHom) eL.surjective
  let eR := (centerQuotientCongr b).trans eL
  let e := (centerQuotientCongr (QuotientGroup.congr _ _ a (pCore_map_iso 2 a))).trans eR
  let : Group.IsPerfect R := oddActorResidual_isPerfect L A
  let : Group.IsPerfect (R.subgroupOf N) := Group.IsPerfect.ofSurjective
    (f := a.symm.toMonoidHom) a.symm.surjective
  obtain ⟨_,hRK,_⟩ := chosen_oddNormalizer_component_normalization h.toHypothesis1221 D
    A hAN hAL ho hAV K hK
  exact perfect_actor_inner_of_core_central_quotient K (R.subgroupOf N) e hno hRK

/-- The selected A6 component contains the whole original
orbit and residual, has odd centralizer, and retains the full orbit rank eight.
Original residual uniqueness remains explicit at this intermediate endpoint. -/
private theorem six_oddNormalizer_placement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (hno : ∀ U : Subgroup (MulAut.Outer K), ∀ f : U →* alternatingGroup (Fin 6),
      ¬ Function.Surjective f) :
    K.Normal ∧ D.sourceOrbit ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) =
        pPrimeCore 2 (normalizer (A : Set G)) ∧
      8 ≤ primeRank 2 (K ⧸ center K) := by
  have hs : normalizer (L : Set G) ⊓ centralizer (V : Set G) ≤ sectionCentralizer L := by
    let := h.quasisimple
    apply relative_module_centralizer_le_sectionCentralizer L V D.normalizes _ D.ne_bot D.eq_commutator
    exact (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes
  have hA : A ≤ normalizer (L : Set G) ⊓
      centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
    rw [←D.sourceOrbit_eq]
    exact le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
  have hu := D.sourceOrbit_six_residual_uniqueness h hd hmodel A hAC ho
  have hi := D.six_odd_residual_inner h hd hmodel A hne hAC ho K hK hno
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
  have hc : Nat.card D.sourceOrbit = 2 ^ (8) := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)
    rw [Nat.card_congr Additive.toMul,Nat.card_zmod,D.sourceOrbit_six_dimension h hd hmodel] at hh
    exact hh
  have he := IsElementaryAbelian.log_card_eq_primeRank (p := 2) D.sourceOrbit
  rw [hc,Nat.log_pow (by decide : 1 < (2 : ℕ))] at he
  exact ⟨hKn,hw,hr,hcent,he ▸ hrQ⟩
/-- The actual Hall component either contains the whole orbit and residual,
or its full outer group has the original alternating-six section. -/
theorem sourceOrbit_six_oddNormalizer_placement_or_outer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G)) :
    (K.Normal ∧ D.sourceOrbit ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) =
        pPrimeCore 2 (normalizer (A : Set G)) ∧
      8 ≤ primeRank 2 (K ⧸ center K)) ∨
    ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* alternatingGroup (Fin 6),
      Function.Surjective f := by
  by_cases houter : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* alternatingGroup (Fin 6),
      Function.Surjective f
  · exact Or.inr houter
  · exact Or.inl (D.six_oddNormalizer_placement h hd hmodel A hne hAC ho hout K hK houtK
      (fun U f hf => houter ⟨U,f,hf⟩))

/-- Binary symplectic six-space forces actual original component placement;
no outer-solvability or inner-action guard is supplied. -/
theorem sourceOrbit_six_oddNormalizer_symplectic_placement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (hm : ClassicalGroup.IsPSp (K ⧸ center K) 3 2) :
    K.Normal ∧ D.sourceOrbit ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) =
        pPrimeCore 2 (normalizer (A : Set G)) ∧
      8 ≤ primeRank 2 (K ⧸ center K) := by
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsSolvable (MulAut.Outer (K ⧸ center K)) :=
    DoubledBinaryOddSymplectic.binary_outer_solvable hm
  let : Group.IsSolvable (MulAut.Outer K) := Group.isSolvable_of_isSolvable_injective
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact D.six_oddNormalizer_placement h hd hmodel A hne hAC ho hout K hK houtK
    (fun U f hf => Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6))
      (Group.isSolvable_of_surjective hf))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
