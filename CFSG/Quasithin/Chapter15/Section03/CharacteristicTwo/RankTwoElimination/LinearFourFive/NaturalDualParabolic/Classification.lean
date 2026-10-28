module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Classification.RadicalLayer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.CenterObstruction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.MSData
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.ChiefCases

/-!
# The complete C.1.34 sieve for the natural-plus-dual point parabolic

The binary MS input supplies the exact C.1.31 contract: centerlessness
identifies O₂,Z with O₂, and the actual SL₃(2) is perfect. We transport the
source core [O₂(J),O²(P)] to Q_P through the marked subgroup inclusion.
The actual natural layer models force orders 8, 64, and 16 in cases (1),
(2), and (5), contradicting |Q_P| ≥ 128. In case (3) they force an intrinsic
center of order 8, contradicting the central subgroup of order 16. Case (4)
is excluded by the central four-group and a nonidentity Sylow-fixed vector
in its disjoint natural summand, using the transported 15.3.8 rank bound.

`false_of_universalClassification` retains the full universal C.1.34
implication as an explicit premise. This module proves its application,
not that earlier classification. The ambient MS construction and module-core
containment also remain independent inputs; no realization is assumed here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.31–34,
printed pp.135–137, and 15.3.24, printed pp.1129–1130.
-/

@[expose] public section
open Subgroup BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
universe u
variable {G : Type u} [Group G]
variable {d : LocalData G} {L : Subgroup G} {κ : GroupClass.{u}}

/-- The genuine binary input satisfies every clause of the full MS-pair contract. -/
theorem binaryInput_sourcePair {D : Type u} [Group D] [Finite D]
    {K R : Subgroup D} (b : ChapterC.BinaryMS.Input κ K R) : MSPair κ D K R := by
  refine ⟨inferInstance, b.sqtk, b.fitting, b.product, b.component, ?_,
    Or.inl b.radical, b.characteristic⟩
  apply RankTwoDerived.linear (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) 1 (by decide)
  · exact ⟨ZMod 2, inferInstance, inferInstance, by simp,
      ⟨(projectiveEquivSL (by decide : 0 < 3)).symm⟩⟩
  · exact ⟨b.derivedQuotientEquiv⟩

/-- The source core is carried to Q_P by the original ambient inclusion. -/
noncomputable def MSData.sourceCoreEquiv {h : NaturalDual d L} {x : Space 4}
    (m : MSData κ h x) :
    sourceQ (residualComponent h x) ≃* coreCommutator (point h x) :=
  ((sourceQ (residualComponent h x)).equivMapOfInjective
    (residualOvergroup h x).subtype (residualOvergroup h x).subtype_injective).trans
      (MulEquiv.subgroupCongr m.core_eq)

/-- Intrinsic centers have equal order under the marked core identification. -/
theorem MSData.sourceCenter_card {h : NaturalDual d L} {x : Space 4}
    (m : MSData κ h x) :
    Nat.card (sourceCenter (residualComponent h x)) =
      Nat.card (center (coreCommutator (point h x))) := by
  exact (Nat.card_congr ((center (sourceQ (residualComponent h x))).equivMapOfInjective
    (sourceQ (residualComponent h x)).subtype
    (sourceQ (residualComponent h x)).subtype_injective).toEquiv).symm.trans
    (Nat.card_congr (centerCongr m.sourceCoreEquiv).toEquiv)

private theorem natural_upper_card {D : Type*} [Group D] {K A : Subgroup D}
    {e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    {a : ℕ} (n : LayerModel K A ⊥ e (NaturalCopies (ZMod 2) a)) :
    Nat.card A = 8 ^ a := by
  rw [Nat.card_congr n.upperIso.toEquiv]
  simp [Nat.card_eq_fintype_card]

private theorem natural_quotient_card {D : Type*} [Group D] {K A B : Subgroup D}
    {e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    {a : ℕ} (n : LayerModel K A B e (NaturalCopies (ZMod 2) a)) :
    Nat.card A = 8 ^ a * Nat.card B := by
  let := n.lower_normal
  rw [card_eq_card_quotient_mul_card_subgroup (B.subgroupOf A),
    Nat.card_congr n.quotientIso.toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe n.lower_le).toEquiv]
  simp [Nat.card_eq_fintype_card]

variable [Finite G]

/-- Every alternative of the full source witness contradicts the parabolic geometry. -/
theorem not_source_alternatives (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (m : MSData κ h x) (hU : spanCommutator d L ≤ (point h x).pCoreIn 2)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZS : Nat.card d.ZS = 4)
    (S : Sylow 2 (residualOvergroup h x))
    (hS : (S : Subgroup (residualOvergroup h x)).map (residualOvergroup h x).subtype = d.S)
    (e : (residualComponent h x ⧸ pCore 2 (residualComponent h x)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (ha : Alternatives (ZMod 2) 1 (residualComponent h x) (sylowPart h x) S e) :
    False := by
  have hQ : 128 ≤ Nat.card (sourceQ (residualComponent h x)) := by
    rw [Nat.card_congr m.sourceCoreEquiv.toEquiv]
    exact coreCommutator_card_ge h hx hU
  let := m.input.component_normal
  have hr := LinearThree.local_centralOmega_rank_le_two d (residualOvergroup h x)
    S hS hindex hZ hZS
  rcases LinearThree.alternatives_without_four S hr ha with ha | ha
  · cases ha with
    | one _ hn =>
      obtain ⟨n⟩ := hn
      have hc := natural_upper_card n
      norm_num at hc
      omega
    | two hn _ =>
      obtain ⟨n⟩ := hn
      have hc := natural_upper_card n
      norm_num at hc
      omega
    | three hn _ _ =>
      obtain ⟨n⟩ := hn
      have hc := natural_upper_card n
      rw [m.sourceCenter_card] at hc
      exact not_center_card_eight h hx hU (by simpa using hc)
  · obtain ⟨n⟩ := ha.natural
    have hc := natural_quotient_card n
    rw [ha.fixed_order] at hc
    norm_num at hc
    omega

/-- Apply the full universal C.1.34 implication, with all local inputs discharged. -/
theorem false_of_universalClassification
    (classification : UniversalClassification.{u})
    (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0)
    (m : MSData κ h x) (hU : spanCommutator d L ≤ (point h x).pCoreIn 2)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZS : Nat.card d.ZS = 4) : False := by
  obtain ⟨S, hS⟩ := m.sylow
  have hRS : sylowPart h x ≤ (S : Subgroup (residualOvergroup h x)) := by
    intro s hs
    have hm : (s : G) ∈ (S : Subgroup (residualOvergroup h x)).map
        (residualOvergroup h x).subtype := hS.symm ▸ hs
    obtain ⟨t, ht, he⟩ := hm
    exact (Subtype.ext he : t = s) ▸ ht
  obtain ⟨e, he⟩ := classification κ (residualOvergroup h x)
    (residualComponent h x) (sylowPart h x) (binaryInput_sourcePair m.input)
    (ZMod 2) 1 (by decide) (by simp) ⟨m.input.quotientEquiv⟩ S hRS
  exact not_source_alternatives h hx m hU hindex hZ hZS S hS e he

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic
end
