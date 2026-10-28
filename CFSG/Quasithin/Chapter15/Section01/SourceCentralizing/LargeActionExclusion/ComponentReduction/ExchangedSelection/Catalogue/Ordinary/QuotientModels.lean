module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Alternatives
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Ordinary.Catalogue
public import Theory.SpecificGroups.Triality.BinaryCenter

/-!
# Passing the ordinary source conclusions to the quotient consumer

The binary and M11 source rows identify L itself. Their proved centerlessness
therefore removes its two-core. The sporadic rows identify L/Z(L), and the
source identity Z(L)=O₂(L) changes the denominator. In the binary linear
rows the same flag-model equivalence supplies the actual PSL quotient.

These are consequences of the stated source conclusions, not proofs of
their exhaustiveness. They provide the `OrdinaryPostRankOneModel` interface
used by the existing ordinary-elimination consumer once the separate
15.1.20--22 source producers are assembled.
Source: Aschbacher--Smith 15.1.20(3c--e), 15.1.22(4--7), pp.1094--1100.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ClassificationModels
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private noncomputable def quotientEquivOfCenterlessModel
    (d : CaseIComponentData T M Mc V) (hc : center d.L = pCore 2 d.L)
    {X : Type*} [Group X] (e : d.L ≃* X) (hx : center X = ⊥) :
    (d.L ⧸ pCore 2 d.L) ≃* X := by
  have hL : center d.L = ⊥ := by
    apply bot_unique
    intro x hxc
    have he := (centerCongr e ⟨x,hxc⟩).property
    change e x ∈ center X at he
    rw [hx, mem_bot] at he
    exact mem_bot.mpr (e.injective (he.trans (map_one e).symm))
  exact ((QuotientGroup.quotientMulEquivOfEq (hc.symm.trans hL)).trans
    QuotientGroup.quotientBot).trans e

private theorem binaryRankTwo_quotient_model
    (d : CaseIComponentData T M Mc V) (hc : center d.L = pCore 2 d.L)
    (hm : OrdinaryBinaryRankTwo d.L) : OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) := by
  unfold OrdinaryBinaryRankTwo at hm
  rcases hm with hm | hm | hm <;> obtain ⟨e⟩ := hm
  · exact Or.inr (Or.inl (Or.inr (Or.inl
      ⟨quotientEquivOfCenterlessModel d hc e g2.1⟩)))
  · have hz : center Tits.ParrottGroup = ⊥ := by
      have hf := Facts.of_equiv Tits.parrottFiniteImageEquiv tits_facts
      exact hf.1
    exact Or.inr (Or.inl (Or.inr (Or.inr
      ⟨quotientEquivOfCenterlessModel d hc e hz⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨quotientEquivOfCenterlessModel d hc e
        (Triality.Standard.binaryCarrier_center_eq_bot 1 Nat.zero_lt_one)⟩))))

private theorem linear_quotient_model
    (d : CaseIComponentData T M Mc V) (hc : center d.L = pCore 2 d.L)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) := by
  let q := quotientEquivOfCenterlessModel d hc e (linear hn).1
  refine Or.inr (Or.inl (Or.inl ⟨n,hn,?_⟩))
  exact ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2,
    ⟨q.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega)).symm⟩⟩

/-- The five source rows imply precisely the existing quotient interface
once the two rank-one exclusions have been proved, retaining HS and Ru. -/
theorem Ordinary20Alternatives.postRankOneModel
    {d : CaseIComponentData T M Mc V} (ha : d.Ordinary20Alternatives)
    (hc : center d.L = pCore 2 d.L)
    (hB : ¬ (IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)))
    (hH : ¬ d.OrdinaryHigherField) : OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) := by
  cases ha with
  | rankOne hm _ => exact (hB hm).elim
  | higherField hm _ _ => exact (hH hm).elim
  | binaryRankTwo hm _ => exact binaryRankTwo_quotient_model d hc hm
  | sporadic name hn3 hn4 hm _ =>
      cases name with
      | m11 => exact .inl (.inl hm)
      | m12 => exact .inl (.inr (.inl hm))
      | m22 => exact .inl (.inr (.inr (.inl hm)))
      | m23 => exact .inl (.inr (.inr (.inr (.inl hm))))
      | m24 => exact .inl (.inr (.inr (.inr (.inr (.inl hm)))))
      | j2 => exact .inl (.inr (.inr (.inr (.inr (.inr hm)))))
      | j3 => exact (hn3 rfl).elim
      | j4 => exact (hn4 rfl).elim
      | hs => exact .inr (.inr (.inl hm))
      | he => exact .inr (.inr (.inr (.inl hm)))
      | ru => exact .inr (.inr (.inr (.inr (.inl hm))))
  | linear n hn e _ _ => exact linear_quotient_model d hc hn e

/-- All four ordinary 15.1.22 rows feed the actual quotient interface,
without assuming any facts about an unidentified quotient. -/
theorem Ordinary22Alternatives.postRankOneModel
    {d : CaseIComponentData T M Mc V} (ha : d.Ordinary22Alternatives)
    (hc : center d.L = pCore 2 d.L) : OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) := by
  cases ha with
  | binaryRankTwo hm _ _ _ _ _ _ _ => exact binaryRankTwo_quotient_model d hc hm
  | sporadic name hn hm _ _ =>
      obtain ⟨e⟩ := hm
      have hq : Nonempty ((d.L ⧸ pCore 2 d.L) ≃* name.Carrier) :=
        ⟨(QuotientGroup.quotientMulEquivOfEq hc.symm).trans e⟩
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
      · exact .inl (.inr (.inl hq))
      · exact .inl (.inr (.inr (.inl hq)))
      · exact .inl (.inr (.inr (.inr (.inl hq))))
      · exact .inl (.inr (.inr (.inr (.inr (.inl hq)))))
      · exact .inl (.inr (.inr (.inr (.inr (.inr hq)))))
      · exact .inr (.inr (.inr (.inl hq)))
  | mathieuEleven hm _ _ =>
      obtain ⟨e⟩ := hm
      exact .inl (.inl ⟨quotientEquivOfCenterlessModel d hc e Sporadic.Mathieu.m11_center_eq_bot⟩)
  | linear n hn e _ _ _ _ _ => exact linear_quotient_model d hc hn e

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
