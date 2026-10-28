module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.Definitions
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.LiftingOrders
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Center
public import Theory.SpecificGroups.BinaryLinear.SylowCenters
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
/-!
# Model separations for the exceptional candidate

The actual quotient models have the specified orders. PSL₃(4) and PSL₄(2)
are separated by their Sylow two-center orders, four and at most two.
These facts discharge the model premises of the original 13.6.27 lift.
-/
public section
noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection
open Chapter1.Section02 Chapter1.Section02.LocalModels LiftingOrders

private theorem no_binary_four {X : Type*} [Group X]
    (eF : X ≃* L3Four) : ¬ ClassicalGroup.IsPSL X 4 2 := by
  rintro ⟨E, _, _, hE, ⟨eE⟩⟩
  let := Fintype.ofFinite E
  let e : E ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hE]
    simp)
  let b := eF.symm.trans (eE.trans (Atlas.fieldEquivPSL 4 e))
  let S := Matrix.PSL3.LinearThree.unipotentSylow F4 (by decide : 0 < 2)
    (show Nat.card F4 = 2^2 from by simpa using GaloisField.card 2 2 (by decide))
  have h := BinaryLinear.psl_sylow_center_card_le_two (by decide : 2 ≤ 4)
    (S.mapSurjective (f := b.toMonoidHom) b.surjective)
  rw [← BinaryLinear.sylow_center_card_congr b S] at h
  have hc := Matrix.PSL3.LinearThree.card_center_sylow F4 (by decide : 0 < 2)
    (show Nat.card F4 = 2^2 from by simpa using GaloisField.card 2 2 (by decide)) S
  change Nat.card (center S) ≤ 2 at h
  change Nat.card (center S) = 4 at hc
  omega

private theorem card_binary_four {G : Type*} [Group G]
    (h : ClassicalGroup.IsPSL G 4 2) : Nat.card G = 20160 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
  rw [hF] at hc
  norm_num [Fin.prod_univ_succ] at hc
  exact hc

/-- The concrete candidate supplies both numerical and structural sieve inputs. -/
theorem candidate_sieve_inputs {H : Type*} [Group H] {T K : Subgroup H}
    (hc : Candidate T K) :
    (∃ m, ExceptionalOrder m ∧ Nat.card (K ⧸ pCore 2 K) = m) ∧
      ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 4 2 := by
  rcases hc with hJ | hM | ⟨e, _⟩
  · obtain ⟨e⟩ := hJ
    have horder : Nat.card (K ⧸ pCore 2 K) = 604800 :=
      (Nat.card_congr e.toEquiv).trans
        Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier
    refine ⟨⟨604800, Or.inr (Or.inl rfl), horder⟩, ?_⟩
    intro h
    have := card_binary_four h
    omega
  · obtain ⟨e⟩ := hM
    have horder : Nat.card (K ⧸ pCore 2 K) = 10200960 :=
      (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m23_order
    refine ⟨⟨10200960, Or.inr (Or.inr rfl), horder⟩, ?_⟩
    intro h
    have := card_binary_four h
    omega
  · refine ⟨⟨20160, Or.inl rfl, ?_⟩, no_binary_four e⟩
    rw [Nat.card_congr e.toEquiv]
    exact Matrix.PSL3Four.card_PSL

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection
