module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Nonbinary.Reduction
public import Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.DisplacementRealization.Action

/-!
# Rank and literal root-action transfers for the displacement

The direct decomposition V = [V,L ∩ M] × C_V(L) identifies the action rank
with the binary logarithm of the displacement's order in any actual matrix
model. The central plane has order q² and either root has order q.
Conjugation by V is precisely conjugation by the moving factor; transport
through the inclusion Sp₄(F)′ ≃ Sp₄(F) retains the exact automorphism-image
equality required by `SymplecticRootAction`.

Source: Aschbacher–Smith E.6.8(2), printed pp.247–248
(PDF pp.258–259 of refs/quasithin.pdf).
-/

public section

open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open BorelActionGeometry.DisplacementRealization
open Theory.GroupAction.ModelConjugation
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.Nonbinary
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem inducedAutomizer_model_image {D : Type*} [Group D]
    (hN : V ≤ normalizer (L : Set G)) (e : L ≃* D) :
    ((inducedAutomizer L V).map (Automizer L).subtype).map (MulAut.congr e).toMonoidHom =
      (action V L hN e).range := by
  ext a
  constructor
  · rintro ⟨b, ⟨c, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨L.normalizerMonoidHom ⟨v, hN v.property⟩,
      ⟨L.normalizerMonoidHom.rangeRestrict ⟨v, hN v.property⟩,
        ⟨⟨v, hN v.property⟩, v.property, rfl⟩, rfl⟩, rfl⟩

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem actionCorank_eq_log_displacement_image
    (hclass : DiagramSemilinearCoverage)
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hn : 1 < n) (hm : SymplecticDerivedModel L n)
    (hB : ∃ B : Subgroup G, B ≤ L ⊓ M ∧ BorelPreimage L B) (e : L ≃* Sp F) :
    actionCorank V L = Nat.log 2 (Nat.card (((⁅V, L ⊓ M⁆).subgroupOf L).map e.toMonoidHom)) := by
  rw [← displacement_corank hclass h hU hL hn hm hB]
  change Nat.log 2 ((⊥ : Subgroup G).relIndex ⁅V, L ⊓ M⁆) = _
  rw [relIndex_bot_left, card_map_of_injective e.injective,
    Nat.card_congr (subgroupOfEquivOfLe (displacement_le_component h hU hL)).toEquiv]

omit [Finite F] in
theorem actionCorank_of_centralPlane_image
    (hclass : DiagramSemilinearCoverage)
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hn : 1 < n) (hm : SymplecticDerivedModel L n)
    (hB : ∃ B : Subgroup G, B ≤ L ⊓ M ∧ BorelPreimage L B)
    (hF : Nat.card F = 2 ^ n) (e : L ≃* Sp F)
    (hplane : ((⁅V, L ⊓ M⁆).subgroupOf L).map e.toMonoidHom =
      (CentralRootGeometry.parameter (F := F)).range) :
    actionCorank V L = 2 * n := by
  rw [actionCorank_eq_log_displacement_image hclass h hU hL hn hm hB e,
    hplane, BorelActionGeometry.card_centralPlane, hF, ← pow_mul,
    Nat.log_pow (by decide : 1 < 2), Nat.mul_comm]

omit [Finite F] [CharP F 2] in
theorem actionCorank_of_root_image
    (hclass : DiagramSemilinearCoverage)
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hn : 1 < n) (hm : SymplecticDerivedModel L n)
    (hB : ∃ B : Subgroup G, B ≤ L ⊓ M ∧ BorelPreimage L B)
    (hF : Nat.card F = 2 ^ n) (e : L ≃* Sp F) (r : Fin 8)
    (hroot : ((⁅V, L ⊓ M⁆).subgroupOf L).map e.toMonoidHom = RootSubgroup.group r) :
    actionCorank V L = n := by
  rw [actionCorank_eq_log_displacement_image hclass h hU hL hn hm hB e,
    hroot, RootSubgroup.card, hF, Nat.log_pow (by decide : 1 < 2)]

theorem rootAction_of_displacement_image
    (hclass : DiagramSemilinearCoverage)
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hn : 1 < n) (hm : SymplecticDerivedModel L n)
    (hB : ∃ B : Subgroup G, B ≤ L ⊓ M ∧ BorelPreimage L B)
    (hF : Nat.card F = 2 ^ n) (e : L ≃* Sp F) (r : Fin 8)
    (hroot : ((⁅V, L ⊓ M⁆).subgroupOf L).map e.toMonoidHom = RootSubgroup.group r) :
    SymplecticRootAction L V n := by
  have hN := component_normalized_by_V h hU hL
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (by decide : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hn
  let d := derivedEquivFull_of_card_gt_two hlarge
  refine ⟨hN, F, inferInstance, inferInstance, hF, e.trans d.symm, r, ?_⟩
  change ((inducedAutomizer L V).map (Automizer L).subtype).map
    ((MulAut.congr d.symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom) =
      (RootSubgroup.group (F := F) r).map (MulAut.conjNormal (H := commutator (Sp F)))
  rw [← map_map, inducedAutomizer_model_image hN e,
    action_range_of_central_factor hN e (decomposition hclass h hU hL hn hm hB).1
      (displacement_le_component h hU hL) inf_le_right,
    hroot, map_map]
  apply congrArg (fun f : Sp F →* MulAut (commutator (Sp F)) => (RootSubgroup.group r).map f)
  apply MonoidHom.ext
  exact congr_conj_derived hlarge

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.Nonbinary
