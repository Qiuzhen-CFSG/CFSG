module
public import Theory.SpecificGroups.AlternatingSeven.CentralCoverParabolic
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.GroupTheory.PCoreRestriction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Two-cores normalizing a binary-three section in A₇

Let D be a normal A₇ in a finite group, and B ≤ D with B/O₂(B) ≅ GL₃(2).
The order of A₇ forces |B| = 168 and O₂(B) = 1. If B ≤ E ≤ N(B),
then [B,O₂(E)] lies in O₂(B), so O₂(E) centralizes B. Automorphism
rigidity for a nonsolvable seven-divisible subgroup of A₇ then shows that
O₂(E) centralizes D.

The natural-module application uses the literal image of L₁ and the image
of L₁T in K₁T/O₂(K₁T). This removes the A₇ row using its quadratic actor.
Source context: Aschbacher--Smith 12.9.5--7, printed pp.860--862;
GLS III, Theorem 5.2.1, via `AlternatingSeven.SevenFixer`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace AlternatingSeven
open BinaryLinear.OuterCyclic

private theorem linear_three_card : Nat.card (LinearGroup 3) = 168 := by
  rw [←Nat.card_congr (matrixEquivLinear 3).toEquiv,Matrix.card_GL_field]
  norm_num
  decide

/-- The two-core of a normalizing overgroup centralizes the normal A₇. -/
theorem parabolic_core_centralizes
    {G : Type*} [Group G] [Finite G] (D B E : Subgroup G) [D.Normal]
    (hBD : B ≤ D) (hBE : B ≤ E) (hEB : E ≤ normalizer (B : Set G))
    (eD : D ≃* alternatingGroup (Fin 7))
    (eB : (B ⧸ pCore 2 B) ≃* LinearGroup 3) :
    E.pCoreIn 2 ≤ centralizer (D : Set G) := by
  let : Finite (LinearGroup 3) := Finite.of_surjective eB eB.surjective
  have hq : Nat.card (B ⧸ pCore 2 B) = 168 :=
    (Nat.card_congr eB.toEquiv).trans linear_three_card
  have hd : Nat.card B ∣ 7560 := by
    have hh := card_dvd_of_le hBD
    rw [Nat.card_congr eD.toEquiv,nat_card_alternatingGroup,Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    exact hh.trans (by decide : 2520 ∣ 7560)
  obtain ⟨hcore,hcard⟩ := CentralCoverParabolic.twoCore_eq_bot_of_binary_three_section hd hq
  have hns : ¬ Group.IsSolvable B := by
    intro hs
    let := hs
    let : Group.IsSolvable (LinearGroup 3) :=
      Group.isSolvable_of_surjective (f := eB.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B)))
        (eB.surjective.comp (QuotientGroup.mk'_surjective _))
    let : Group.IsPerfect (LinearGroup 3) := BinaryLinear.linearGroup_isPerfect 3 (by decide)
    let : Nontrivial (LinearGroup 3) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [linear_three_card]; decide)
    exact Group.IsPerfect.not_isSolvable (LinearGroup 3) inferInstance
  have h7 : 7 ∣ Nat.card B := by rw [hcard]; decide
  have hEN : E ≤ normalizer (E.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
      using (pCore 2 E).le_normalizer_map E.subtype
  have hc : ⁅B,E.pCoreIn 2⁆ = ⊥ := by
    apply bot_unique
    have hb : B.pCoreIn 2 = ⊥ := by rw [pCoreIn,hcore,Subgroup.map_bot]
    apply le_trans _ ((inf_pCoreIn_le_of_le 2 hBE).trans hb.le)
    exact le_inf
        (le_normalizer_iff_commutator_le_left.mp ((pCoreIn_le 2 E).trans hEB))
        (le_normalizer_iff_commutator_le_right.mp (hBE.trans hEN))
  have hfix : E.pCoreIn 2 ≤ centralizer (B : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
  intro a ha
  exact SevenFixer.centralizes_of_centralizes_subgroup D B hBD eD hns h7 a
    (le_normalizer_of_normal (mem_top a)) (hfix ha)
end AlternatingSeven
