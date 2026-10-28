module
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.RankOneExchange
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Flags
public import Theory.GroupTheory.PResidual.OrderSix
public import Theory.GroupTheory.PResidual.PCoreQuotient
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The cubic residual of a binary rank-one parabolic

A cover of a Sylow two-subgroup deletes one cut of its complete flag.
Its diagonal quotient has one two-dimensional binary block, hence order
six. The two-residual has order three there, and the actual two-group
kernel preserves its intrinsic two-core quotient.

Source application: Aschbacher--Smith, 10.2.9, printed p.753.
-/

public section
open Subgroup
namespace BinaryLinear.FiveFlagGeometry
open OuterCyclic SmallParabolicLevi SmallParabolicLevi.TwoNodes
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

/-- Cardinality of the actual binary linear group on an arbitrary finite coordinate set. -/
theorem coordinateLinear_card {α : Type*} [Fintype α] :
    Nat.card (BinaryLinear.GL (α → ZMod 2)) =
      ∏ j : Fin (Fintype.card α), (2^(Fintype.card α) - 2^j.val) := by
  let e : (α → ZMod 2) ≃ₗ[ZMod 2] Space (Fintype.card α) :=
    LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (Fintype.equivFin α).symm
  rw [Nat.card_congr (linearGroupCongr e).toEquiv,
    ←Nat.card_congr (matrixEquivLinear _).toEquiv,Matrix.card_GL_field]
  simp

/-- Deleting one cut leaves one binary two-space block, of linear order six. -/
theorem rankOne_quotient_card (S : Sylow 2 (LinearGroup 5))
    (P : Subgroup (LinearGroup 5)) (hP : (S : Subgroup _) ⋖ P) :
    Nat.card (P ⧸ pCore 2 P) = 6 := by
  obtain ⟨b,hb⟩ := sylow_eq_flagStabilizer S
  obtain ⟨i,rfl⟩ := (fullFlag_covBy_iff b P).mp (hb ▸ hP)
  rw [Nat.card_congr (flagDiagonalQuotientEquiv b {i}ᶜ).toEquiv,Nat.card_pi]
  simp_rw [coordinateLinear_card]
  have hlabel : ∀ i : Fin 4, cutLabel {i}ᶜ =
      (![![0,0,1,2,3],![0,1,1,2,3],![0,1,2,2,3],![0,1,2,3,3]] : Fin 4 → Fin 5 → Fin 5) i := by
    intro i
    funext j
    fin_cases i <;> fin_cases j <;> simp [cutLabel,
      show (Finset.univ : Finset (Fin 4)) = {0,1,2,3} from by decide,
      Finset.filter_insert,Finset.filter_singleton]
  rw [hlabel]
  fin_cases i <;> decide

/-- The two-residual of the actual rank-one node has core quotient of order three. -/
theorem rankOne_residual_quotient_card (S : Sylow 2 (LinearGroup 5))
    (P : Subgroup (LinearGroup 5)) (hP : (S : Subgroup _) ⋖ P) :
    Nat.card (pResidual 2 P ⧸ pCore 2 (pResidual 2 P)) = 3 := by
  let q := QuotientGroup.mk' (pCore 2 P)
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  rw [Nat.card_congr (q.pResidualCoreQuotientEquiv (QuotientGroup.mk'_surjective _) hk).toEquiv]
  have hc : Nat.card (pResidual 2 (P ⧸ pCore 2 P)) = 3 :=
    card_twoResidual_of_card_six (rankOne_quotient_card S P hP)
  have hz : pCore 2 (pResidual 2 (P ⧸ pCore 2 P)) = ⊥ := by
    apply card_eq_one.mp
    rcases (pCore_isPGroup (p := 2) (G := pResidual 2 (P ⧸ pCore 2 P))).card_eq_or_dvd with h | h
    · exact h
    · have hd := h.trans (pCore 2 (pResidual 2 (P ⧸ pCore 2 P))).card_subgroup_dvd_card
      rw [hc] at hd
      omega
  rw [hz,Nat.card_congr QuotientGroup.quotientBot.toEquiv,hc]

/-- A two-group kernel preserves the residual quotient for every original node. -/
theorem rankOne_residual_quotient_card_of_two_kernel
    {H : Type*} [Group H] [Finite H]
    (f : H →* LinearGroup 5) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (S : Sylow 2 H) (P : Subgroup H) (hP : (S : Subgroup H) ⋖ P) :
    Nat.card (pResidual 2 P ⧸ pCore 2 (pResidual 2 P)) = 3 := by
  have hs := hk.le_sylow_of_normal S
  have hc : (S.mapSurjective hf : Subgroup (LinearGroup 5)) ⋖ P.map f := by
    apply (comap_covBy_iff_of_surjective f hf _ _).mp
    rw [Sylow.coe_mapSurjective,comap_map_eq_self hs,comap_map_eq_self (hs.trans hP.le)]
    exact hP
  have hpker : IsPGroup 2 (f.subgroupMap P).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  rw [Nat.card_congr ((f.subgroupMap P).pResidualCoreQuotientEquiv
    (f.subgroupMap_surjective P) hpker).toEquiv]
  exact rankOne_residual_quotient_card (S.mapSurjective hf) (P.map f) hc
end BinaryLinear.FiveFlagGeometry
