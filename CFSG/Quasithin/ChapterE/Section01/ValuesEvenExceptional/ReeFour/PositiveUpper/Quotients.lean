module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.SimpleSocle
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer
public import Theory.SpecificGroups.Suzuki.TwoRank
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearQuotient
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.ElementaryAbelian.GeneratorRank

/-!
# E-generation of the exact Ree rank-one quotients

At positive parameters the actual Suzuki and PSL₂ quotient groups are
nonabelian simple. The whole group is therefore a genuine E2-member for
every nontrivial elementary subgroup, by the proved simple-socle calculation:
the radical is trivial, the two-residual equals the solvable residual, and
the component's local tau orbit is the whole layer. The canonical radical
quotient cannot increase the elementary rank.

The Suzuki rank is 2*m+1. For the linear quotient, the characteristic-two
SL₂–PSL₂ equivalence and the additive-field Sylow subgroup bound the order
of every elementary subgroup by 2^(2*m+1). These prove the two generation
bounds consumed by the actual Ree local factors in `PositiveUpper`.

Source: Aschbacher–Smith E.1.2, E.1.5 and E.1.14(1), printed pp.210,214
of `refs/quasithin.pdf`; E.1.14 cites Aschbacher (1982), Lemma 4.7,
DOI 10.2307/2374202. The exact quotient models are those in F.1.12(I)(5).
-/

public section

namespace CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour.PositiveUpper
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

private theorem simple_isEGenerated_of_rank {H : Type*} [Group H] [Finite H]
    [IsSimpleGroup H] (hna : ¬ IsMulCommutative H) {n : ℕ}
    (hrank : ∀ A : Subgroup H, IsElementaryAbelian 2 A → Group.rank A ≤ n) :
    IsEGenerated n H := by
  let : Group.IsPerfect H := ⟨
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator H)
      inferInstance).resolve_left (fun h => hna ((commutator_eq_bot_iff H).mp h))⟩
  have hz : center H = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center H) inferInstance).resolve_right
      (fun h => hna (center_eq_top_iff.mp h))
  let : IsQuasisimple H := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  have hF : generalizedFitting H = ⊤ := generalizedFitting_eq_top_of_quasisimple
  let e : generalizedFitting H ≃* H := (MulEquiv.subgroupCongr hF).trans topEquiv
  let : IsSimpleGroup (generalizedFitting H) := e.isSimpleGroup
  have ha : ¬ IsMulCommutative (generalizedFitting H) := by
    intro h
    let := h
    apply hna
    exact IsMulCommutative.of_comm fun x y => e.symm.injective (by
      simp only [map_mul, mul_comm])
  intro T
  apply ValuesEvenClassical.RankOneUpper.isEGeneratedAt_of_top_component_and_rank T
  · intro A _ _ hA
    exact ValuesEvenClassical.RankOneUpper.eCaseComponent_top ha T
      (by rw [hF, top_sup_eq]) _ A hA
  · intro A hA _
    exact hrank A hA

/-- The genuine Suzuki quotient is E-generated at the Ree field exponent. -/
theorem suzuki_quotient_isEGenerated {m : ℕ} (hm : 0 < m) :
    IsEGenerated (2 * m + 1) (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  apply simple_isEGenerated_of_rank
  · intro h
    let := h
    exact BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm inferInstance
  · intro A hA
    let := hA
    exact (A.rank_le_primeRank 2 (IsElementaryAbelian.isPGroup 2 A)).trans
      (BenderSuzuki.MatrixGroups.suzuki_two_rank m hm).le

/-- The genuine PSL₂ quotient is E-generated at the same field exponent. -/
theorem linear_quotient_isEGenerated {m : ℕ} (hm : 0 < m) :
    IsEGenerated (2 * m + 1) (ReeF4.LargeLocalSeeds.LinearQuotient m) := by
  let F := ReeF4.CoefficientField m
  let e := Theory.PSL2.sl2QuotientEquiv F
  let := ReeF4.LargeLocalSeeds.linearQuotient_simple m hm
  apply simple_isEGenerated_of_rank
  · intro h
    let := h
    let : IsMulCommutative (Matrix.SpecialLinearGroup (Fin 2) F) :=
      IsMulCommutative.of_comm fun x y => e.injective (by simp only [map_mul, mul_comm])
    exact Matrix.SpecialLinearGroup.upperUnipotent_not_normal F inferInstance
  · intro A hA
    let := hA
    let B := A.map e.symm.toMonoidHom
    obtain ⟨P, hP⟩ := ((IsElementaryAbelian.isPGroup 2 A).map
      e.symm.toMonoidHom).exists_le_sylow
    apply IsElementaryAbelian.rank_le_of_card_le (p := 2) A
    calc
      Nat.card A = Nat.card B := Nat.card_congr (e.symm.subgroupMap A).toEquiv
      _ ≤ Nat.card P := Nat.card_le_card_of_injective (Subgroup.inclusion hP)
        (Subgroup.inclusion_injective hP)
      _ = Nat.card F := (Nat.card_congr
        (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 P).toEquiv).symm
      _ = 2 ^ (2 * m + 1) := ReeF4.field_card m

end CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour.PositiveUpper
