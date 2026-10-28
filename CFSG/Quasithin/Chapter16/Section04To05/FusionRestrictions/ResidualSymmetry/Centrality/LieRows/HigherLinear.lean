module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.LieRows.Actions
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.HigherLinear.Reduction

/-!
# Separating the higher-linear centrality rows

In PSL₄(2) the root, j₂, and graph residuals have two-parts 32, 4, and 8.
The exceptional three-transposition actor has the same residual A₄ as j₂,
and both actors are noncentral. In PSL₅(2) the root, j₂, and graph two-parts
are 1024, 256, and 8. Hence no central row is isomorphic to a noncentral row.
The O³ modification preserves these two-parts and causes no extra cases.

The earlier table is an explicit universal input on actual linear actions:
root and rank-two matrix types, Sylow-centrality markings, exact extensions,
and the marked eight-point exceptional action are all retained. The j₂
kernel in dimension five has order 256; no elementary-kernel claim is made.
The source-theorem owner still has to supply this table and the trivial-center
covering clause. This module proves the comparison, not the earlier table.

Source: Aschbacher–Smith, 16.1.4(1),(3),(8),(9), pp.1170–1171,
16.5.5–6(4), p.1197, and the corrected PSL₅(2) expression in 16.5.12, p.1200.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.LieRows.HigherLinear
open Subgroup BinaryLinear.OuterCyclic
open SylowSymmetry.ReverseDelta.Comparison.HigherLinear
open Theory.SpecificGroups.SymmetricEight.Involutions

private instance finite_linearGroup (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n))
    DFunLike.coe_injective

/-- Root residual extensions in the two binary dimensions. -/
def RootResidual (n : ℕ) (X : Type*) [Group X] : Prop :=
  (n = 4 ∧ Nonempty (TwoKernelExtension X C3 5)) ∨
  (n = 5 ∧ Nonempty (TwoKernelExtension X (LinearGroup 3) 7))

/-- The rank-two rows; the five-dimensional kernel is the corrected one. -/
def J2Residual (n : ℕ) (X : Type*) [Group X] : Prop :=
  (n = 4 ∧ Nonempty (X ≃* A4)) ∨
  (n = 5 ∧ Nonempty (TwoKernelExtension X C3 8))

/-- A single marked source row of an actual involutory automorphism.
The markings concern each actor individually and assert no row comparison. -/
inductive InvolutionRow (n : ℕ) (a : MulAut (LinearGroup n)) : Prop
  | root (x : LinearGroup n) (action : a = MulAut.conj x)
      (type : IsTransvection x)
      (central : IsTwoCentralIn (MulAut.innerSubgroup (LinearGroup n)) a)
      (residual : RootResidual n (pResidual 2 a.fixedSubgroup))
  | j2 (x : LinearGroup n) (action : a = MulAut.conj x)
      (type : Module.finrank (ZMod 2)
        (LinearMap.range (x.toLinearMap - LinearMap.id)) = 2)
      (noncentral : ¬ IsTwoCentralIn (MulAut.innerSubgroup (LinearGroup n)) a)
      (residual : J2Residual n (pResidual 2 a.fixedSubgroup))
  | graph (outer : ¬ ∃ x, a = MulAut.conj x)
      (residual : Nonempty (pResidual 2 a.fixedSubgroup ≃* A6))
  | exceptional (dimension : n = 4)
      (marking : ∃ e : LinearGroup n ≃* alternatingGroup (Fin 8),
        (automorphismPermutationEquiv e a).cycleType = {2, 2, 2})
      (residual : Nonempty (pResidual 2 a.fixedSubgroup ≃* A4))

/-- Exactly the earlier table coverage needed by this comparison. -/
def InvolutionTable : Prop :=
  ∀ n : ℕ, n = 4 ∨ n = 5 → ∀ a : MulAut (LinearGroup n),
    orderOf a = 2 → InvolutionRow n a

private theorem c3_card : Nat.card C3 = 3 := by
  simp [C3, Nat.card_eq_fintype_card]

private theorem a4_card : Nat.card A4 = 12 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private theorem a6_card : Nat.card A6 = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private theorem linear_three_card : Nat.card (LinearGroup 3) = 168 := by
  calc
    Nat.card (LinearGroup 3) = Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :=
      (Nat.card_congr (matrixEquivLinear 3).toEquiv).symm
    _ = ∏ i : Fin 3, (Fintype.card (ZMod 2) ^ 3 - Fintype.card (ZMod 2) ^ i.val) :=
      Matrix.card_GL_field (𝔽 := ZMod 2) 3
    _ = 168 := by decide

private theorem twoValuation_pow_mul (n m : ℕ) (hm : ¬ 2 ∣ m) :
    padicValNat 2 (2 ^ n * m) = n := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 2)
  rw [padicValNat.mul (pow_ne_zero _ (by decide)) hm0,
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm, add_zero]

private theorem root_valuation {n : ℕ} {X : Type*} [Group X] [Finite X]
    (h : RootResidual n X) :
    (n = 4 ∧ padicValNat 2 (Nat.card X) = 5) ∨
    (n = 5 ∧ padicValNat 2 (Nat.card X) = 10) := by
  rcases h with ⟨hn, ⟨s⟩⟩ | ⟨hn, ⟨s⟩⟩
  · refine Or.inl ⟨hn, ?_⟩
    rw [s.card, c3_card]
    exact twoValuation_pow_mul 5 3 (by decide)
  · refine Or.inr ⟨hn, ?_⟩
    rw [s.card, linear_three_card]
    change padicValNat 2 (2 ^ 10 * 21) = 10
    exact twoValuation_pow_mul 10 21 (by decide)

private theorem j2_valuation {n : ℕ} {X : Type*} [Group X] [Finite X]
    (h : J2Residual n X) :
    (n = 4 ∧ padicValNat 2 (Nat.card X) = 2) ∨
    (n = 5 ∧ padicValNat 2 (Nat.card X) = 8) := by
  rcases h with ⟨hn, ⟨e⟩⟩ | ⟨hn, ⟨s⟩⟩
  · refine Or.inl ⟨hn, ?_⟩
    rw [Nat.card_congr e.toEquiv, a4_card]
    exact twoValuation_pow_mul 2 3 (by decide)
  · refine Or.inr ⟨hn, ?_⟩
    rw [s.card, c3_card]
    exact twoValuation_pow_mul 8 3 (by decide)

private theorem central_mem {n : ℕ} {a : MulAut (LinearGroup n)}
    (ha : IsTwoCentralIn (MulAut.innerSubgroup (LinearGroup n)) a) :
    ∃ x, a = MulAut.conj x := by
  obtain ⟨x, hx⟩ := (twoCentral_iff_odd_index.mp ha).2.1
  exact ⟨x, hx.symm⟩

/-- The central row has the root two-part in each dimension. -/
theorem InvolutionRow.central_valuation {n : ℕ} {a : MulAut (LinearGroup n)}
    (row : InvolutionRow n a)
    (ha : IsTwoCentralIn (MulAut.innerSubgroup (LinearGroup n)) a) :
    (n = 4 ∧ padicValNat 2 (Nat.card (pResidual 2 a.fixedSubgroup)) = 5) ∨
    (n = 5 ∧ padicValNat 2 (Nat.card (pResidual 2 a.fixedSubgroup)) = 10) := by
  cases row with
  | root _ _ _ _ hr => exact root_valuation hr
  | j2 _ _ _ h _ => exact (h ha).elim
  | graph ho _ => exact (ho (central_mem ha)).elim
  | exceptional _ mark _ =>
    obtain ⟨e, he⟩ := mark
    exact (outer_of_threePairs e a he (twoCentral_iff_odd_index.mp ha).2.1).elim

/-- Every noncentral row has a different two-part, including both A₄ rows. -/
theorem InvolutionRow.noncentral_valuation {n : ℕ} {a : MulAut (LinearGroup n)}
    (row : InvolutionRow n a)
    (ha : ¬ IsTwoCentralIn (MulAut.innerSubgroup (LinearGroup n)) a) :
    padicValNat 2 (Nat.card (pResidual 2 a.fixedSubgroup)) = 2 ∨
    padicValNat 2 (Nat.card (pResidual 2 a.fixedSubgroup)) = 3 ∨
    padicValNat 2 (Nat.card (pResidual 2 a.fixedSubgroup)) = 8 := by
  cases row with
  | root _ _ _ hc _ => exact (ha hc).elim
  | j2 _ _ _ _ hr =>
    rcases j2_valuation hr with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  | graph _ hr =>
    obtain ⟨e⟩ := hr
    refine Or.inr (Or.inl ?_)
    rw [Nat.card_congr e.toEquiv, a6_card]
    exact twoValuation_pow_mul 3 45 (by decide)
  | exceptional _ _ hr =>
    obtain ⟨e⟩ := hr
    refine Or.inl ?_
    rw [Nat.card_congr e.toEquiv, a4_card]
    exact twoValuation_pow_mul 2 3 (by decide)

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

/-- Separation in a full higher-linear component model. All graph and
exceptional rows remain present, and the modified residual is used literally. -/
theorem separation_of_model (rows : InvolutionTable) {n : ℕ}
    (hn : n = 4 ∨ n = 5) (e : L ≃* LinearGroup n)
    (u v : normalizer (L : Set G))
    (hu2 : orderOf (actionMap le_rfl u) = 2)
    (hv2 : orderOf (actionMap le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃*
      modifiedCentralizerResidual L v.val) := by
  let a := fullModelAction e (actionMap le_rfl u)
  let b := fullModelAction e (actionMap le_rfl v)
  have ha2 : orderOf a = 2 :=
    (orderOf_injective (fullModelAction e) (fullModelAction_injective e) _).trans hu2
  have hb2 : orderOf b = 2 :=
    (orderOf_injective (fullModelAction e) (fullModelAction_injective e) _).trans hv2
  have ha := (rows n hn a ha2).central_valuation
    ((fullModelAction_twoCentral_iff e _).mpr hu)
  have hb := (rows n hn b hb2).noncentral_valuation
    (fun h => hv ((fullModelAction_twoCentral_iff e _).mp h))
  rintro ⟨d⟩
  have he := fixedResidual_twoValuation_eq e u v d
  change padicValNat 2 (Nat.card (pResidual 2 a.fixedSubgroup)) =
    padicValNat 2 (Nat.card (pResidual 2 b.fixedSubgroup)) at he
  omega

/-- The source center-quotient formulation. The exact 16.1.2 covering clause
is the displayed trivial-center input; it is not silently discarded. -/
theorem separation (rows : InvolutionTable)
    (hZ : center L = ⊥) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) n 2)
    (u v : normalizer (L : Set G))
    (hu2 : orderOf (actionMap le_rfl u) = 2)
    (hv2 : orderOf (actionMap le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃*
      modifiedCentralizerResidual L v.val) := by
  let e : L ≃* LinearGroup n :=
    (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans
      (LiePreliminaries.higherLinearEquiv (by omega) hmodel)
  exact separation_of_model rows hn e u v hu2 hv2 hu hv

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.LieRows.HigherLinear
