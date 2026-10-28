module

public import CFSG.Quasithin.ChapterG.Section09.Basic
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Models
public import Theory.Representation.NonsplitFour
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
import Mathlib.Tactic

/-!
# The degree-two branch of G.9.4

Faithfulness embeds the group in GL₂(2), of order six. A positive-rank
elementary actor forces even order. Irreducibility makes the two-core
trivial, excluding order two, so the embedding is onto. The actual full
linear action is retained, and the checked SL₂(2) permutation model gives
the asserted isomorphism with S₃. Divisibility of the actor's order gives
rank one.

Source: Aschbacher--Smith, G.9.4(1), printed pp.354--355.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition

universe u v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {A : Subgroup G} {m : ℕ}

private theorem matrix_card :
    Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) = 6 := by
  rw [Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ]

/-- In the plane branch, both the actor rank and the whole group order
are forced; no Fitting or SQTK classification is needed. -/
theorem plane_rank_and_card (h : Setup ρ A m) [Representation.IsIrreducible ρ]
    (hm : 0 < m) (hd : Module.finrank (ZMod 2) V = 2) :
    m = 1 ∧ Nat.card G = 6 := by
  have hG : Nat.card G ∣ 6 := by
    have hdiv := Representation.card_dvd_card_GL_of_injective ρ h.faithful
    rwa [hd, matrix_card] at hdiv
  have hA : 2 ^ m ∣ Nat.card G := h.card_actor ▸ A.card_subgroup_dvd_card
  have htwo : 2 ∣ Nat.card G := (dvd_pow_self 2 (Nat.ne_of_gt hm)).trans hA
  have hmone : m = 1 := by
    have hn : ¬ 2 ≤ m := by
      intro hle
      have hfour : 4 ∣ 6 := (pow_dvd_pow 2 hle).trans (hA.trans hG)
      norm_num at hfour
    omega
  have hne : Nat.card G ≠ 2 := by
    intro hc
    have hp : IsPGroup 2 G := IsPGroup.of_card (n := 1) hc
    have htop : (⊤ : Subgroup G) ≤ pCore 2 G :=
      le_sSup ⟨inferInstance, hp.to_subgroup ⊤⟩
    rw [h.twoCore_eq_bot] at htop
    have hh := congrArg (fun H : Subgroup G => Nat.card H) (bot_unique htop)
    simp only [Subgroup.card_top, Subgroup.card_bot, hc] at hh
    omega
  have hle := Nat.le_of_dvd (by decide : 0 < 6) hG
  have hpos := Nat.card_pos (α := G)
  refine ⟨hmone, ?_⟩
  interval_cases hc : Nat.card G <;> norm_num at *

/-- The original faithful plane action fills the full linear group. The
isomorphism retains each operator, rather than identifying groups by order. -/
theorem plane_full_linear_action (h : Setup ρ A m) [Representation.IsIrreducible ρ]
    (hm : 0 < m) (hd : Module.finrank (ZMod 2) V = 2) :
    ∃ e : G ≃* (V ≃ₗ[ZMod 2] V), ∀ g v, e g v = ρ g v := by
  let b := Module.finBasisOfFinrankEq (ZMod 2) V hd
  let t := Matrix.GeneralLinearGroup.toLin' b
  let : Finite (LinearMap.GeneralLinearGroup (ZMod 2) V) :=
    Finite.of_equiv _ t.toEquiv
  have hc : Nat.card (LinearMap.GeneralLinearGroup (ZMod 2) V) = 6 :=
    (Nat.card_congr t.symm.toEquiv).trans matrix_card
  have hi : Function.Injective ρ.toHomUnits := by
    intro g k he
    exact h.faithful (congrArg Units.val he)
  have hb : Function.Bijective ρ.toHomUnits := by
    rw [Nat.bijective_iff_injective_and_card]
    exact ⟨hi, (plane_rank_and_card h hm hd).2.trans hc.symm⟩
  exact ⟨(MulEquiv.ofBijective ρ.toHomUnits hb).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V), fun _ _ => rfl⟩

/-- G.9.4(1), whenever the actual module has degree two. -/
theorem caseOne_of_degree_two {K : GroupClass.{u}}
    (h : FittingHypothesis K ρ A m) (hm : 0 < m)
    (hd : Module.finrank (ZMod 2) V = 2) : CaseOne ρ m := by
  let : Representation.IsIrreducible ρ := h.irreducible
  obtain ⟨e, _⟩ := plane_full_linear_action h.toSetup hm hd
  let b := Module.finBasisOfFinrankEq (ZMod 2) V hd
  let t := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm.trans
    (Matrix.GeneralLinearGroup.toLin' b).symm
  let s := (BinaryLinear.OuterCyclic.matrixEquivLinear 2).trans
    ((BinaryLinear.OuterCyclic.slEquivLinear 2).symm.trans
      (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three))
  exact ⟨(plane_rank_and_card h.toSetup hm hd).1, hd, ⟨e.trans (t.trans s)⟩⟩

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition
