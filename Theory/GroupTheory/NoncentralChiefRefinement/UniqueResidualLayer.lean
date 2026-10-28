module
public import Theory.GroupAction.NormalPChiefSeries
public import Theory.GroupTheory.NoncentralChiefRefinement.Transport
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# A unique noncentral chief factor controls the residual commutator

On a normal two-group, the two-residual acts idempotently. If every step
of a chief series is central, induction puts its commutator in the first
term. Refine through an arbitrary normal subgroup X and compare actual
chief counts by Jordan–Hölder. With exactly one noncentral factor,
either the interval below X or the interval above X has zero count.
Thus X centralizes O²(H), or X contains [U,O²(H)].

Source: Aschbacher–Smith, D.1.4, printed pp.175–176, the unique-layer
irreducibility and lifting observation (*). No split-module hypothesis.
-/

public section
open Subgroup
namespace NoncentralChiefRefinement
variable {H : Type*} [Group H] [Finite H]

theorem ChiefSeries.residual_commutator_le_head_of_central_steps
    (s : ChiefSeries H) (hp : IsPGroup 2 s.last.val)
    (hc : ∀ i : Fin s.length, IsCentral (s i.castSucc) (s i.succ)) :
    ⁅s.last.val, pResidual 2 H⁆ ≤ s.head.val := by
  have hall : ∀ i : Fin (s.length + 1), ⁅(s i).val, pResidual 2 H⁆ ≤ s.head.val := by
    intro i
    induction i using Fin.induction with
    | zero => exact commutator_le_left _ _
    | succ i ih =>
      have hs : ⁅(s i.succ).val, pResidual 2 H⁆ ≤ (s i.castSucc).val := by
        have hh := (isCentral_iff_commutator_le _ _).mp (hc i)
        rw [commutator_comm] at hh
        exact (commutator_mono le_rfl le_top).trans hh
      have hid := commutator_isPPerfect_idempotent (pResidual 2 H) (s i.succ).val
        (isPPerfect_pResidual 2) (hp.to_le (show (s i.succ).val ≤ s.last.val from CompositionSeries.le_last i.succ)) le_normalizer_of_normal
      rw [← hid]
      exact (commutator_mono hs le_rfl).trans ih
  exact hall (Fin.last s.length)

theorem ChiefSeries.residual_commutator_le_head_of_count_zero
    (s : ChiefSeries H) (hp : IsPGroup 2 s.last.val) (hz : s.noncentralTwoCount = 0) :
    ⁅s.last.val, pResidual 2 H⁆ ≤ s.head.val := by
  apply s.residual_commutator_le_head_of_central_steps hp
  intro i
  by_contra hn
  have hi : IsNoncentralTwo (s i.castSucc) (s i.succ) :=
    ⟨(hp.to_le (CompositionSeries.le_last i.succ)).to_quotient _, hn⟩
  have hempty : IsEmpty {i : Fin s.length // IsNoncentralTwo (s i.castSucc) (s i.succ)} := by
    rcases Nat.card_eq_zero.mp hz with he | he
    · exact he
    · exact ((not_finite_iff_infinite.mpr he) inferInstance).elim
  exact hempty.false ⟨i, hi⟩

theorem SeriesOn.residual_dichotomy_of_count_one
    {U : Subgroup H} [U.Normal] (s : SeriesOn U)
    (hp : IsPGroup 2 U) (hs : s.noncentralCount = 1)
    (X : Subgroup H) [X.Normal] (hXU : X ≤ U) :
    ⁅X, pResidual 2 H⁆ = ⊥ ∨ ⁅U, pResidual 2 H⁆ ≤ X := by
  let x : NormalNode H := ⟨X, inferInstanceAs X.Normal⟩
  let u : NormalNode H := ⟨U, inferInstanceAs U.Normal⟩
  obtain ⟨a, ha0, haX⟩ := exists_chiefSeries (⊥ : NormalNode H) x bot_le
  obtain ⟨b, hbX, hbU⟩ := exists_chiefSeries x u hXU
  have hab : a.last = b.head := haX.trans hbX.symm
  have hc : a.noncentralTwoCount + b.noncentralTwoCount = 1 := by
    rw [← ChiefSeries.noncentralTwoCount_smash a b hab]
    rw [ChiefSeries.noncentralTwoCount_eq (a.smash b hab) s.series
      ((RelSeries.head_smash hab).trans (ha0.trans s.head_eq.symm))
      ((RelSeries.last_smash hab).trans (hbU.trans s.last_eq.symm))]
    rw [← s.noncentralCount_eq_twoCount hp, hs]
  by_cases ha : a.noncentralTwoCount = 0
  · left
    have hpa : IsPGroup 2 a.last.val := (hp.to_le hXU).of_equiv
      (MulEquiv.subgroupCongr (congrArg Subtype.val haX)).symm
    have h := a.residual_commutator_le_head_of_count_zero hpa ha
    rw [ha0, haX] at h
    change ⁅X, pResidual 2 H⁆ ≤ ⊥ at h
    exact le_bot_iff.mp h
  · right
    have hb : b.noncentralTwoCount = 0 := by omega
    have hpb : IsPGroup 2 b.last.val := hp.of_equiv
      (MulEquiv.subgroupCongr (congrArg Subtype.val hbU)).symm
    have h := b.residual_commutator_le_head_of_count_zero hpb hb
    simpa only [hbX, hbU, x, u] using h
end NoncentralChiefRefinement

