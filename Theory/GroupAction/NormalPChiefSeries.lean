module
public import Theory.GroupTheory.NoncentralChiefRefinement.Actions
public import Theory.GroupAction.PGroupNoncentralChiefQuotient

/-!
# Chief series on a finite normal p-subgroup

A series on U has actual ambient-normal terms, starts at 1 and ends at U.
Finite normal-lattice refinement constructs it. Each literal relative quotient
has its conjugation action, is nontrivial and irreducible; when U is a p-group,
Frattini nongeneration shows that every quotient is elementary abelian.
Centrality means triviality of this action. The noncentral count is the
cardinality of its actual noncentral intervals, with exact zero, one and
multiple-factor criteria, rather than an externally supplied integer.

This source-neutral extension of NoncentralChiefRefinement supplies the
series used in Aschbacher--Smith, D.1.3--D.1.5, printed pp.173--177.
-/

@[expose] public section
namespace NoncentralChiefRefinement
open Subgroup
variable {H : Type*} [Group H]

/-- A chief series on a specified normal subgroup, with actual ambient-normal terms. -/
structure SeriesOn (U : Subgroup H) [U.Normal] where
  series : ChiefSeries H
  head_eq : series.head = ⊥
  last_eq : series.last = ⟨U, inferInstanceAs U.Normal⟩

namespace SeriesOn
variable {U : Subgroup H} [U.Normal]

theorem exists_series [Finite H] (U : Subgroup H) [U.Normal] : Nonempty (SeriesOn U) := by
  obtain ⟨s, hs0, hsU⟩ := exists_chiefSeries (⊥ : NormalNode H) ⟨U, inferInstanceAs U.Normal⟩ bot_le
  exact ⟨⟨s, hs0, hsU⟩⟩

variable (s : SeriesOn U)

/-- The lower endpoint of an actual chief interval. -/
def lower (i : Fin s.series.length) : NormalNode H := s.series i.castSucc
/-- The upper endpoint of an actual chief interval. -/
def upper (i : Fin s.series.length) : NormalNode H := s.series i.succ
abbrev Factor (i : Fin s.series.length) := Section (s.lower i) (s.upper i)
def action (i : Fin s.series.length) : H →* MulAut (s.Factor i) :=
  sectionAction (s.lower i) (s.upper i)
def Central (i : Fin s.series.length) : Prop := IsCentral (s.lower i) (s.upper i)
noncomputable def noncentralCount : ℕ := Nat.card {i : Fin s.series.length // ¬ s.Central i}

theorem upper_le (i : Fin s.series.length) : (s.upper i).val ≤ U := by
  have h := CompositionSeries.le_last (s := s.series) i.succ
  rw [s.last_eq] at h
  exact h

theorem factor_nontrivial (i : Fin s.series.length) : Nontrivial (s.Factor i) :=
  (s.series.isChief i).quotient_nontrivial _ _

theorem central_iff_action (i : Fin s.series.length) :
    s.Central i ↔ ∀ h x, s.action i h x = x :=
  isCentral_iff_action _ _

theorem action_mk (i : Fin s.series.length) (h : H) (x : (s.upper i).val) :
    s.action i h (QuotientGroup.mk' ((s.lower i).val.subgroupOf (s.upper i).val) x) =
      QuotientGroup.mk' ((s.lower i).val.subgroupOf (s.upper i).val)
        (MulAut.conjNormal h x) := rfl

theorem factor_irreducible (i : Fin s.series.length) (K : Subgroup (s.Factor i))
    (hK : ∀ h x, x ∈ K → s.action i h x ∈ K) : K = ⊥ ∨ K = ⊤ := by
  let A := (s.lower i).val
  let B := (s.upper i).val
  have hc : ChiefFactor.IsChief B A := s.series.isChief i
  have hnB : (⊤ : Subgroup H) ≤ normalizer (B : Set H) := by
    rw [normalizer_eq_top]
  apply quotient_conjugation_irreducible_of_maximal ⊤ B A hc.lt.le hnB inferInstance
    (fun L hAL hLB hL => ?_) ((s.action i).comp (⊤ : Subgroup H).subtype)
    (fun _ _ => rfl) K (fun h x hx => hK h x hx)
  have hnL : L.Normal := normalizer_eq_top_iff.mp (top_unique hL)
  rcases hc.minimal L hnL hAL hLB.le with he | he
  · exact he
  · exact (hLB.ne he).elim

variable [Finite H]

/-- A chief factor below a finite normal p-subgroup is elementary abelian. -/
theorem factor_elementary {p : ℕ} [Fact p.Prime] (hU : IsPGroup p U)
    (i : Fin s.series.length) : IsElementaryAbelian p (s.Factor i) := by
  let A := (s.lower i).val
  let B := (s.upper i).val
  have hc : ChiefFactor.IsChief B A := s.series.isChief i
  have hB : IsPGroup p B := hU.of_injective (inclusion (s.upper_le i)) (inclusion_injective _)
  let Φ := (frattini B).map B.subtype
  have hΦB : Φ ≤ B := map_subtype_le _
  have hNΦ : Φ.Normal := by
    exact inferInstanceAs ((frattini B).map B.subtype).Normal
  let _ := hNΦ
  have hAL : A ≤ A ⊔ Φ := le_sup_left
  have hLB : A ⊔ Φ ≤ B := sup_le hc.lt.le hΦB
  have hLA : A ⊔ Φ = A := by
    rcases hc.minimal (A ⊔ Φ) inferInstance hAL hLB with he | he
    · exact he
    · have ht : A.subgroupOf B ⊔ frattini B = ⊤ := by
        apply map_injective B.subtype_injective
        rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hc.lt.le,
          ← MonoidHom.range_eq_map, range_subtype]
        exact he
      have ha := frattini_nongenerating ht
      exact (hc.lt.not_ge (subgroupOf_eq_top.mp ha)).elim
  apply elementary_quotient_of_frattini_le hB (A.subgroupOf B)
  intro x hx
  change (x : H) ∈ A
  rw [← hLA]
  exact (show Φ ≤ A ⊔ Φ from le_sup_right) (mem_map_of_mem B.subtype hx)

omit [Finite H] in
theorem noncentralCount_eq_twoCount (hU : IsPGroup 2 U) :
    s.noncentralCount = s.series.noncentralTwoCount := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro i
  have hp : IsPGroup 2 (s.Factor i) :=
    (hU.of_injective (inclusion (s.upper_le i)) (inclusion_injective _)).to_quotient _
  exact (and_iff_right hp).symm

omit [Finite H] in
theorem noncentralCount_eq_zero_iff : s.noncentralCount = 0 ↔ ∀ i, s.Central i := by
  classical
  rw [noncentralCount, Nat.card_eq_zero]
  constructor
  · intro h i
    by_contra hi
    rcases h with h | h
    · exact h.false ⟨i, hi⟩
    · exact (not_finite_iff_infinite.mpr h) inferInstance
  · intro h
    exact Or.inl ⟨fun i => i.property (h i.val)⟩

omit [Finite H] in
/-- Exactly one actual chief interval has nontrivial conjugation action. -/
theorem noncentralCount_eq_one_iff :
    s.noncentralCount = 1 ↔ ∃! i, ¬ s.Central i := by
  rw [noncentralCount, Nat.card_eq_one_iff_exists]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i.val, i.property, ?_⟩
    intro j hj
    exact congrArg Subtype.val (hi ⟨j, hj⟩)
  · rintro ⟨i, hi, huniq⟩
    exact ⟨⟨i, hi⟩, fun j => Subtype.ext (huniq j.val j.property)⟩

omit [Finite H] in
/-- The multiple-factor branch means two distinct actual noncentral factors. -/
theorem one_lt_noncentralCount_iff :
    1 < s.noncentralCount ↔ ∃ i j, i ≠ j ∧ ¬ s.Central i ∧ ¬ s.Central j := by
  classical
  let _ := Fintype.ofFinite {i : Fin s.series.length // ¬ s.Central i}
  rw [noncentralCount, Nat.card_eq_fintype_card, Fintype.one_lt_card_iff]
  constructor
  · rintro ⟨i, j, hij⟩
    exact ⟨i.val, j.val, fun he => hij (Subtype.ext he), i.property, j.property⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    exact ⟨⟨i, hi⟩, ⟨j, hj⟩, fun he => hij (congrArg Subtype.val he)⟩

omit [Finite H] in
/-- The three source branches exhaust a chosen genuine chief series. -/
theorem noncentral_cases :
    (∀ i, s.Central i) ∨ (∃! i, ¬ s.Central i) ∨
      (∃ i j, i ≠ j ∧ ¬ s.Central i ∧ ¬ s.Central j) := by
  by_cases hz : s.noncentralCount = 0
  · exact Or.inl (s.noncentralCount_eq_zero_iff.mp hz)
  by_cases ho : s.noncentralCount = 1
  · exact Or.inr (Or.inl (s.noncentralCount_eq_one_iff.mp ho))
  · exact Or.inr (Or.inr (s.one_lt_noncentralCount_iff.mp (by omega)))

end SeriesOn
end NoncentralChiefRefinement
