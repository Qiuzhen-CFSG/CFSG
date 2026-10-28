module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Relations
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Detection
public import Theory.PGroupCore
import Mathlib.Tactic.FinCases

/-!
# Structure of the fixed J₃ order-1152 candidate

The checked power and conjugation relations collect every element into a
mixed-radix normal form. A separating letter proves that the 1152 forms are
distinct. The first six stages give an order-64 subgroup, normalized by every
generator of the candidate. Each later normal form fails to commute with a
generator of this subgroup, so its intrinsic centralizer lies inside it.
The normal two-subgroup then lies in the intrinsic two-core, which is also
self-centralizing.

Source: GLS, Number 3, Table 5.3h, printed p.269, the local of shape
`2^(2+4).(S₃ × C₃)`. These are finite-subgroup facts about the actual
word-defined candidate; no ambient normalizer identification is assumed.
The application is Aschbacher–Smith, Theorem 0.1.2(5), printed p.4.
-/

namespace Sporadic.Janko3.TwoLocal.ThompsonCertificate
open Subgroup

public theorem chain_eq : chainSubgroup 9 = thompsonNormalizerCandidate := by
  apply le_antisymm
  · exact (NormalForm.series_le_iff gen 9 _).mpr (fun i _ => gen_mem i)
  · apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · change thompsonNormalizerGenerator 0 ∈ chainSubgroup 9
      rw [← g1_eq]
      exact NormalForm.gen_mem gen (i := 1) (by decide)
    · change thompsonNormalizerGenerator 1 ∈ chainSubgroup 9
      rw [← g5_eq]
      exact NormalForm.gen_mem gen (i := 5) (by decide)
    · change thompsonNormalizerGenerator 2 ∈ chainSubgroup 9
      rw [← g4_eq]
      exact NormalForm.gen_mem gen (i := 4) (by decide)
    · change thompsonNormalizerGenerator 3 ∈ chainSubgroup 9
      rw [← g3_eq]
      exact NormalForm.gen_mem gen (i := 3) (by decide)
    · change thompsonNormalizerGenerator 4 ∈ chainSubgroup 9
      rw [← g2_eq]
      exact NormalForm.gen_mem gen (i := 2) (by decide)
    · change thompsonNormalizerGenerator 5 ∈ chainSubgroup 9
      rw [← g0_eq]
      exact NormalForm.gen_mem gen (i := 0) (by decide)
    · change thompsonNormalizerGenerator 6 ∈ chainSubgroup 9
      rw [← g8_eq]
      exact NormalForm.gen_mem gen (i := 8) (by decide)
    · change thompsonNormalizerGenerator 7 ∈ chainSubgroup 9
      rw [← g6_eq]
      exact NormalForm.gen_mem gen (i := 6) (by decide)

public theorem chain_normalizes (k : ℕ) (hk : k < 9) :
    gen k ∈ normalizer (chainSubgroup k : Set Model) := by
  apply NormalForm.normalizes
  · intro i hi
    rw [conjugate_relation ⟨k, hk⟩ ⟨i, hi⟩]
    apply NormalForm.series_mono gen (show conjugateDepth k i ≤ k by
      simp only [conjugateDepth]; split <;> omega)
    exact NormalForm.rep_mem gen radix _ _
  · intro i hi
    rw [inverse_conjugate_relation ⟨k, hk⟩ ⟨i, hi⟩]
    apply NormalForm.series_mono gen (show conjugateDepth k i ≤ k by
      simp only [conjugateDepth]; split <;> omega)
    exact NormalForm.rep_mem gen radix _ _

public theorem chain_cover (n : ℕ) (hn : n ≤ 9) :
    ∀ x ∈ chainSubgroup n, ∃ r : Fin (width n), x = representative n r.val := by
  apply NormalForm.cover
  · intro i _; simp only [radix]; split <;> decide
  · intro i hi; exact chain_normalizes i (by omega)
  · intro i hi
    rw [power_relation ⟨i, by omega⟩]
    exact NormalForm.rep_mem gen radix _ _

public theorem chain_card (n : ℕ) (hn : n ≤ 9)
    (hi : Function.Injective (fun r : Fin (width n) => representative n r.val)) :
    Nat.card (chainSubgroup n) = width n := by
  let f : Fin (width n) → chainSubgroup n := fun r =>
    ⟨representative n r.val, NormalForm.rep_mem gen radix _ _⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h; exact hi (congrArg Subtype.val h)
    · intro x
      obtain ⟨r, hr⟩ := chain_cover n hn x x.property
      exact ⟨r, Subtype.ext hr.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_fin]

public theorem candidate_card : Nat.card thompsonNormalizerCandidate = 1152 := by
  rw [← chain_eq]
  exact chain_card 9 (by decide) representative_injective

public theorem core_chain_card : Nat.card (chainSubgroup 6) = 64 :=
  chain_card 6 (by decide) core_representative_injective

public theorem core_chain_le : chainSubgroup 6 ≤ thompsonNormalizerCandidate := by
  rw [← chain_eq]
  exact NormalForm.series_mono gen (by decide)

public theorem candidate_normalizes_core :
    thompsonNormalizerCandidate ≤ normalizer (chainSubgroup 6 : Set Model) := by
  rw [← chain_eq]
  apply (NormalForm.series_le_iff gen 9 _).mpr
  intro k hk
  by_cases hk6 : k < 6
  · exact (chainSubgroup 6).le_normalizer (NormalForm.gen_mem gen hk6)
  · apply NormalForm.normalizes
    · intro i hi
      have hik : i < k := by omega
      rw [conjugate_relation ⟨k, hk⟩ ⟨i, hik⟩]
      have hd : conjugateDepth k i = 6 := by simp [conjugateDepth, hi, Nat.min_eq_right (by omega : 6 ≤ k)]
      rw [hd]
      exact NormalForm.rep_mem gen radix _ _
    · intro i hi
      have hik : i < k := by omega
      rw [inverse_conjugate_relation ⟨k, hk⟩ ⟨i, hik⟩]
      have hd : conjugateDepth k i = 6 := by simp [conjugateDepth, hi, Nat.min_eq_right (by omega : 6 ≤ k)]
      rw [hd]
      exact NormalForm.rep_mem gen radix _ _

/-- The first six cyclic stages, as a subgroup of the local candidate itself. -/
@[expose] public def intrinsicCore : Subgroup thompsonNormalizerCandidate :=
  (chainSubgroup 6).subgroupOf thompsonNormalizerCandidate

public theorem intrinsicCore_normal : intrinsicCore.Normal :=
  (normal_subgroupOf_iff_le_normalizer core_chain_le).mpr candidate_normalizes_core

public theorem intrinsicCore_card : Nat.card intrinsicCore = 64 := by
  change Nat.card ((chainSubgroup 6).subgroupOf thompsonNormalizerCandidate) = 64
  rw [Nat.card_congr (subgroupOfEquivOfLe core_chain_le).toEquiv]
  exact core_chain_card

public theorem intrinsicCore_isPGroup : IsPGroup 2 intrinsicCore :=
  IsPGroup.of_card (n := 6) intrinsicCore_card

public theorem intrinsicCore_selfCentralizing :
    centralizer (intrinsicCore : Set thompsonNormalizerCandidate) ≤ intrinsicCore := by
  intro x hx
  have hxc : (x : Model) ∈ chainSubgroup 9 := chain_eq.symm ▸ x.property
  obtain ⟨r, hr⟩ := chain_cover 9 (by decide) x hxc
  have hr64 : r.val < 64 := by
    by_contra! hbad
    let j : Fin 6 := detectGenerator r
    let y : thompsonNormalizerCandidate := ⟨gen j.val, gen_mem j.val⟩
    have hy : y ∈ intrinsicCore := NormalForm.gen_mem gen j.isLt
    have heq := congrArg
      (fun z : thompsonNormalizerCandidate => (z.val.val : Equiv.Perm (Fin 6156)) (detectPoint r))
      (hx y hy)
    change ((gen j.val * (x : Model) : Model) : Equiv.Perm (Fin 6156)) (detectPoint r) =
      (((x : Model) * gen j.val : Model) : Equiv.Perm (Fin 6156)) (detectPoint r) at heq
    rw [hr] at heq
    exact outside_core_noncommuting r hbad heq.symm
  change (x : Model) ∈ chainSubgroup 6
  rw [hr, core_representative_agrees ⟨r.val, hr64⟩]
  exact NormalForm.rep_mem gen radix _ _

public theorem candidate_centralizer_pCore_le :
    centralizer (pCore 2 thompsonNormalizerCandidate : Set thompsonNormalizerCandidate) ≤
      pCore 2 thompsonNormalizerCandidate := by
  have hle : intrinsicCore ≤ pCore 2 thompsonNormalizerCandidate :=
    le_sSup ⟨intrinsicCore_normal, intrinsicCore_isPGroup⟩
  exact (centralizer_le hle).trans (intrinsicCore_selfCentralizing.trans hle)

end Sporadic.Janko3.TwoLocal.ThompsonCertificate
