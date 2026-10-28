module

public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.StrictFixedBound
public import Theory.ElementaryAbelian.Basic

/-!
# Elementary subgroups interchanging the definite planes

An elementary abelian subgroup containing an interchange has order at most four:
the centralizer of a swapping involution has order twelve. That involution fixes
four vectors, and any second independent involution cuts the common fixed space
to at most two vectors. Thus its fixed-vector/order product is less than sixteen.
The counts use the 72 explicit quadratic isometries and kernel-checked finite
certificates. This supplies the pair-stabilizing alternative in the first
paragraph of Aschbacher--Smith 15.3.67, printed p.1153.
-/

@[expose] public section

open Subgroup Theory.AlgebraicGroup
namespace OrthogonalFourBinary.SylowGeometry
open TerminalLines
set_option synthInstance.maxSize 10000

set_option maxRecDepth 10000 in
private theorem finite_swap_fixed : ∀ k : Code, k.2.2 = true →
    (∀ v : Space, eval k (eval k v) = v) →
    Fintype.card {v : Space // eval k v = v} = 4 := by decide +kernel

set_option maxRecDepth 10000 in
private theorem finite_swap_centralizer : ∀ k : Code, k.2.2 = true →
    (∀ v : Space, eval k (eval k v) = v) →
    Fintype.card {j : Code // ∀ v : Space, eval k (eval j v) = eval j (eval k v)} = 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem finite_swap_extra_fixed : ∀ k j : Code, k.2.2 = true →
    (∀ v : Space, eval k (eval k v) = v) →
    (∀ v : Space, eval j (eval j v) = v) →
    (∀ v : Space, eval k (eval j v) = eval j (eval k v)) →
    (∃ v : Space, eval j v ≠ v) → (∃ v : Space, eval j v ≠ eval k v) →
    Fintype.card {v : Space // eval k v = v ∧ eval j v = v} ≤ 2 := by
  decide +kernel

private theorem code_square (k : Code) (h : codeMap k ^ 2 = 1) :
    ∀ v : Space, eval k (eval k v) = v := by
  intro v
  have hh := congrArg (fun a : Actor => a.val v) h
  change candidate k (candidate k v) = v at hh
  simpa only [candidate_eval] using hh

private theorem code_centralizer (k j : Code) :
    codeMap j ∈ centralizer ({codeMap k} : Set Actor) ↔
      ∀ v : Space, eval k (eval j v) = eval j (eval k v) := by
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h v
    have hh := congrArg (fun a : Actor => a.val v) h.symm
    change candidate k (candidate j v) = candidate j (candidate k v) at hh
    simpa only [candidate_eval] using hh
  · intro h
    symm
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change candidate k (candidate j v) = candidate j (candidate k v)
    simpa only [candidate_eval] using h v

private theorem swap_centralizer_card (k : Code) (hk : k.2.2 = true)
    (h2 : codeMap k ^ 2 = 1) :
    Nat.card (centralizer ({codeMap k} : Set Actor)) = 12 := by
  let e : {j : Code // ∀ v : Space, eval k (eval j v) = eval j (eval k v)} ≃
      centralizer ({codeMap k} : Set Actor) :=
    codeEquiv.subtypeEquiv (fun j => (code_centralizer k j).symm)
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  exact finite_swap_centralizer k hk (code_square k h2)

private theorem code_elementary_strict_fixed_bound
    (B : Subgroup Actor) [IsElementaryAbelian 2 B]
    (k : Code) (hkB : codeMap k ∈ B) (hk : k.2.2 = true) :
    Nat.card (FixedVectors B) * Nat.card B < 16 := by
  classical
  have hk2 : codeMap k ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hkB
  have hle : B ≤ centralizer ({codeMap k} : Set Actor) := by
    intro t ht
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := B)).comm
      (⟨t, ht⟩ : B) (⟨codeMap k, hkB⟩ : B))
  have hdiv : Nat.card B ∣ 12 := by
    rw [← swap_centralizer_card k hk hk2]
    exact card_dvd_of_le hle
  have hBcard : Nat.card B ≤ 4 := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_card_eq
    have hn2 : n ≤ 2 := by
      by_contra! hh
      have h8 : 8 ∣ 12 := by
        rw [hn] at hdiv
        exact (Nat.pow_dvd_pow 2 hh).trans hdiv
      norm_num at h8
    rw [hn]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hn2
  have hf4 : Nat.card {v : Space // eval k v = v} = 4 := by
    rw [Nat.card_eq_fintype_card]
    exact finite_swap_fixed k hk (code_square k hk2)
  have hfix4 : Nat.card (FixedVectors B) ≤ 4 := by
    rw [← hf4]
    refine Nat.card_le_card_of_injective
      (fun v : FixedVectors B => (⟨v.val, ?_⟩ : {v : Space // eval k v = v}))
      (fun a b h => Subtype.ext (congrArg
        (fun v : {v : Space // eval k v = v} => v.val) h))
    exact (candidate_eval k v.val).symm.trans (v.property (codeMap k) hkB)
  by_cases hsmall : Nat.card B ≤ 2
  · exact lt_of_le_of_lt (Nat.mul_le_mul hfix4 hsmall) (by decide : 4 * 2 < 16)
  have hex : ∃ t : B, (t : Actor) ≠ 1 ∧ (t : Actor) ≠ codeMap k := by
    by_contra! hh
    have hinj : Function.Injective (fun t : B => decide ((t : Actor) = 1)) := by
      intro a b he
      apply Subtype.ext
      by_cases ha : (a : Actor) = 1
      · have hb : (b : Actor) = 1 := by simpa only [ha, decide_true, true_eq_decide_iff] using he
        exact ha.trans hb.symm
      · have hb : (b : Actor) ≠ 1 := by
          intro hb
          simp only [ha, hb, decide_false, decide_true, Bool.false_eq_true] at he
        exact (hh a ha).trans (hh b hb).symm
    have hc := Nat.card_le_card_of_injective _ hinj
    have hbool : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card]; decide
    rw [hbool] at hc
    exact hsmall hc
  obtain ⟨t, ht1, htk⟩ := hex
  obtain ⟨j, hj⟩ := codeMap_bijective.surjective (t : Actor)
  have hjB : codeMap j ∈ B := hj ▸ t.property
  have hj2 : codeMap j ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hjB
  have hcommon : Nat.card {v : Space // eval k v = v ∧ eval j v = v} ≤ 2 := by
    rw [Nat.card_eq_fintype_card]
    apply finite_swap_extra_fixed k j hk (code_square k hk2) (code_square j hj2)
      ((code_centralizer k j).mp (hle hjB))
    · by_contra! he
      apply ht1
      rw [← hj]
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      exact (candidate_eval j v).trans (he v)
    · by_contra! he
      apply htk
      rw [← hj]
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      exact (candidate_eval j v).trans ((he v).trans (candidate_eval k v).symm)
  have hfix2 : Nat.card (FixedVectors B) ≤ 2 := by
    apply le_trans _ hcommon
    refine Nat.card_le_card_of_injective
      (fun v : FixedVectors B => (⟨v.val, ?_, ?_⟩ :
        {v : Space // eval k v = v ∧ eval j v = v}))
      (fun a b h => Subtype.ext (congrArg
        (fun v : {v : Space // eval k v = v ∧ eval j v = v} => v.val) h))
    · exact (candidate_eval k v.val).symm.trans (v.property (codeMap k) hkB)
    · exact (candidate_eval j v.val).symm.trans (v.property (codeMap j) hjB)
  exact lt_of_le_of_lt (Nat.mul_le_mul hfix2 hBcard) (by decide : 2 * 4 < 16)

/-- An elementary subgroup containing an interchange of the two definite planes
has fixed-vector/order product strictly less than the order of the module. -/
theorem swapping_elementary_strict_fixed_bound
    (B : Subgroup Actor) [IsElementaryAbelian 2 B] (s : Actor) (hs : s ∈ B)
    (hswap : (codeEquiv.symm s).2.2 = true) :
    Nat.card (FixedVectors B) * Nat.card B < 16 := by
  apply code_elementary_strict_fixed_bound B (codeEquiv.symm s) _ hswap
  change codeEquiv (codeEquiv.symm s) ∈ B
  simpa only [Equiv.apply_symm_apply] using hs

end OrthogonalFourBinary.SylowGeometry
