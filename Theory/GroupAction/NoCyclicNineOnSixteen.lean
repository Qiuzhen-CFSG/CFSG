module
public import Theory.GroupAction.Invariant
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Tactic

/-!
# A faithful cyclic-nine group cannot act on a group of order sixteen

A finite group F of order nine acting faithfully by automorphisms on a
group V of order sixteen is not cyclic. No commutativity or elementary
structure of V is assumed, and the supplied action instance is retained.

If F were cyclic, its unique subgroup of order three would be contained
in every nontrivial cyclic subgroup. The complement of its fixed subgroup
in V would therefore have a free F action, so its size is divisible by
nine. The fixed subgroup has order dividing sixteen. Every proper divisor
contradicts the free-complement congruence, while faithfulness excludes
fixed subgroup V itself.

This source-neutral orbit argument is extracted unchanged from the
private cyclic-nine exclusion in Stellmacher.SectionOne.GLFourTwoClassification,
which imports this theorem and preserves its public classification API.
It is also used for the faithful three-group bound in Stellmacher (8.6)(20).
-/

open scoped BigOperators IsMulCommutative

private theorem zmodNine_three_mem_zpowers_of_ne_one
    (z : Multiplicative (ZMod 9)) (hz : z ≠ 1) :
    Multiplicative.ofAdd (3 : ZMod 9) ∈ Subgroup.zpowers z := by
  let a : ZMod 9 := Multiplicative.toAdd z
  change Multiplicative.ofAdd (3 : ZMod 9) ∈
    Subgroup.zpowers (Multiplicative.ofAdd a)
  rw [Subgroup.mem_zpowers_iff]
  have a_eq_cast (k : ℕ) (hk : k < 9) (ha : a.val = k) :
      a = (k : ZMod 9) := by
    apply ZMod.val_injective
    rw [ha, ZMod.val_natCast_of_lt hk]
  have haLt : a.val < 9 := a.val_lt
  interval_cases ha : a.val
  · exfalso
    apply hz
    apply Multiplicative.toAdd.injective
    change a = 0
    exact a_eq_cast 0 (by omega) rfl
  · rw [a_eq_cast 1 (by omega) rfl]
    exact ⟨3, by decide⟩
  · rw [a_eq_cast 2 (by omega) rfl]
    exact ⟨6, by decide⟩
  · rw [a_eq_cast 3 (by omega) rfl]
    exact ⟨1, by decide⟩
  · rw [a_eq_cast 4 (by omega) rfl]
    exact ⟨3, by decide⟩
  · rw [a_eq_cast 5 (by omega) rfl]
    exact ⟨6, by decide⟩
  · rw [a_eq_cast 6 (by omega) rfl]
    exact ⟨2, by decide⟩
  · rw [a_eq_cast 7 (by omega) rfl]
    exact ⟨3, by decide⟩
  · rw [a_eq_cast 8 (by omega) rfl]
    exact ⟨6, by decide⟩

public theorem not_isCyclic_of_card_nine_of_faithful_on_card_sixteen
    {F V : Type*} [Group F] [Finite F] [Group V] [Finite V]
    [MulDistribMulAction F V]
    (hcardF : Nat.card F = 9) (hcardV : Nat.card V = 16)
    (hfaith : fixingSubgroup F (Set.univ : Set V) = ⊥) :
    ¬ IsCyclic F := by
  classical
  intro hcyclic
  let : IsCyclic F := hcyclic
  let e : F ≃* Multiplicative (ZMod 9) :=
    mulEquivOfCyclicCardEq (by simpa using hcardF)
  let y : F := e.symm (Multiplicative.ofAdd (3 : ZMod 9))
  have hyne : y ≠ 1 := by
    intro hy
    have heq : Multiplicative.ofAdd (3 : ZMod 9) = 1 := by
      simpa [y] using congrArg e hy
    exact (by decide : Multiplicative.ofAdd (3 : ZMod 9) ≠ 1) heq
  let K : Subgroup F := Subgroup.zpowers y
  have hK_le_zpowers (f : F) (hf : f ≠ 1) : K ≤ Subgroup.zpowers f := by
    have hef : e f ≠ 1 := by
      intro hef
      exact hf (e.injective (by simpa using hef))
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
      (zmodNine_three_mem_zpowers_of_ne_one (e f) hef)
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨n, ?_⟩
    apply e.injective
    simpa [y] using hn
  let C : Subgroup V := FixedPoints.subgroup K V
  have hCne : C ≠ ⊤ := by
    intro hC
    have hyfix : ∀ v : V, y • v = v := by
      intro v
      have hv : v ∈ C := by rw [hC]; exact Subgroup.mem_top v
      exact (FixedPoints.mem_subgroup (M := K) (a := v)).1 hv
        ⟨y, Subgroup.mem_zpowers y⟩
    have hyker : y ∈ fixingSubgroup F (Set.univ : Set V) := by
      rw [mem_fixingSubgroup_iff]
      exact fun v _hv => hyfix v
    rw [hfaith] at hyker
    exact hyne (by simpa using hyker)
  let X := {v : V // v ∉ C}
  let : MulAction F X := {
    smul f v := ⟨f • (v : V), by
      intro hfv
      apply v.property
      rw [FixedPoints.mem_subgroup] at hfv ⊢
      intro k
      apply smul_left_cancel f
      calc
        f • ((k : F) • (v : V)) = (f * (k : F)) • (v : V) := by rw [mul_smul]
        _ = ((k : F) * f) • (v : V) := by rw [mul_comm]
        _ = (k : F) • (f • (v : V)) := by rw [mul_smul]
        _ = f • (v : V) := hfv k⟩
    one_smul v := by
      apply Subtype.ext
      exact one_smul F (v : V)
    mul_smul f g v := by
      apply Subtype.ext
      exact mul_smul f g (v : V) }
  let : IsCancelSMul F X := isCancelSMul_iff_eq_one_of_smul_eq.mpr (by
    intro f v hfv
    by_contra hf
    apply v.property
    rw [FixedPoints.mem_subgroup]
    intro k
    exact smul_eq_self_of_mem_zpowers (hK_le_zpowers f hf k.property)
      (congrArg Subtype.val hfv))
  let : Fintype F := Fintype.ofFinite F
  let : Fintype V := Fintype.ofFinite V
  let : Fintype X := Fintype.ofFinite X
  let : ∀ f : F, Fintype (MulAction.fixedBy X f) := fun _ => Fintype.ofFinite _
  have hsum :
      (∑ f : F, Nat.card (MulAction.fixedBy X f)) = Nat.card X := by
    rw [Finset.sum_eq_single 1]
    · simp [MulAction.fixedBy_one_eq_univ]
    · intro f _hfmem hf
      have hempty : MulAction.fixedBy X f = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro v hv
        exact hf (IsCancelSMul.eq_one_of_smul ((MulAction.mem_fixedBy).1 hv))
      simp [hempty]
    · simp
  have hburn0 := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group F X
  have hburn : Nat.card X =
      Nat.card (Quotient (MulAction.orbitRel F X)) * Nat.card F := by
    rw [← hsum]
    simpa [Nat.card_eq_fintype_card] using hburn0
  have hdvdX : 9 ∣ Nat.card X := by
    rw [hburn, hcardF]
    exact dvd_mul_left 9 _
  have hcardX : Nat.card X = 16 - Nat.card C := by
    rw [← hcardV]
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card]
    change Fintype.card {v : V // v ∉ C} =
      Fintype.card V - Fintype.card {v : V // v ∈ C}
    exact Fintype.card_subtype_compl (fun v : V => v ∈ C)
  have hdvdC : Nat.card C ∣ 16 := by
    rw [← hcardV]
    exact C.card_subgroup_dvd_card
  rw [hcardX] at hdvdX
  have hdvdCpow : Nat.card C ∣ 2 ^ 4 := by simpa using hdvdC
  obtain ⟨k, hk, hCpow⟩ :=
    (Nat.dvd_prime_pow (m := 4) (i := Nat.card C)
      (by decide : Nat.Prime 2)).mp hdvdCpow
  have hkCases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hkCases with rfl | rfl | rfl | rfl | rfl
  · rw [hCpow] at hdvdX
    norm_num at hdvdX
  · rw [hCpow] at hdvdX
    norm_num at hdvdX
  · rw [hCpow] at hdvdX
    norm_num at hdvdX
  · rw [hCpow] at hdvdX
    norm_num at hdvdX
  · have hcardEq : Nat.card C = Nat.card V := by
      rw [hCpow, hcardV]
      norm_num
    have : C = ⊤ := Subgroup.eq_top_of_card_eq C hcardEq
    exact hCne this
