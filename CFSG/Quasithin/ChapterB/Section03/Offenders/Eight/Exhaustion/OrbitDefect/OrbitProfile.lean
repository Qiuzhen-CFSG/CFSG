module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Exhaustion.CoreBound
import Theory.GroupAction.AbelianPermutationOrbitBound

/-!
# Orbit sizes in the degree-eight defect-one bound

For an abelian permutation group, evaluation at one representative from each
orbit is injective. Thus its order is at most the product of the orbit sizes.
For an elementary abelian two-group without fixed coordinates these sizes are
2, 4, or 8. If there are respectively `a`, `b`, and `c` such orbits, the degree
equation and the defect bound give `b + 4*c ≤ 1`.

Consequently the only possibilities are four pairs with group order 8 or 16,
and the pattern 4+2+2 with group order 16. In the latter case evaluation is
bijective, so the three orbit actions can be prescribed independently. This is
the quantitative reduction; identifying the actual conjugacy classes also
requires normal forms for the resulting permutation actions.

The evaluation argument follows `Theory.GroupAction.AbelianPermutationOrbitBound`.
It is repeated in this degree-specific extension because that module's
product bound is private, avoiding a change to a shared dependency.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, Proposition B.3.2(5), printed pp. 83–84.
-/

public section

open scoped BigOperators IsMulCommutative
open BinaryPermutation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.Offenders.EightExhaustion

/-- Evaluate a permutation at the chosen representative of every orbit. -/
@[expose] noncomputable def orbitEvaluation (A : Subgroup (Equiv.Perm (Fin 8))) (a : A)
    (q : MulAction.orbitRel.Quotient A (Fin 8)) : q.orbit :=
  ⟨a.val q.out, by
    rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq']
    exact ⟨a, rfl⟩⟩

/-- An abelian permutation is determined by its values on orbit representatives. -/
theorem orbitEvaluation_injective (A : Subgroup (Equiv.Perm (Fin 8)))
    [IsMulCommutative A] : Function.Injective (orbitEvaluation A) := by
  intro a b h
  apply Subtype.ext
  apply Equiv.ext
  intro x
  let q : MulAction.orbitRel.Quotient A (Fin 8) := Quotient.mk'' x
  have hx : x ∈ MulAction.orbit A q.out :=
    MulAction.orbitRel_apply.mp (Quotient.exact (Quotient.out_eq q).symm)
  obtain ⟨c, hc⟩ := hx
  change c.val q.out = x at hc
  have hab : a.val q.out = b.val q.out := congrArg Subtype.val (congrFun h q)
  rw [← hc]
  calc
    a.val (c.val q.out) = c.val (a.val q.out) :=
      congrArg (fun d : A => d.val q.out) (mul_comm a c)
    _ = c.val (b.val q.out) := congrArg c.val hab
    _ = b.val (c.val q.out) :=
      congrArg (fun d : A => d.val q.out) (mul_comm c b)

noncomputable local instance (A : Subgroup (Equiv.Perm (Fin 8))) :
    Fintype (MulAction.orbitRel.Quotient A (Fin 8)) := Fintype.ofFinite _

/-- Faithful evaluation bounds the order by the product of orbit sizes. -/
theorem card_le_prod_orbit_sizes (A : Subgroup (Equiv.Perm (Fin 8)))
    [IsMulCommutative A] :
    Nat.card A ≤ ∏ q : MulAction.orbitRel.Quotient A (Fin 8), Nat.card q.orbit := by
  simpa only [Nat.card_pi] using
    (Nat.card_le_card_of_injective (orbitEvaluation A) (orbitEvaluation_injective A))

private theorem orbit_size_options (A : Subgroup (Equiv.Perm (Fin 8)))
    (hA : IsElementaryTwo A) (hmove : ∀ x : Fin 8, ∃ a ∈ A, a x ≠ x)
    (x : Fin 8) :
    Nat.card (MulAction.orbit A x) = 2 ∨ Nat.card (MulAction.orbit A x) = 4 ∨
      Nat.card (MulAction.orbit A x) = 8 := by
  classical
  let _ : IsElementaryAbelian 2 A := hA.2
  obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 2 A).card_orbit x
  have hle : Nat.card (MulAction.orbit A x) ≤ 8 := by
    simpa using Nat.card_le_card_of_injective
      (Subtype.val : MulAction.orbit A x → Fin 8) Subtype.val_injective
  have hk3 : k ≤ 3 := by
    apply (Nat.pow_le_pow_iff_right (a := 2) (by decide)).mp
    rw [← hk]
    exact hle
  have hk0 : k ≠ 0 := by
    intro he
    have hc : Fintype.card (MulAction.orbit A x) = 1 := by
      simpa [he, Nat.card_eq_fintype_card] using hk
    obtain ⟨a, ha, hax⟩ := hmove x
    exact hax (MulAction.mem_fixedPoints.mp
      (MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mpr hc) (⟨a, ha⟩ : A))
  interval_cases k <;> simp_all

private theorem profile_arithmetic {Q : Type*} [Fintype Q]
    (s : Q → ℕ) (hs : ∀ q, s q = 2 ∨ s q = 4 ∨ s q = 8)
    (hsum : ∑ q, s q = 8) (r : ℕ)
    (hprod : 2 ^ r ≤ ∏ q, s q) (hdef : 8 ≤ r + Fintype.card Q + 1) :
    ((∀ q, s q = 2) ∧ (r = 3 ∨ r = 4)) ∨
      ((∀ q, s q = 2 ∨ s q = 4) ∧ Fintype.card Q = 3 ∧
        r = 4 ∧ ∏ q, s q = 16) := by
  classical
  let n₂ := (Finset.univ.filter fun q => s q = 2).card
  let n₄ := (Finset.univ.filter fun q => s q = 4).card
  let n₈ := (Finset.univ.filter fun q => s q = 8).card
  have hsum' : ∑ q, s q = 2 * n₂ + 4 * n₄ + 8 * n₈ := by
    calc
      ∑ q, s q = ∑ q, ((if s q = 2 then 2 else 0) +
          (if s q = 4 then 4 else 0) + (if s q = 8 then 8 else 0)) := by
        apply Finset.sum_congr rfl
        intro q _
        rcases hs q with h | h | h <;> simp [h]
      _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_ite, n₂, n₄, n₈, Nat.mul_comm]
  have hcard : Fintype.card Q = n₂ + n₄ + n₈ := by
    calc
      Fintype.card Q = ∑ q : Q, (1 : ℕ) := by simp
      _ = ∑ q, ((if s q = 2 then 1 else 0) +
          (if s q = 4 then 1 else 0) + (if s q = 8 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro q _
        rcases hs q with h | h | h <;> simp [h]
      _ = _ := by simp [Finset.sum_add_distrib, n₂, n₄, n₈]
  have hprod' : ∏ q, s q = 2 ^ (n₂ + 2 * n₄ + 3 * n₈) := by
    calc
      ∏ q, s q = ∏ q, 2 ^ ((if s q = 2 then 1 else 0) +
          (if s q = 4 then 2 else 0) + (if s q = 8 then 3 else 0)) := by
        apply Finset.prod_congr rfl
        intro q _
        rcases hs q with h | h | h <;> simp [h]
      _ = _ := by
        rw [Finset.prod_pow_eq_pow_sum]
        simp [Finset.sum_add_distrib, Finset.sum_ite, n₂, n₄, n₈, Nat.mul_comm]
  have hr : r ≤ n₂ + 2 * n₄ + 3 * n₈ := by
    apply (Nat.pow_le_pow_iff_right (a := 2) (by decide)).mp
    rwa [hprod'] at hprod
  have hn₈ : n₈ = 0 := by omega
  have hn₄ : n₄ ≤ 1 := by omega
  have hno8 (q : Q) : s q ≠ 8 := by
    intro h
    have : q ∈ Finset.univ.filter (fun q => s q = 8) := by simp [h]
    have : 0 < n₈ := Finset.card_pos.mpr ⟨q, this⟩
    omega
  rcases Nat.eq_zero_or_pos n₄ with hzero | hpos
  · left
    refine ⟨?_, by omega⟩
    intro q
    have hno4 : s q ≠ 4 := by
      intro h
      have : q ∈ Finset.univ.filter (fun q => s q = 4) := by simp [h]
      have : 0 < n₄ := Finset.card_pos.mpr ⟨q, this⟩
      omega
    exact (hs q).resolve_right (fun h => h.elim hno4 (hno8 q))
  · right
    refine ⟨fun q => (hs q).elim Or.inl (fun h => Or.inr (h.resolve_right (hno8 q))),
      by omega, by omega, ?_⟩
    rw [hprod', show n₂ + 2 * n₄ + 3 * n₈ = 4 by omega]
    norm_num

/-- Defect at most one leaves only four pair orbits, or the orbit pattern 4+2+2.
The alternatives include the forced group orders and, in the second case,
independent evaluation on the three orbits. -/
theorem orbit_profile_of_defect_le_one
    (A : Subgroup (Equiv.Perm (Fin 8))) (hA : IsElementaryTwo A)
    (hmove : ∀ x : Fin 8, ∃ a ∈ A, a x ≠ x)
    (hdef : fixedCodim (representation (Fin 8)) A ≤ rank A + 1) :
    ((∀ x : Fin 8, Nat.card (MulAction.orbit A x) = 2) ∧
      (Nat.card A = 8 ∨ Nat.card A = 16)) ∨
    ((∀ x : Fin 8, Nat.card (MulAction.orbit A x) = 2 ∨
        Nat.card (MulAction.orbit A x) = 4) ∧
      Nat.card (MulAction.orbitRel.Quotient A (Fin 8)) = 3 ∧ Nat.card A = 16 ∧
        Function.Bijective (orbitEvaluation A)) := by
  classical
  let _ : IsElementaryAbelian 2 A := hA.2
  have hs (q : MulAction.orbitRel.Quotient A (Fin 8)) :
      Nat.card q.orbit = 2 ∨ Nat.card q.orbit = 4 ∨ Nat.card q.orbit = 8 := by
    rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq']
    exact orbit_size_options A hA hmove q.out
  have hsum : (∑ q : MulAction.orbitRel.Quotient A (Fin 8), Nat.card q.orbit) = 8 := by
    simpa only [Nat.card_sigma, Nat.card_fin] using
      (Nat.card_congr (MulAction.selfEquivSigmaOrbits' A (Fin 8))).symm
  have hb := fixedCodim_full_add_card_orbits A
  simp only [Fintype.card_fin, Nat.card_eq_fintype_card] at hb
  have hp := card_le_prod_orbit_sizes A
  rw [hA.card_eq_two_pow_rank] at hp
  rcases profile_arithmetic (fun q : MulAction.orbitRel.Quotient A (Fin 8) => Nat.card q.orbit)
    hs hsum (rank A) hp (by omega) with h | h
  · left
    refine ⟨?_, ?_⟩
    · intro x
      simpa only [MulAction.orbitRel.Quotient.orbit_mk] using h.1 (Quotient.mk'' x)
    · rw [hA.card_eq_two_pow_rank]
      rcases h.2 with he | he <;> simp [he]
  · right
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x
      simpa only [MulAction.orbitRel.Quotient.orbit_mk] using h.1 (Quotient.mk'' x)
    · simpa only [Nat.card_eq_fintype_card] using h.2.1
    · rw [hA.card_eq_two_pow_rank, h.2.2.1]
      norm_num
    · apply (Nat.bijective_iff_injective_and_card _).mpr
      refine ⟨orbitEvaluation_injective A, ?_⟩
      rw [Nat.card_pi, h.2.2.2, hA.card_eq_two_pow_rank, h.2.2.1]
      norm_num

end CFSG.Quasithin.ChapterB.Offenders.EightExhaustion
