module

public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.Lemmas
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum

/-!
# A nontrivial order-three action on an elementary eight

An order-three group acting nontrivially on an elementary abelian two-group
of order eight has a fixed subgroup of order two and a displacement subgroup
of order four. The theorem retains the supplied action and expresses
nontriviality by its actual displacement subgroup being nontrivial; no
faithfulness hypothesis or chosen generator is needed.

The fixed-point congruence modulo three and the fixed subgroup's order
dividing eight leave orders two and eight. The latter would make every
commutator trivial, so it is excluded. Coprime splitting expresses the
module as the product of its fixed and displacement subgroups; their
cardinalities then give displacement order four.

This elementary action count is used in Stellmacher (10.1), printed p.60
of `refs/files/stellmacher-n-group.pdf`, in the small local-quotient branch.
Its consumer supplies the actual middle-residual image acting on U/Zmiddle.
The result itself is independent of the graph and local group hypotheses.
-/

open scoped IsMulCommutative

public theorem card_three_action_on_eight_fixed_commutator_card
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction A V]
    (hA : Nat.card A = 3) (hV : Nat.card V = 8)
    (hnontrivial : commutatorAction A V ≠ ⊥) :
    Nat.card (FixedPoints.subgroup A V) = 2 ∧
      Nat.card (commutatorAction A V) = 4 := by
  let C := FixedPoints.subgroup A V
  have hp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hmod := hp.card_modEq_card_fixedPoints V
  change Nat.card V % 3 = Nat.card C % 3 at hmod
  rw [hV] at hmod
  have hdiv : Nat.card C ∣ 2 ^ 3 := by
    simpa [hV] using C.card_subgroup_dvd_card
  obtain ⟨dimension, hdimension, hcard⟩ :=
    (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hdiv
  have hproper : C ≠ ⊤ := by
    intro htop
    apply hnontrivial
    apply bot_unique
    rw [commutatorAction_eq_closure, Subgroup.closure_le]
    rintro point ⟨actor,source,rfl⟩
    have hsource : source ∈ C := htop ▸ Subgroup.mem_top source
    have hfixed : actor • source = source := hsource actor
    rw [hfixed,inv_mul_cancel]
    exact (⊥ : Subgroup V).one_mem
  have hsmall : dimension < 3 := by
    by_contra hnot
    have heq : dimension = 3 := by omega
    apply hproper
    apply C.eq_top_of_card_eq
    rw [hcard,heq,hV]
    norm_num
  have hC : Nat.card C = 2 := by
    rw [hcard] at hmod ⊢
    interval_cases dimension <;> norm_num at *
  have hcop : Nat.Coprime (Nat.card A) (Nat.card V) := by rw [hA,hV]; decide
  have hcompl := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := V) (A := A) (Group.isSolvable_of_comm fun v w => mul_comm v w) hcop inferInstance
  let _ : C.Normal := Subgroup.normal_of_isMulCommutative C
  have hprod := Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint C (commutatorAction A V)
    (by rw [Subgroup.normalizer_eq_top]; exact le_top) hcompl.disjoint
  rw [hcompl.sup_eq_top,Subgroup.card_top,hV,hC] at hprod
  exact ⟨hC,by omega⟩
