module

public import Theory.Representation.GeneralLinearNatural
public import Theory.Representation.PGroupScalarWitness
public import Theory.Representation.SolvableDimension
public import Theory.Representation.RankThreePGroupIrreducible
public import Theory.Representation.RankThreeIrreducibleThreeAutomizer
public import Mathlib.GroupTheory.Nilpotent

/-!
# Nonabelian prime-group representations in degree three

An odd nonabelian prime-group in degree three in cross characteristic acts
absolutely irreducibly: complete reducibility and odd irreducible degrees rule
out a proper constituent. The irreducible degree divides the group order, so
the prime is three. The faithful natural action then gives an actual scalar
matrix of order three over the original field.

For solvability, the three-group has an abelian index-three subgroup with
abelian ambient centralizer. Its normalizer is solvable by the weight action,
and its orbit under the original normalizer has size at most four. The coset
action proves solvability of the original normalizer and hence its automizer.

These results supply the nonabelian representation argument for
Aschbacher–Smith, Lemma A.3.21(c), printed pp. 55–56 of `refs/quasithin.pdf`.
-/

public section

namespace Representation.RankThreeNonabelianAutomizer

variable {F : Type*} [Field F] [Finite F]

/-- An absolutely irreducible prime-group in degree three is a three-group. -/
theorem prime_eq_three_of_absolutelyIrreducible
    (Q : Subgroup (GL (Fin 3) F)) {q : ℕ} [Fact q.Prime] (hQ : IsPGroup q Q)
    [IsAbsolutelyIrreducible ((generalLinearNatural (F := F) 3).comp Q.subtype)] :
    q = 3 := by
  let : Group.IsNilpotent Q := hQ.isNilpotent
  have hdiv := lemma_2_3 ((generalLinearNatural (F := F) 3).comp Q.subtype)
  have hthree : 3 ∣ Nat.card Q := by simpa using hdiv
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  rw [hn] at hthree
  exact (((Nat.dvd_prime (Fact.out : q.Prime)).mp
    (Nat.prime_three.dvd_of_dvd_pow hthree)).resolve_left (by decide)).symm

/-- The required scalar is a matrix in the original subgroup and a unit of the
original field, with order exactly three. -/
theorem exists_scalar_order_three_of_absolutelyIrreducible
    (Q : Subgroup (GL (Fin 3) F)) {q : ℕ} [Fact q.Prime] (hQ : IsPGroup q Q)
    (hcomm : ¬ IsMulCommutative Q)
    [IsAbsolutelyIrreducible ((generalLinearNatural (F := F) 3).comp Q.subtype)] :
    ∃ a : Fˣ, orderOf a = 3 ∧ ∃ g : Q,
      ((g.val : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        Matrix.scalar (Fin 3) (a : F) := by
  let : Nontrivial Q := not_subsingleton_iff_nontrivial.mp fun h => by
    let : Subsingleton Q := h
    exact hcomm inferInstance
  have hq := prime_eq_three_of_absolutelyIrreducible Q hQ
  obtain ⟨a, ha, g, hg⟩ := exists_scalar_order_prime_of_absolutelyIrreducible
    ((generalLinearNatural (F := F) 3).comp Q.subtype)
    ((generalLinearNatural_injective 3).comp Subtype.val_injective) hQ
  refine ⟨a, ha.trans hq, g, ?_⟩
  have hmatrix := congrArg LinearMap.toMatrix' hg
  simpa [generalLinearNatural, Matrix.GeneralLinearGroup.coe_toLin,
    ← Matrix.toLin'_apply', Matrix.smul_one_eq_diagonal] using hmatrix

/-- A nonabelian odd prime-subgroup of GL₃ in cross characteristic is a
three-group. -/
theorem prime_eq_three
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [CharP F p]
    (hqodd : Odd q) (hqp : q ≠ p)
    (Q : Subgroup (GL (Fin 3) F)) (hQ : IsPGroup q Q)
    (hcomm : ¬ IsMulCommutative Q) : q = 3 := by
  let : IsAbsolutelyIrreducible ((generalLinearNatural (F := F) 3).comp Q.subtype) :=
    generalLinearNatural_three_isAbsolutelyIrreducible_of_isPGroup hqodd hqp Q hQ hcomm
  exact prime_eq_three_of_absolutelyIrreducible Q hQ

/-- The automizer of a nonabelian odd prime-subgroup of GL₃ in cross
characteristic is solvable. -/
theorem automizer_isSolvable
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [CharP F p]
    (hqodd : Odd q) (hqp : q ≠ p)
    (Q : Subgroup (GL (Fin 3) F)) (hQ : IsPGroup q Q)
    (hcomm : ¬ IsMulCommutative Q) :
    Group.IsSolvable Q.normalizerMonoidHom.range := by
  have hirr :=
    generalLinearNatural_three_isAbsolutelyIrreducible_of_isPGroup hqodd hqp Q hQ hcomm
  have hq := prime_eq_three hqodd hqp Q hQ hcomm
  exact rankThree_automizer_isSolvable_of_absolutelyIrreducible_threeGroup
    p (hq ▸ hqp) Q (hq ▸ hQ) hcomm hirr

/-- A nonabelian odd prime-subgroup of GL₃ in cross characteristic contains
a scalar matrix whose scalar has order exactly three in the original field. -/
theorem exists_scalar_order_three
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [CharP F p]
    (hqodd : Odd q) (hqp : q ≠ p)
    (Q : Subgroup (GL (Fin 3) F)) (hQ : IsPGroup q Q)
    (hcomm : ¬ IsMulCommutative Q) :
    ∃ a : Fˣ, orderOf a = 3 ∧ ∃ g : Q,
      ((g.val : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        Matrix.scalar (Fin 3) (a : F) := by
  let : IsAbsolutelyIrreducible ((generalLinearNatural (F := F) 3).comp Q.subtype) :=
    generalLinearNatural_three_isAbsolutelyIrreducible_of_isPGroup hqodd hqp Q hQ hcomm
  exact exists_scalar_order_three_of_absolutelyIrreducible Q hQ hcomm

end Representation.RankThreeNonabelianAutomizer
