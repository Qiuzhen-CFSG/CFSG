module

public import Theory.AlgebraicGroup.Bor1.Differential

universe u w

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup
open scoped BigOperators

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- A derivation at the identity differentiates a finite product one factor
at a time, evaluating every undifferentiated factor at the identity. -/
public theorem identityPointDerivation_prod
    {G : Variety k} [AlgebraicGroup G] (D : IdentityPointDerivation G)
    {ι : Type w} [DecidableEq ι] (s : Finset ι)
    (q : ι → G.PolynomialFunction) :
    D (∏ i ∈ s, q i) =
      ∑ i ∈ s, (∏ j ∈ s.erase i, q j 1) * D (q i) := by
  induction s using Finset.induction_on with
  | empty => simp [D.map_one_eq_zero]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, D.leibniz, ih]
      have hsmul (f : G.PolynomialFunction) (c : k) :
          f • c = f 1 * c := rfl
      rw [hsmul, hsmul]
      have heval (t : Finset ι) :
          (∏ i ∈ t, q i) 1 = ∏ i ∈ t, q i 1 := by
        let ev := polynomialFunctionPointAlgHom G 1
        change ev (∏ i ∈ t, q i) = _
        simp only [map_prod]
        rfl
      rw [heval]
      change q a 1 *
          (∑ i ∈ s, (∏ j ∈ s.erase i, q j 1) * D (q i)) +
          (∏ i ∈ s, q i 1) * D (q a) = _
      rw [Finset.sum_insert ha]
      simp only [Finset.erase_insert, ha, not_false_eq_true]
      rw [Finset.mul_sum]
      rw [add_comm]
      apply congrArg (fun z => (∏ j ∈ s, q j 1) * D (q a) + z)
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.erase_insert_of_ne (ne_of_mem_of_not_mem hi ha).symm]
      rw [Finset.prod_insert]
      · ring
      · exact fun hai => ha (Finset.mem_of_mem_erase hai)

end Theory.AlgebraicGroup.Bor1
