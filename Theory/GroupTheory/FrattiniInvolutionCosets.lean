module

public import Theory.GroupTheory.FrattiniInvolutionObstruction
public import Theory.ElementaryAbelian.TenPointConfiguration

/-!
# Bounding the involutory cosets of an elementary Frattini subgroup

If D = Φ(J) = Z₂(J) is elementary abelian and J/D is elementary of order
sixteen, fewer than ten nonidentity cosets admit involutory lifts. Otherwise
the ten-point configuration supplies generators and their products with the
first generator, contradicting the Frattini involution obstruction.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
Lemma 4, printed p.675. This bound also excludes two disjoint five-element
orbits consisting of involutory cosets.
-/

open Subgroup

/-- There are fewer than ten nonidentity cosets with involutory lifts. -/
public theorem nonidentity_involutory_cosets_ncard_lt_ten
    {J : Type*} [Group J] [Finite J]
    (D : Subgroup J) [D.Normal] [IsElementaryAbelian 2 D]
    [IsElementaryAbelian 2 (J ⧸ D)]
    (hPhi : D = frattini J) (hUpper : D = Subgroup.upperCentralSeries J 2)
    (hcard : Nat.card (J ⧸ D) = 16) :
    {x : J ⧸ D | x ≠ 1 ∧ ∃ a : J, a ^ 2 = 1 ∧ QuotientGroup.mk' D a = x}.ncard < 10 := by
  classical
  let S : Set (J ⧸ D) :=
    {x | x ≠ 1 ∧ ∃ a : J, a ^ 2 = 1 ∧ QuotientGroup.mk' D a = x}
  change S.ncard < 10
  by_contra! hlarge
  obtain ⟨v, hgen, hv, hprod⟩ :=
    Theory.ElementaryAbelian.exists_generating_configuration_of_ten_le_ncard
      hcard S (fun hh => hh.1 rfl) hlarge
  obtain ⟨j, hj⟩ := exists_product_without_involutory_lift D hPhi hUpper
    v hgen (fun i => (hv i).2) 0 (hv 0).1
  by_cases hj0 : j = 0
  · subst j
    obtain ⟨a, ha, hqa⟩ := (hv 0).2
    apply hj
    refine ⟨1, one_pow 2, ?_⟩
    rw [map_one, ← hqa, ← map_mul, ← pow_two, ha, map_one]
  · exact hj (hprod j hj0).2
