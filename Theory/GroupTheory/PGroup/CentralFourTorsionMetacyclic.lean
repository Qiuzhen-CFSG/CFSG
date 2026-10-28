module

public import Theory.GroupTheory.PGroup.CentralFourTorsionAbelianBase
public import Theory.GroupTheory.PGroup.CentralFourTorsionPowerful
public import Theory.GroupTheory.PGroup.PowerfulTwoGeneratorMetacyclic

/-!
# Metacyclic witnesses and abelian bases for central four-torsion

A finite abelian two-group with exactly four square roots of one is a product
of two cyclic groups. Projection onto one factor supplies a cyclic normal
subgroup with cyclic quotient.

For a possibly nonabelian finite two-group whose fourth roots of one are
central, choose a maximal normal abelian subgroup containing the center.
It is self-centralizing and contains every involution. The same root count
therefore identifies it with a product of two nontrivial cyclic two-groups.
Conjugation fixes its fourth roots of one.

These results close the abelian case and provide the abelian base for the
remaining nonabelian structural argument. They do not assert that every such
group is metacyclic. The intended application is MacWilliams, *On 2-groups
with no normal abelian subgroups of rank 3*, Trans. AMS 150 (1970), printed
p.377, assertion (xvii), citing Alperin, *Centralizers of abelian normal
subgroups of p-groups*, J. Algebra 1 (1964), pp.110–113.
-/

open Subgroup
open scoped IsMulCommutative

/-- A product of two cyclic groups has an explicit cyclic normal subgroup
with cyclic quotient, transported along an isomorphism. -/
public theorem exists_cyclic_normal_cyclic_quotient_of_equiv_prod
    {Q A B : Type*} [Group Q] [Group A] [Group B]
    [IsCyclic A] [IsCyclic B] (e : Q ≃* A × B) :
    ∃ (N : Subgroup Q) (_ : N.Normal), IsCyclic N ∧ IsCyclic (Q ⧸ N) := by
  let f : Q →* B := (MonoidHom.snd A B).comp e.toMonoidHom
  let g : f.ker →* A := ((MonoidHom.fst A B).comp e.toMonoidHom).comp f.ker.subtype
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    apply e.injective
    apply Prod.ext h
    exact (show (e (x : Q)).2 = 1 from x.property).trans
      (show (e (y : Q)).2 = 1 from y.property).symm
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨q, hq⟩ := e.surjective (1, b)
    exact ⟨q, congrArg Prod.snd hq⟩
  let : IsCyclic f.ker := isCyclic_of_injective g hg
  let eqv := QuotientGroup.quotientKerEquivOfSurjective f hf
  exact ⟨f.ker, inferInstance, inferInstance,
    isCyclic_of_injective eqv.toMonoidHom eqv.injective⟩

namespace IsPGroup

/-- The abelian case of the metacyclic conclusion from four square roots of one. -/
public theorem exists_cyclic_normal_cyclic_quotient_of_four_square_roots_of_abelian
    {Q : Type*} [Group Q] [Finite Q] [IsMulCommutative Q]
    (hQ : IsPGroup 2 Q) (hcount : Nat.card {x : Q // x ^ 2 = 1} = 4) :
    ∃ (N : Subgroup Q) (_ : N.Normal), IsCyclic N ∧ IsCyclic (Q ⧸ N) := by
  let : CommGroup Q := IsMulCommutative.instCommGroup
  have hO : Nat.card (omega₁ Q (p := 2)) = 4 := by
    rw [← square_ker_eq_omega_one]
    exact hcount
  obtain ⟨n, m, _, _, ⟨e⟩⟩ :=
    hQ.equiv_two_cyclic_factors_of_card_omega_one_eq_four hO
  exact exists_cyclic_normal_cyclic_quotient_of_equiv_prod e

/-- Central fourth roots and exactly four square roots force metacyclicity.

The power-and-generator reduction is supplied by
`powerful_and_two_generated_of_central_fourth_roots`; the final metacyclic
witness is the powerful two-generator theorem.
-/
public theorem exists_cyclic_normal_cyclic_quotient_of_central_fourth_roots
    {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q)
    (hfour : ∀ x : Q, x ^ 4 = 1 → x ∈ Subgroup.center Q)
    (hcount : Nat.card {x : Q // x ^ 2 = 1} = 4) :
    ∃ (N : Subgroup Q) (_ : N.Normal), IsCyclic N ∧ IsCyclic (Q ⧸ N) := by
  obtain ⟨hpower, a, b, hgen⟩ :=
    hQ.powerful_and_two_generated_of_central_fourth_roots hfour hcount
  exact hQ.exists_cyclic_normal_cyclic_quotient_of_le_fourthPowers
    hpower a b hgen

end IsPGroup
