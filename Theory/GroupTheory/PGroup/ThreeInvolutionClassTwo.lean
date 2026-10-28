module

public import Theory.GroupTheory.PGroup.ThreeInvolutionAutomorphism
public import Theory.GroupTheory.PGroup.CriticalSubgroupAutomorphisms
public import Theory.GroupTheory.PGroup.CriticalSubgroupFrattiniBound
public import Theory.GroupTheory.PGroup.SmallFrattiniAutomorphismOrderNine

/-!
# The class bound for groups with three transitive central involutions

Transitivity on three involutions supplies a fixed-point-free automorphism.
Its induced permutation is a three-cycle. If the automorphism group has no
element of order nine, the prime-order lifting lemma supplies an actual
order-three automorphism moving all involutions. Cauchy's theorem makes
this automorphism fixed-point-free, and Neumann's theorem makes the derived
subgroup central.

The order-nine obstruction can be tested on a critical subgroup, since
restriction preserves odd automorphism orders. These reductions keep the
order exclusion explicit; they do not assume that an arbitrary three-cycle
lifts with order three.

When all involutions are central, a critical subgroup has Frattini quotient
of order at most sixteen. This excludes its automorphisms of order nine and
discharges the obstruction, proving that the ambient derived subgroup is
central.

Sources: B. H. Neumann's theorem as cited in Higman, *Suzuki 2-groups*,
Illinois J. Math. 7 (1963), Lemma 6; Thompson's critical subgroup theorem
in Gorenstein, *Finite Groups*, Theorem 5.3.11, pp.185–186.
-/

namespace IsPGroup

private def involutionPermHom (P : Type*) [Group P] :
    MulAut P →* Equiv.Perm {x : P // orderOf x = 2} where
  toFun a := Equiv.Perm.subtypePerm a.toEquiv (fun x => by
    change orderOf (a x) = 2 ↔ orderOf x = 2
    rw [a.orderOf_eq])
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl

private theorem three_point_order :
    ∀ a : Equiv.Perm (Fin 3), orderOf a = 3 ↔ ∀ x, a x ≠ x := by
  have h : ∀ a : Equiv.Perm (Fin 3),
      (a ^ 3 = 1 ∧ a ≠ 1) ↔ ∀ x, a x ≠ x := by decide +kernel
  intro a
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [orderOf_eq_prime_iff]
  exact h a

/-- Excluding order nine makes the involution three-cycle lift to a
fixed-point-free automorphism of actual order three. -/
public theorem exists_order_three_fixedPointFree_of_three_transitive_involutions_of_no_order_nine
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (htrans : ∀ x y : P, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut P, a x = y)
    (hno : ∀ a : MulAut P, orderOf a ≠ 9) :
    ∃ a : MulAut P, orderOf a = 3 ∧ MonoidHom.FixedPointFree a := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let I := {x : P // orderOf x = 2}
  let : Fintype I := Fintype.ofFinite I
  let e : I ≃ Fin 3 := Fintype.equivFinOfCardEq
    (by simpa only [Nat.card_eq_fintype_card] using hthree)
  let f : MulAut P →* Equiv.Perm (Fin 3) :=
    e.permCongrHom.toMonoidHom.comp (involutionPermHom P)
  have hf (a : MulAut P) (x : I) : f a (e x) = e ⟨a x, (a.orderOf_eq x).trans x.property⟩ := by
    simp [f, involutionPermHom]
    rfl
  obtain ⟨a, ha⟩ := hP.exists_fixedPointFree_of_three_transitive_involutions hthree htrans
  have hfa : orderOf (f a) = 3 := by
    apply (three_point_order _).mpr
    intro i hi
    obtain ⟨x, rfl⟩ := e.surjective i
    rw [hf] at hi
    have heq : a x = x := congrArg Subtype.val (e.injective hi)
    have hx := ha x heq
    have ho := x.property
    rw [hx, orderOf_one] at ho
    omega
  obtain ⟨b, hb, hfb⟩ := f.exists_prime_order_lift_of_no_prime_square_order
    (by decide : Nat.Prime 3) hno a hfa
  refine ⟨b, hb, hP.fixedPointFree_of_no_fixed_prime_order b ?_⟩
  intro x hx hfix
  apply (three_point_order _).mp hfb (e ⟨x, hx⟩)
  rw [hf]
  exact congrArg e (Subtype.ext hfix)
/-- The class-two conclusion reduces to excluding order-nine automorphisms.
The order exclusion is explicit: a three-cycle need not lift with order three
for a general homomorphism. -/
public theorem commutator_le_center_of_three_transitive_involutions_of_no_order_nine
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (htrans : ∀ x y : P, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut P, a x = y)
    (hno : ∀ a : MulAut P, orderOf a ≠ 9) :
    commutator P ≤ Subgroup.center P := by
  obtain ⟨a, ha, hfree⟩ :=
    hP.exists_order_three_fixedPointFree_of_three_transitive_involutions_of_no_order_nine
      hthree htrans hno
  exact a.commutator_le_center_of_orderOf_eq_three_of_fixedPointFree ha hfree

/-- It suffices to exclude order-nine automorphisms on a critical subgroup. -/
public theorem commutator_le_center_of_three_transitive_involutions_of_critical_aut_no_order_nine
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (htrans : ∀ x y : P, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut P, a x = y)
    {C : Subgroup P} (hC : IsCriticalPSubgroup 2 C)
    (hno : ∀ a : MulAut C, orderOf a ≠ 9) :
    commutator P ≤ Subgroup.center P :=
  hP.commutator_le_center_of_three_transitive_involutions_of_no_order_nine
    hthree htrans (hC.no_order_nine_of_restriction hP hno)

/-- A finite two-group with exactly three central involutions, on which its
automorphism group acts transitively, has nilpotency class at most two. -/
public theorem commutator_le_center_of_three_transitive_involutions
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ Subgroup.center P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (htrans : ∀ x y : P, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut P, a x = y) :
    commutator P ≤ Subgroup.center P := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C, hC⟩ := hP.exists_criticalPSubgroup
  exact hP.commutator_le_center_of_three_transitive_involutions_of_critical_aut_no_order_nine
    hthree htrans hC
    ((hP.to_subgroup C).orderOf_mulAut_ne_nine_of_card_frattini_quotient_le_sixteen
      (hC.card_frattini_quotient_le_sixteen_of_three_central_involutions hP hcentral hthree))

end IsPGroup
