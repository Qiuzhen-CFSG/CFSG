module
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.GroupAction.TwoGroupFixedImage
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Fixed subgroups modulo an odd characteristic subgroup

For an automorphism whose square is one, the fixed subgroup maps onto the
fixed subgroup of the induced quotient automorphism. The kernel is retained
as the given odd characteristic subgroup. The proof uses the cyclic two-group
of automorphisms and the odd-fiber fixed-point theorem.

This is the standard coprime centralizer covering argument; see GLS,
Volume 4, Chapter 2, the proof of Proposition 4.4 for its local application.
-/

namespace MulAut
variable {G : Type*} [Group G] [Finite G]

/-- Fixed points lift through the actual odd characteristic quotient. -/
public theorem map_fixedSubgroup_characteristic_odd
    (O : Subgroup G) [O.Characteristic] (hodd : Odd (Nat.card O))
    (a : MulAut G) (ha : a ^ 2 = 1) :
    a.fixedSubgroup.map (QuotientGroup.mk' O) = (O.quotientAut a).fixedSubgroup := by
  let A := Subgroup.zpowers a
  let q := QuotientGroup.mk' O
  let rho := O.quotientAut.comp A.subtype
  let : MulDistribMulAction A (G ⧸ O) := MulDistribMulAction.compHom _ rho
  have hp : IsPGroup 2 A := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [A, Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one ha)
  have heqG : FixedPoints.subgroup A G = a.fixedSubgroup := by
    ext x
    constructor
    · intro hx
      rw [mem_fixedSubgroup]
      exact hx ⟨a, Subgroup.mem_zpowers a⟩
    · intro hx
      have hle : A ≤ MulAction.stabilizer (MulAut G) x :=
        Subgroup.zpowers_le.mpr ((mem_fixedSubgroup a x).mp hx)
      intro b
      exact hle b.property
  have heqQ : FixedPoints.subgroup A (G ⧸ O) = (O.quotientAut a).fixedSubgroup := by
    ext x
    constructor
    · intro hx
      rw [mem_fixedSubgroup]
      exact hx ⟨a, Subgroup.mem_zpowers a⟩
    · intro hx
      have hle : A ≤ (MulAction.stabilizer (MulAut (G ⧸ O)) x).comap O.quotientAut :=
        Subgroup.zpowers_le.mpr ((mem_fixedSubgroup _ x).mp hx)
      intro b
      exact hle b.property
  have hker : Odd (Nat.card q.ker) := by
    simpa only [q, QuotientGroup.ker_mk'] using hodd
  have hh := q.map_fixedPoints_eq_of_odd_kernel hp hker (fun b x =>
    (O.quotientAut_apply_mk (b : MulAut G) x).symm)
  rwa [heqG, heqQ, q.range_eq_top_of_surjective (QuotientGroup.mk'_surjective O), top_inf_eq] at hh

end MulAut
