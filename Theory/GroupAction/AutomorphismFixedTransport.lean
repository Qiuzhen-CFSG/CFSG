module

public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.GroupTheory.Sylow

/-!
# Fixed subgroups under group isomorphisms

Transport an automorphism by an actual multiplicative equivalence. Its fixed
subgroup is isomorphic to the original fixed subgroup, innerness is preserved,
and the existence of a normal Sylow subgroup is invariant under the resulting
isomorphism. Multiplying by an inner automorphism also preserves innerness.

For an automorphism whose square is one, orbit counting by its cyclic subgroup
shows that the fixed subgroup and ambient finite group have the same parity.
Cauchy's theorem then supplies a fixed involution when the ambient order is even.

These elementary results support the model calculations in GLS, Volume 4,
Chapter 4, Lemma 3.4, used in Chapter 2, Proposition 4.4. They make no
classification assumption about arbitrary automorphisms of a matrix group.
-/


namespace MulAut
variable {G H : Type*} [Group G] [Group H]

/-- The equivalence restricts to an equivalence of the actual fixed subgroups. -/
public def fixedSubgroupCongr (e : G ≃* H) (a : MulAut G) :
    a.fixedSubgroup ≃* (MulAut.congr e a).fixedSubgroup where
  toFun x := ⟨e x, by
    rw [mem_fixedSubgroup]
    change e (a (e.symm (e x))) = e x
    rw [e.symm_apply_apply, (mem_fixedSubgroup a x).mp x.property]⟩
  invFun y := ⟨e.symm y, by
    rw [mem_fixedSubgroup]
    apply e.injective
    have hy := (mem_fixedSubgroup (MulAut.congr e a) y).mp y.property
    change e (a (e.symm y)) = y at hy
    simpa using hy⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (e.map_mul x y)

/-- Transport carries conjugation by an element to conjugation by its image. -/
public theorem congr_conj (e : G ≃* H) (g : G) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext y
  simp [MulAut.congr, MulAut.conj_apply]

/-- Innerness is invariant under transport to an isomorphic group. -/
public theorem congr_inner_iff (e : G ≃* H) (a : MulAut G) :
    (∃ h : H, MulAut.congr e a = MulAut.conj h) ↔
      ∃ g : G, a = MulAut.conj g := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨e.symm h, (MulAut.congr e).injective ?_⟩
    rw [hh, congr_conj, e.apply_symm_apply]
  · rintro ⟨g, rfl⟩
    exact ⟨e g, congr_conj e g⟩

/-- An automorphism of order dividing two preserves the parity of the fixed subgroup. -/
public theorem fixedSubgroup_card_mod_two [Finite G] (a : MulAut G) (ha : a ^ 2 = 1) :
    Nat.card a.fixedSubgroup % 2 = Nat.card G % 2 := by
  let A := Subgroup.zpowers a
  have hp : IsPGroup 2 A := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [A, Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one ha)
  have heq : FixedPoints.subgroup A G = a.fixedSubgroup := by
    ext x
    constructor
    · intro hx
      rw [mem_fixedSubgroup]
      exact ((FixedPoints.mem_subgroup (M := A) (α := G) (a := x)).mp hx) ⟨a, Subgroup.mem_zpowers a⟩
    · intro hx
      rw [FixedPoints.mem_subgroup]
      have hle : A ≤ MulAction.stabilizer (MulAut G) x :=
        Subgroup.zpowers_le.mpr ((mem_fixedSubgroup a x).mp hx)
      intro b
      exact hle b.property
  have hmod := hp.card_modEq_card_fixedPoints G
  change Nat.card G % 2 = Nat.card (FixedPoints.subgroup A G) % 2 at hmod
  rw [heq] at hmod
  exact hmod.symm

/-- The fixed subgroup has even order when the ambient finite group does. -/
public theorem even_card_fixedSubgroup [Finite G] (a : MulAut G) (ha : a ^ 2 = 1)
    (heven : Even (Nat.card G)) : Even (Nat.card a.fixedSubgroup) := by
  rw [Nat.even_iff, fixedSubgroup_card_mod_two a ha]
  exact Nat.even_iff.mp heven

/-- An automorphism squaring to one on a finite even-order group fixes an involution. -/
public theorem exists_fixed_orderOf_eq_two [Finite G] (a : MulAut G) (ha : a ^ 2 = 1)
    (heven : Even (Nat.card G)) : ∃ x : G, a x = x ∧ orderOf x = 2 := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := a.fixedSubgroup) 2
    (even_iff_two_dvd.mp (even_card_fixedSubgroup a ha heven))
  exact ⟨x, (mem_fixedSubgroup a x).mp x.property,
    (Subgroup.orderOf_coe x).trans hx⟩

/-- The fixed subgroup of an inner automorphism is the element centralizer. -/
public theorem fixedSubgroup_conj (g : G) :
    (MulAut.conj g).fixedSubgroup = Subgroup.centralizer ({g} : Set G) := by
  ext x
  rw [mem_fixedSubgroup, Subgroup.mem_centralizer_singleton_iff]
  change g * x * g⁻¹ = x ↔ x * g = g * x
  rw [mul_inv_eq_iff_eq_mul, eq_comm]

/-- Composing with conjugation does not change whether an automorphism is inner. -/
public theorem mul_conj_inner_iff (a : MulAut G) (g : G) :
    (∃ b : G, a * MulAut.conj g = MulAut.conj b) ↔
      ∃ b : G, a = MulAut.conj b := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b * g⁻¹, ?_⟩
    rw [map_mul, map_inv]
    exact (eq_mul_inv_iff_mul_eq).mpr hb
  · rintro ⟨b, rfl⟩
    exact ⟨b * g, (map_mul MulAut.conj b g).symm⟩

end MulAut

namespace MulEquiv
variable {G H : Type*} [Group G] [Group H]

/-- An actual group isomorphism preserves existence of a normal Sylow subgroup. -/
public theorem exists_normal_sylow_iff [Finite G] [Finite H]
    (e : G ≃* H) (p : ℕ) [Fact p.Prime] :
    (∃ P : Sylow p G, (P : Subgroup G).Normal) ↔
      ∃ Q : Sylow p H, (Q : Subgroup H).Normal := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨P.mapSurjective e.surjective, hP.map e.toMonoidHom e.surjective⟩
  · rintro ⟨Q, hQ⟩
    exact ⟨Q.mapSurjective e.symm.surjective, hQ.map e.symm.toMonoidHom e.symm.surjective⟩
end MulEquiv
