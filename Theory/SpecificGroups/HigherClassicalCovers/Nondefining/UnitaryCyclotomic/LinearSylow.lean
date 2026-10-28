module

public import Theory.Representation.CyclotomicPrimeCyclicity
public import Theory.Representation.GeneralLinearNatural
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Cyclic Sylow subgroups in dimension four over arbitrary finite fields

The units of a cubic extension act on its direct product with the base
field, producing a cyclic subgroup of GL₄(q) of order q³−1 and index
q⁶(q⁴−1)(q²−1)(q−1). This controls primes outside q(q⁴−1). For odd primes
in q²+1, the least-degree representation theorem controls the Sylow
subgroups directly. Together these arguments handle every odd prime
outside q(q²−1), for arbitrary finite fields, not just prime fields.

This extends the finite-extension construction in `Nondefining.LinearCubic`.
The consumer is the natural SU₄(p) representation over its field of order
p². It discharges the nondefining cyclotomic branch outside p⁴−1 in
Aschbacher–Smith A.2.17, printed p.39, using I.1.2, printed p.407.
-/

open Matrix Subgroup
noncomputable section

namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryCyclotomic

private theorem exists_cubic_torus (F : Type*) [Field F] [Finite F] :
    ∃ C : Subgroup (GL (Fin 4) F), IsCyclic C ∧ Nat.card C = Nat.card F ^ 3 - 1 := by
  let p := ringChar F
  let : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  let K := FiniteField.Extension F p 3
  let b := Module.finBasisOfFinrankEq F (K × F) (show Module.finrank F (K × F) = 4 by
    rw [Module.finrank_prod, FiniteField.finrank_extension, Module.finrank_self])
  let j : Kˣ →* (K × F)ˣ := {
    toFun u := ⟨((u : K), 1), ((u⁻¹ : Kˣ), 1), by ext <;> simp, by ext <;> simp⟩
    map_one' := by apply Units.ext; rfl
    map_mul' u v := by apply Units.ext; ext <;> simp }
  let f : Kˣ →* GL (Fin 4) F :=
    (Units.map (Algebra.leftMulMatrix b).toMonoidHom).comp j
  have hf : Function.Injective f := by
    intro u v h
    apply Units.ext
    exact congrArg Prod.fst (Algebra.leftMulMatrix_injective b (congrArg Units.val h))
  let e := MonoidHom.ofInjective hf
  refine ⟨f.range, e.isCyclic.mp inferInstance, ?_⟩
  rw [← Nat.card_congr e.toEquiv, Nat.card_units, FiniteField.natCard_extension]

private theorem index_cubic {F : Type*} [Field F] [Finite F]
    (C : Subgroup (GL (Fin 4) F)) (hC : Nat.card C = Nat.card F ^ 3 - 1) :
    C.index = Nat.card F ^ 6 * (Nat.card F ^ 4 - 1) *
      (Nat.card F ^ 2 - 1) * (Nat.card F - 1) := by
  classical
  let := Fintype.ofFinite F
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hpos : 0 < Nat.card F ^ 3 - 1 :=
    Nat.sub_pos_of_lt (one_lt_pow₀ (by omega) (by decide))
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [← hC, C.card_mul_index, hC, Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ, ← Nat.card_eq_fintype_card]
  have h41 : Nat.card F ^ 4 - Nat.card F =
      Nat.card F * (Nat.card F ^ 3 - 1) := by rw [Nat.mul_sub]; ring_nf
  have h42 : Nat.card F ^ 4 - Nat.card F ^ 2 =
      Nat.card F ^ 2 * (Nat.card F ^ 2 - 1) := by rw [Nat.mul_sub]; ring_nf
  have h43 : Nat.card F ^ 4 - Nat.card F ^ 3 =
      Nat.card F ^ 3 * (Nat.card F - 1) := by rw [Nat.mul_sub]; ring_nf
  rw [h41, h42, h43]
  ring

/-- A cyclic subgroup of prime-to-r index forces cyclic Sylow r-subgroups. -/
public theorem sylow_isCyclic_of_cyclic_index {G : Type*} [Group G] [Finite G]
    {r : ℕ} [Fact r.Prime] (C : Subgroup G) [IsCyclic C]
    (hi : ¬ r ∣ C.index) (Q : Sylow r G) : IsCyclic Q := by
  let T : Sylow r C := default
  let A := (T : Subgroup C).map C.subtype
  have ha : IsPGroup r A := T.isPGroup'.map C.subtype
  have hai : ¬ r ∣ A.index := by
    rw [Subgroup.index_map_subtype]
    exact (Fact.out : r.Prime).not_dvd_mul T.not_dvd_index hi
  let U : Sylow r G := ha.toSylow hai
  let e := (T : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective
  have hc : IsCyclic U := e.isCyclic.mp inferInstance
  exact (U.equiv Q).isCyclic.mp hc

private theorem fourth_sub_one (q : ℕ) :
    q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
  calc
    q ^ 4 - 1 = (q ^ 2) ^ 2 - 1 ^ 2 := by ring_nf
    _ = (q ^ 2 - 1) * (q ^ 2 + 1) := by rw [Nat.sq_sub_sq]; ac_rfl

private theorem gl_cyclic_of_cubic_index {F : Type*} [Field F] [Finite F]
    {r : ℕ} [Fact r.Prime] (hq : ¬ r ∣ Nat.card F)
    (hfour : ¬ r ∣ Nat.card F ^ 4 - 1) (Q : Sylow r (GL (Fin 4) F)) : IsCyclic Q := by
  obtain ⟨C, hc, hC⟩ := exists_cubic_torus F
  let := hc
  apply sylow_isCyclic_of_cyclic_index C ?_ Q
  rw [index_cubic C hC]
  have hr : r.Prime := Fact.out
  have hnp : ¬ r ∣ Nat.card F ^ 6 := fun h => hq (hr.dvd_of_dvd_pow h)
  have htwo : ¬ r ∣ Nat.card F ^ 2 - 1 := by
    intro h
    apply hfour
    rw [fourth_sub_one]
    exact dvd_mul_of_dvd_left h _
  have hone : ¬ r ∣ Nat.card F - 1 := fun h =>
    hfour (h.trans (by simpa using Nat.sub_dvd_pow_sub_pow (Nat.card F) 1 4))
  exact hr.not_dvd_mul (hr.not_dvd_mul (hr.not_dvd_mul hnp hfour) htwo) hone

/-- The residue of q has order four at every odd prime dividing q²+1. -/
public theorem orderOf_eq_four_of_dvd_sq_add_one {q r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) (hd : r ∣ q ^ 2 + 1) : orderOf (q : ZMod r) = 4 := by
  have hs : (q : ZMod r) ^ 2 = -1 := by
    have h := (ZMod.natCast_eq_zero_iff (q ^ 2 + 1) r).mpr hd
    push_cast at h
    exact eq_neg_of_add_eq_zero_left h
  have hn : (q : ZMod r) ^ 2 ≠ 1 := by
    rw [hs]
    intro h
    have ht : (2 : ZMod r) = 0 := by linear_combination -h
    have hdiv := (ZMod.natCast_eq_zero_iff 2 r).mp ht
    exact hr2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) Nat.prime_two).mp hdiv)
  have hpw : (q : ZMod r) ^ 4 = 1 := by
    calc
      (q : ZMod r) ^ 4 = ((q : ZMod r) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hs]; ring
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hn) (by simpa using hpw)

private theorem gl_cyclic_of_quartic {F : Type*} [Field F] [Finite F]
    {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (hq : ¬ r ∣ Nat.card F)
    (hd : r ∣ Nat.card F ^ 2 + 1) (P : Sylow r (GL (Fin 4) F)) : IsCyclic P := by
  classical
  let := Fintype.ofFinite F
  have hrF : (r : F) ≠ 0 :=
    ((isUnit_iff_not_dvd_char F r).mpr (fun h => hq
      (by simpa only [Nat.card_eq_fintype_card] using (prime_dvd_char_iff_dvd_card r).mp h))).ne_zero
  let ρ : Representation F P (Fin 4 → F) :=
    (Representation.generalLinearNatural (F := F) 4).comp (P : Subgroup (GL (Fin 4) F)).subtype
  have hi : Function.Injective ρ :=
    (Representation.generalLinearNatural_injective (F := F) 4).comp
      (P : Subgroup (GL (Fin 4) F)).subtype_injective
  refine Representation.CyclotomicPrimeCyclicity.isCyclic_of_minimal_degree
    P.isPGroup' hrF (by simpa only [← Nat.card_eq_fintype_card] using hq) ρ hi ?_
  simpa only [Module.finrank_fin_fun, ← Nat.card_eq_fintype_card, orderOf_eq_four_of_dvd_sq_add_one hr2 hd]
    using (le_refl 4)

/-- Over any finite field, primes outside q(q²−1) have cyclic Sylow subgroups
in GL₄(q). The field cardinality need not be prime. -/
public theorem gl_sylow_isCyclic_of_not_dvd_sq_sub_one
    {F : Type*} [Field F] [Finite F] {r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) (hq : ¬ r ∣ Nat.card F) (htwo : ¬ r ∣ Nat.card F ^ 2 - 1)
    (P : Sylow r (GL (Fin 4) F)) : IsCyclic P := by
  by_cases hplus : r ∣ Nat.card F ^ 2 + 1
  · exact gl_cyclic_of_quartic hr2 hq hplus P
  apply gl_cyclic_of_cubic_index hq ?_ P
  rw [fourth_sub_one]
  exact (Fact.out : r.Prime).not_dvd_mul htwo hplus

/-- The same exclusion holds for every r-subgroup of a subgroup of GL₄(q),
by embedding in an ambient Sylow subgroup. -/
public theorem subgroup_isCyclic_of_not_dvd_sq_sub_one
    {F : Type*} [Field F] [Finite F] {r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) (hq : ¬ r ∣ Nat.card F) (htwo : ¬ r ∣ Nat.card F ^ 2 - 1)
    (H : Subgroup (GL (Fin 4) F)) (P : Subgroup H) (hP : IsPGroup r P) :
    IsCyclic P := by
  obtain ⟨Q, hQ⟩ := (hP.map H.subtype).exists_le_sylow
  let := gl_sylow_isCyclic_of_not_dvd_sq_sub_one hr2 hq htwo Q
  let f : P →* Q := (H.subtype.comp P.subtype).codRestrict _
    (fun a => hQ ⟨a, a.property, rfl⟩)
  apply isCyclic_of_injective f
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun q : Q => (q : GL (Fin 4) F)) h

end Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryCyclotomic
