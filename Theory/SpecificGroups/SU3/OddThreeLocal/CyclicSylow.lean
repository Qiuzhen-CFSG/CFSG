module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Mathlib.GroupTheory.Sylow

/-!
# Cyclic Sylow three-subgroups of PSU₃(q) for q ≡ 1 modulo three

The standard unitary torus is cyclic of order q² - 1. Its index is
q³(q³ + 1), which is prime to three. A Sylow subgroup of the torus is
therefore Sylow in the whole projective group. Basis change transports
this calculation to any nondegenerate Hermitian form while retaining its
field involution. The prime-field corollary derives the fixed-field order
from the specified Frobenius conjugation.

Source: Huppert, Endliche Gruppen I, II.10.12; Aschbacher–Smith, combined
1 March 2004 manuscript, proof of Proposition 1.3.4, printed p.511 (PDF p.528).
-/

public section
noncomputable section

open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.OddPrimeSylow.NormalizedOuter

namespace BenderSuzuki.MatrixGroups.HermitianForm.OddThreeLocal

private theorem cyclic_sylow_of_cyclic_subgroup_index
    {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    [IsCyclic H] (hi : ¬ 3 ∣ H.index) (S : Sylow 3 G) : IsCyclic S := by
  let P : Sylow 3 H := Classical.choice inferInstance
  let R : Subgroup G := (P : Subgroup H).map H.subtype
  have hR : IsPGroup 3 R := P.isPGroup'.map H.subtype
  have hindex : ¬ 3 ∣ R.index := by
    rw [show R.index = (P : Subgroup H).index * H.index from index_map_subtype _]
    exact Nat.prime_three.not_dvd_mul P.not_dvd_index hi
  let T : Sylow 3 G := hR.toSylow hindex
  let eP : P ≃* R := (P : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective
  exact isCyclic_of_injective ((S.equiv T).trans eP.symm).toMonoidHom
    ((S.equiv T).trans eP.symm).injective

/-- The actual standard matrix group has a cyclic subgroup of index prime to three. -/
theorem exists_cyclic_subgroup_three_coprime_index
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    (q : ℕ) (hq : 1 < q) (hmod : q % 3 = 1)
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ∃ H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      IsCyclic H ∧ ¬ 3 ∣ H.index := by
  obtain ⟨_, _, _, _, _, _, ht, _, hG, _⟩ := huppert_II_10_12 J q hcard hfixed hJ
  obtain ⟨R, H, _, _, _, _, _, hc, _, _, _, hH, _⟩ := ht
  have hgcd : Nat.gcd (q + 1) 3 = 1 := by
    rw [Nat.gcd_comm, Nat.gcd_rec, show (q + 1) % 3 = 2 by omega]
    decide
  rw [hgcd, Nat.div_one] at hH
  rw [Nat.gcd_comm, hgcd, Nat.div_one] at hG
  have hi : H.index = (q ^ 3 + 1) * q ^ 3 := by
    have hh := H.card_mul_index
    rw [hH, hG, mul_comm ((q ^ 3 + 1) * q ^ 3)] at hh
    exact Nat.eq_of_mul_eq_mul_left (Nat.sub_pos_of_lt (by nlinarith)) hh
  refine ⟨H, hc, ?_⟩
  rw [hi, Nat.dvd_iff_mod_eq_zero]
  simp [Nat.mul_mod, Nat.add_mod, Nat.pow_mod, hmod]

/-- Sylow three-subgroups are cyclic for every Gram matrix when q ≡ 1 modulo three. -/
theorem cyclic_three_sylow_of_mod_one
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    (q : ℕ) (hq : 1 < q) (hmod : q % 3 = 1)
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (S : Sylow 3 (ProjectiveSpecialUnitaryMatrixGroup J)) : IsCyclic S := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J q hcard hfixed
  obtain ⟨H, hc, hi⟩ := exists_cyclic_subgroup_three_coprime_index
    (FormTransport.standardForm J) q hq hmod hcard hfixed rfl
  let _ := hc
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hc' := cyclic_sylow_of_cyclic_subgroup_index H hi S'
  change IsCyclic ((S : Subgroup _).map e.toMonoidHom) at hc'
  let _ := hc'
  let eS := (S : Subgroup _).equivMapOfInjective e.toMonoidHom e.injective
  exact isCyclic_of_injective eS.toMonoidHom eS.injective

/-- Prime fixed-field order, with conjugation specified as x ↦ x^p. -/
theorem cyclic_three_sylow_of_prime_mod_one
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    (p : ℕ) (hp : p.Prime) (hmod : p % 3 = 1)
    (hcard : Nat.card E = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    (S : Sylow 3 (ProjectiveSpecialUnitaryMatrixGroup J)) : IsCyclic S := by
  let : Fact p.Prime := ⟨hp⟩
  have hfixed : Nat.card {x : E // J.conj x = x} = p := by
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        (by simpa only [pow_one] using hcard) (by simpa only [pow_one] using hconj)
  exact cyclic_three_sylow_of_mod_one J p hp.one_lt hmod hcard hfixed S

end BenderSuzuki.MatrixGroups.HermitianForm.OddThreeLocal
