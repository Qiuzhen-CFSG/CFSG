module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.NormalizerAction
public import Theory.GroupTheory.Fitting.Centralizer

/-!
# The moved-prime restriction in 13.5.20

For an involution subgroup A moving a normal odd p-subgroup P, an element
of P fails to commute with A. The resulting product of two conjugate
involutions is a nonidentity element of P in their generated pair.
The pair cannot be a two-group. If the non-two pairs have order six, as
F.9.5(6.i) implies in the source application, then p divides six and p=3.
The prime-core join formula then reduces failure of Fitting centralization
to a moved three-core. These are group-theoretic deductions from the pair
input, not a proof of the independent F.9.5 implication or its applicability.

Source: Aschbacher–Smith, combined manuscript, first sentence of 13.5.20,
printed p.923 (PDF p.940), using F.9.5(6.i), printed p.319.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting
/-- The prime restriction only needs the S₃ conclusion for the actual
conjugate pairs. A moved normal p-subgroup supplies a nonidentity odd-order
product of the two involutions inside one of those pairs. -/
theorem prime_eq_three_of_moved_normal
    {X : Type*} [Group X] [Finite X] (A P : Subgroup X) [P.Normal]
    (hA : Nat.card A = 2) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hP : IsPGroup p P) (hm : ⁅P, A⁆ ≠ ⊥)
    (hpairs : ∀ x : X,
      ¬ IsPGroup 2 (A ⊔ A.map (MulAut.conj x).toMonoidHom : Subgroup X) →
        Nat.card (A ⊔ A.map (MulAut.conj x).toMonoidHom : Subgroup X) = 6) : p = 3 := by
  have hex : ∃ x ∈ P, ∃ a ∈ A, x * a ≠ a * x := by
    by_contra! he
    apply hm
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro x hx a ha
    exact (he x hx a ha).symm
  obtain ⟨x, hx, a, ha, hxa⟩ := hex
  have ha2 : a ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨a, ha⟩ : A))
    rw [hA] at hh
    exact congrArg Subtype.val hh
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha2)
  let r := a * (x * a * x⁻¹)
  have hrP : r ∈ P := by
    have hh := P.mul_mem ((inferInstance : P.Normal).conj_mem x hx a) (P.inv_mem hx)
    simpa only [r, hai, mul_assoc] using hh
  have hrne : r ≠ 1 := by
    intro he
    have hh := congrArg (fun z : X => a⁻¹ * z * x) he
    change a⁻¹ * (a * (x * a * x⁻¹)) * x = a⁻¹ * 1 * x at hh
    simp only [inv_mul_cancel_left, inv_mul_cancel_right, mul_one] at hh
    exact hxa (by simpa only [hai] using hh)
  have hd : p ∣ orderOf r := by
    have hh := hP.dvd_orderOf
      (show (⟨r, hrP⟩ : P) ≠ 1 from fun h => hrne (congrArg Subtype.val h))
    exact (Subgroup.orderOf_coe (⟨r, hrP⟩ : P)) ▸ hh
  let I := A ⊔ A.map (MulAut.conj x).toMonoidHom
  have hrI : r ∈ I := I.mul_mem (mem_sup_left ha)
    (mem_sup_right (mem_map.mpr ⟨a, ha, rfl⟩))
  have hI : ¬ IsPGroup 2 I := by
    intro hI
    exact hrne (disjoint_def.mp (IsPGroup.disjoint_of_ne p 2 hp2 P I hP hI) hrP hrI)
  have hc : Nat.card I = 6 := hpairs x hI
  have hd6 : p ∣ 6 := hc ▸ hd.trans (I.orderOf_dvd_natCard hrI)
  have hor : p ∣ 2 ∨ p ∣ 3 := (Fact.out : p.Prime).dvd_mul.mp hd6
  rcases hor with h | h
  · exact (hp2 ((Nat.prime_two.eq_one_or_self_of_dvd p h).resolve_left
      (Fact.out : p.Prime).ne_one)).elim
  · exact (Nat.prime_three.eq_one_or_self_of_dvd p h).resolve_left
      (Fact.out : p.Prime).ne_one


/-- If Fitting centralization fails, the moved prime core is the three-core.
This uses the prime-core join formula for F(X), not a chosen Fitting factor. -/
theorem threeCore_moved_of_fitting_not_centralized
    {X : Type*} [Group X] [Finite X] (A : Subgroup X)
    (hA : Nat.card A = 2) (hcore : pCore 2 X = ⊥)
    (hpairs : ∀ x : X,
      ¬ IsPGroup 2 (A ⊔ A.map (MulAut.conj x).toMonoidHom : Subgroup X) →
        Nat.card (A ⊔ A.map (MulAut.conj x).toMonoidHom : Subgroup X) = 6)
    (hfit : ¬ A ≤ centralizer (fittingSubgroup X : Set X)) :
    ⁅pCore 3 X, A⁆ ≠ ⊥ := by
  have hex : ∃ q : (Nat.card X).primeFactors.attach,
      ¬ A ≤ centralizer (pCore q.1.1 X : Set X) := by
    by_contra! hn
    exact hfit (subgroup_le_centralizer_fitting_of_le_centralizer_pCores hn)
  obtain ⟨q, hq⟩ := hex
  let p := q.1.1
  have hp : p.Prime := (Nat.mem_primeFactors.mp q.1.2).1
  let : Fact p.Prime := ⟨hp⟩
  have hm : ⁅pCore p X, A⁆ ≠ ⊥ := by
    intro he
    exact hq (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))
  have hp2 : p ≠ 2 := by
    intro he
    apply hm
    rw [he, hcore, commutator_bot_left]
  have he := prime_eq_three_of_moved_normal A (pCore p X) hA hp2 pCore_isPGroup hm hpairs
  rwa [he] at hm

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting

end
