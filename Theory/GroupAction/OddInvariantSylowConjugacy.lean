module

public import Theory.GroupAction.OddInvariantSylow

/-!
# Fixed conjugators for invariant Sylow subgroups

A prime-power actor on a finite group of coprime order has a fixed element
in every nonempty invariant transporter: that transporter is a coset of
a stabilizer, hence has order prime to the actor prime. Applying this to
Sylow conjugacy, and then invariant Sylow extension, puts every invariant
p-subgroup into any chosen invariant Sylow by a fixed conjugator.

This supplies the equivariant Sylow step in GLS, Volume 4, Chapter 2,
Proposition 16.5, without a solvability assumption.
-/

open Subgroup MulAction
open scoped Pointwise

namespace Theory.GroupAction

/-- A nonempty transporter between fixed points has a fixed element. -/
public theorem exists_fixed_transporter_of_prime_not_dvd_card {A K X : Type*} [Group A] [Group K] [Finite K]
    [MulDistribMulAction A K] [MulAction A X] [MulAction K X]
    {p : ℕ} [Fact p.Prime] (hA : IsPGroup p A) (hK : ¬ p ∣ Nat.card K)
    (compat : ∀ (a : A) (k : K) (x : X), a • (k • x) = (a • k) • (a • x))
    (x y : X) (hx : ∀ a : A, a • x = x) (hy : ∀ a : A, a • y = y)
    (hxy : ∃ k : K, k • x = y) :
    ∃ k : K, (∀ a : A, a • k = k) ∧ k • x = y := by
  obtain ⟨g, hg⟩ := hxy
  let T := {k : K // k • x = y}
  let e : stabilizer K x ≃ T := {
    toFun c := ⟨g * c, by rw [mul_smul, c.property, hg]⟩
    invFun k := ⟨g⁻¹ * k, by
      change (g⁻¹ * (k : K)) • x = x
      rw [mul_smul, k.property, ← hg, inv_smul_smul]⟩
    left_inv c := Subtype.ext (by simp)
    right_inv k := Subtype.ext (by simp) }
  let _ : MulAction A T := {
    smul a k := ⟨a • (k : K), by
      calc
        (a • (k : K)) • x = a • ((k : K) • x) := by simpa only [hx a] using (compat a k x).symm
        _ = y := by rw [k.property, hy]⟩
    one_smul k := Subtype.ext (one_smul A (k : K))
    mul_smul a b k := Subtype.ext (mul_smul a b (k : K)) }
  have hT : ¬ p ∣ Nat.card T := by
    rw [← Nat.card_congr e]
    exact fun h => hK (h.trans (stabilizer K x).card_subgroup_dvd_card)
  obtain ⟨k, hk⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card T hT
  exact ⟨k, fun a => congrArg Subtype.val (hk a), k.property⟩

private theorem sylow_smul_compat
    {A K : Type*} [Group A] [Group K] [MulDistribMulAction A K]
    {q : ℕ} (a : A) (k : K) (P : Sylow q K) :
    a • (k • P) = (a • k) • (a • P) := by
  apply Sylow.ext
  change ((P : Subgroup K).map (MulAut.conj k).toMonoidHom).map
      (MulDistribMulAction.toMulAut A K a).toMonoidHom =
    ((P : Subgroup K).map (MulDistribMulAction.toMulAut A K a).toMonoidHom).map
      (MulAut.conj (a • k)).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, smul_mul', smul_inv']

private theorem sylow_fixed_of_invariant
    {A K : Type*} [Group A] [Group K] [MulDistribMulAction A K]
    {q : ℕ} (P : Sylow q K) (hP : IsInvariant A K (P : Subgroup K)) (a : A) :
    a • P = P := by
  apply Sylow.ext
  change (P : Subgroup K).map (MulDistribMulAction.toMulAut A K a).toMonoidHom = P
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hP.invariant a y).mp hy
  · intro hx
    refine ⟨a⁻¹ • x, (hP.invariant a⁻¹ x).mp hx, ?_⟩
    exact smul_inv_smul a x

/-- Invariant Sylow subgroups have a conjugator fixed by a coprime
prime-power actor. No solvability hypothesis is needed. -/
public theorem exists_fixed_conjugator_invariant_sylow
    {A K : Type*} [Group A] [Group K] [Finite K]
    [MulDistribMulAction A K] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hA : IsPGroup p A) (hK : ¬ p ∣ Nat.card K)
    (P Q : Sylow q K) (hP : IsInvariant A K (P : Subgroup K))
    (hQ : IsInvariant A K (Q : Subgroup K)) :
    ∃ k : K, (∀ a : A, a • k = k) ∧
      (P : Subgroup K).map (MulAut.conj k).toMonoidHom = Q := by
  obtain ⟨k, hk, he⟩ := exists_fixed_transporter_of_prime_not_dvd_card hA hK
    sylow_smul_compat P Q (sylow_fixed_of_invariant P hP)
    (sylow_fixed_of_invariant Q hQ) (exists_smul_eq K P Q)
  exact ⟨k, hk, congrArg Sylow.toSubgroup he⟩

/-- Every invariant p-subgroup of an odd-order group is conjugate into any
chosen invariant Sylow subgroup by an element fixed by the two-group actor. -/
public theorem exists_fixed_conjugator_le_invariant_sylow
    {A K : Type*} [Group A] [Group K] [Finite K]
    [MulDistribMulAction A K] (hA : IsPGroup 2 A) (hK : Odd (Nat.card K))
    {p : ℕ} [Fact p.Prime] (R : Subgroup K) (hR : IsPGroup p R)
    (hRI : IsInvariant A K R) (P : Sylow p K)
    (hPI : IsInvariant A K (P : Subgroup K)) :
    ∃ k : K, (∀ a : A, a • k = k) ∧
      R.map (MulAut.conj k).toMonoidHom ≤ P := by
  obtain ⟨Q, hRQ, hQI⟩ := exists_invariant_sylow_le_of_isPGroup hA hK R hR hRI
  obtain ⟨k, hk, he⟩ := exists_fixed_conjugator_invariant_sylow hA
    hK.not_two_dvd_nat Q P hQI hPI
  exact ⟨k, hk, he ▸ Subgroup.map_mono hRQ⟩

/-- Choose one invariant Sylow which receives every invariant p-subgroup
by conjugation with a fixed element. -/
public theorem exists_invariant_sylow_fixed_control
    {A K : Type*} [Group A] [Group K] [Finite K]
    [MulDistribMulAction A K] (hA : IsPGroup 2 A) (hK : Odd (Nat.card K))
    (p : ℕ) [Fact p.Prime] :
    ∃ P : Sylow p K, IsInvariant A K (P : Subgroup K) ∧
      ∀ R : Subgroup K, IsPGroup p R → IsInvariant A K R →
        ∃ k : K, (∀ a : A, a • k = k) ∧ R.map (MulAut.conj k).toMonoidHom ≤ P := by
  have hb : IsPGroup p (⊥ : Subgroup K) := IsPGroup.of_card (n := 0) (by simp)
  have hbi : IsInvariant A K (⊥ : Subgroup K) := ⟨fun a k => by
    change k = 1 ↔ a • k = 1
    constructor
    · rintro rfl
      exact smul_one a
    · intro h
      have he := congrArg (fun x : K => a⁻¹ • x) h
      simpa only [inv_smul_smul, smul_one] using he⟩
  obtain ⟨P, _, hP⟩ := exists_invariant_sylow_le_of_isPGroup hA hK ⊥ hb hbi
  exact ⟨P, hP, fun R hR hRI =>
    exists_fixed_conjugator_le_invariant_sylow hA hK R hR hRI P hP⟩

/-- Conjugation by a fixed element gives an actual injective equivariant
homomorphism into the chosen invariant Sylow subgroup. -/
public theorem exists_equivariant_embedding_invariant_sylow
    {A K : Type*} [Group A] [Group K] [Finite K]
    [MulDistribMulAction A K] (hA : IsPGroup 2 A) (hK : Odd (Nat.card K))
    {p : ℕ} [Fact p.Prime] (R : Subgroup K) (hR : IsPGroup p R)
    [IsInvariant A K R] (P : Sylow p K) [IsInvariant A K (P : Subgroup K)] :
    ∃ k : K, (∀ a : A, a • k = k) ∧
      ∃ f : R →* (P : Subgroup K), Function.Injective f ∧
        (∀ x : R, (f x : K) = k * x * k⁻¹) ∧
        ∀ (a : A) (x : R), f (a • x) = a • f x := by
  obtain ⟨k, hk, hle⟩ := exists_fixed_conjugator_le_invariant_sylow
    hA hK R hR inferInstance P inferInstance
  let f : R →* (P : Subgroup K) :=
    ((MulAut.conj k).toMonoidHom.comp R.subtype).codRestrict P
      (fun x => hle (Subgroup.mem_map_of_mem _ x.property))
  refine ⟨k, hk, f, ?_, fun x => rfl, ?_⟩
  · intro x y he
    apply Subtype.ext
    exact (MulAut.conj k).injective (congrArg Subtype.val he)
  · intro a x
    apply Subtype.ext
    change k * (a • (x : K)) * k⁻¹ = a • (k * (x : K) * k⁻¹)
    simp only [smul_mul', smul_inv', hk]

end Theory.GroupAction
