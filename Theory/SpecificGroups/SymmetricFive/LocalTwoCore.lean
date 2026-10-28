module
public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor

/-!
# Two-cores of Sylow overgroups in S₅

If a subgroup of S₅ contains a Sylow two-subgroup and has order divisible
by three, its two-core lies in A₅. Conjugate the Sylow subgroup to the
dihedral group on the first four letters. For each odd element of this
Sylow subgroup and each cubic element, a checked five-point calculation
finds two conjugates whose product has nontrivial odd order. Normality
would put that product in the two-core, which is impossible.

The certificate quantifies over eight Sylow elements and the 120 five-point
permutations; it does not enumerate arbitrary subsets or subgroups of S₅.
This is the intrinsic group calculation used in Aschbacher–Smith, proof of
15.3.49 on printed p.1144, to exclude the B.4.2(5) offender row (p.86).
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.SpecificGroups.SymmetricFive.LocalTwoCore
private abbrev D := Equiv.Perm (Fin 5)
private def a : D := Equiv.swap 0 1
private def b : D := Equiv.swap 2 3
private def c : D := Equiv.swap 0 2 * Equiv.swap 1 3
private def word : Fin 8 → D := ![1, a, b, a*b, c, a*c, b*c, a*b*c]
private def eight : Subgroup D where
  carrier := Set.range word
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    have hc : ∀ i j, ∃ k, word i * word j = word k := by decide +kernel
    rintro x y ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hc i j
    exact ⟨k, hk.symm⟩
  inv_mem' := by
    have hc : ∀ i, ∃ j, (word i)⁻¹ = word j := by decide +kernel
    rintro x ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hc i
    exact ⟨j, hj.symm⟩
private theorem eight_card : Nat.card eight = 8 := by
  have hi : Function.Injective word := by decide +kernel
  change Nat.card (Set.range word) = 8
  rw [← Nat.card_congr (Equiv.ofInjective _ hi)]
  simp
private noncomputable def eightSylow : Sylow 2 D := Sylow.ofCard eight (by
  rw [eight_card, Nat.card_eq_fintype_card, Fintype.card_perm]
  norm_num [Nat.factorial]
  rw [show 120 = 2 ^ 3 * 15 by decide,
    Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 15)]
  rfl)

private theorem odd_core_witness :
    ∀ (i : Fin 8) (y : D), (word i).sign ≠ 1 → y ^ 3 = 1 → y ≠ 1 →
      ∃ j : Fin 8,
        let z := word j * word i * (word j)⁻¹
        let w := z * (y * z * y⁻¹)
        (w ^ 3 = 1 ∨ w ^ 5 = 1) ∧ w ≠ 1 := by
  decide +kernel

private theorem standard_core_even (B : Subgroup D) (hS : eight ≤ B)
    (hthree : 3 ∣ Nat.card B) : B.pCoreIn 2 ≤ alternatingGroup (Fin 5) := by
  let Q := B.pCoreIn 2
  have hQ : IsPGroup 2 Q := isPGroup_pCoreIn 2 B
  have hn : B ≤ normalizer (Q : Set D) := by
    apply le_normalizer_iff.mpr
    intro b hb x hx
    obtain ⟨r, hr, rfl⟩ := hx
    exact ⟨⟨b, hb⟩ * r * (⟨b, hb⟩ : B)⁻¹,
      (inferInstance : (pCore 2 B).Normal).conj_mem r hr ⟨b, hb⟩, rfl⟩
  have hQS : Q ≤ eight := by
    intro q hq
    obtain ⟨r, hr, he⟩ := hq
    have hh := pCore_isPGroup.le_sylow_of_normal (eightSylow.subtype hS) hr
    exact he ▸ hh
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := B) 3 hthree
  intro x hx
  apply Equiv.Perm.mem_alternatingGroup.mpr
  by_contra hodd
  obtain ⟨i, rfl⟩ := hQS hx
  have hy3 : (y.val : D) ^ 3 = 1 := by
    exact congrArg Subtype.val (show y ^ 3 = 1 by simpa only [hy] using pow_orderOf_eq_one y)
  have hyne : (y.val : D) ≠ 1 := by
    intro h
    have : y = 1 := Subtype.ext h
    simp [this] at hy
  obtain ⟨j, hw, hwne⟩ := odd_core_witness i y.val hodd hy3 hyne
  let z := word j * word i * (word j)⁻¹
  have hz : z ∈ Q := (hn (hS ⟨j, rfl⟩) (word i)).mp hx
  have hyz : y.val * z * y.val⁻¹ ∈ Q := (hn y.property z).mp hz
  let w : Q := ⟨z * (y.val * z * y.val⁻¹), Q.mul_mem hz hyz⟩
  have hw1 : w = 1 := by
    rcases hw with h3 | h5
    · apply (hQ.powEquiv (by decide : Nat.Coprime 2 3)).injective
      exact (Subtype.ext h3 : w ^ 3 = 1).trans (one_pow 3).symm
    · apply (hQ.powEquiv (by decide : Nat.Coprime 2 5)).injective
      exact (Subtype.ext h5 : w ^ 5 = 1).trans (one_pow 5).symm
  exact hwne (congrArg Subtype.val hw1)

/-- A local subgroup of S₅ containing a Sylow two-subgroup and an element
of order three has even two-core. -/
theorem core_le_alternating (B : Subgroup (Equiv.Perm (Fin 5)))
    (S : Sylow 2 (Equiv.Perm (Fin 5))) (hSB : (S : Subgroup _) ≤ B)
    (hthree : 3 ∣ Nat.card B) : B.pCoreIn 2 ≤ alternatingGroup (Fin 5) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D S eightSylow
  let f := MulAut.conj g
  have hmap : (S : Subgroup D).map f.toMonoidHom = eight := by
    have h := congrArg (fun Q : Sylow 2 D => (Q : Subgroup D)) hg
    rwa [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  have hS : eight ≤ B.map f.toMonoidHom := hmap ▸ map_mono hSB
  have ht : 3 ∣ Nat.card (B.map f.toMonoidHom) := by
    rwa [← Nat.card_congr (B.equivMapOfInjective f.toMonoidHom f.injective).toEquiv]
  have hc := standard_core_even _ hS ht
  have hf := Alternating.FiveBorelCentralFactor.core_image_le f.toMonoidHom B
  intro x hx
  have h := hc (hf (mem_map_of_mem f.toMonoidHom hx))
  have hs := Equiv.Perm.mem_alternatingGroup.mp h
  apply Equiv.Perm.mem_alternatingGroup.mpr
  change (g * x * g⁻¹).sign = 1 at hs
  simpa only [map_mul, map_inv,
    mul_comm (Equiv.Perm.sign g) (Equiv.Perm.sign x), mul_inv_cancel_right] using hs
end Theory.SpecificGroups.SymmetricFive.LocalTwoCore
