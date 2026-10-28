module

public import Theory.SpecificGroups.SymmetricThreeProduct.NormalThreeSubgroups
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.SubgroupPartitionCounting

/-!
# Subnormal copies of `S₃` in `S₃ × S₃`

The diagonal copy of `S₃` is not normal in the product.  The point of this
lemma is that it is not subnormal either.  We adjoin the normal subgroup
`A₃ × A₃`; the resulting subgroup has odd index three over the given copy.
The prime-to-two residual argument then identifies the copy with the unique
prime-to-two residual of that join.  The join is normal in the whole product,
so the same identification applies to every conjugate.

This is the concrete finite-model input used in Aschbacher--Smith 14.7.70.
-/

@[expose] public section
open Subgroup
namespace SymmetricThreeProduct

private theorem commutator_cube : ∀ x y : S3,
    (x * y * x⁻¹ * y⁻¹) ^ 3 = 1 := by
  decide +kernel

private theorem commutator_mem_threeCore : ∀ x y : G,
    (x.1 * y.1 * x.1⁻¹ * y.1⁻¹) ^ 3 = 1 ∧
      (x.2 * y.2 * x.2⁻¹ * y.2⁻¹) ^ 3 = 1 := by
  intro x y
  exact ⟨commutator_cube x.1 y.1, commutator_cube x.2 y.2⟩

private def cycle : S3 := Equiv.swap 0 1 * Equiv.swap 1 2

private theorem symmetricThree_primeToResidual {D : Type*} [Group D]
    (e : D ≃* S3) : primeToResidual 2 D = ⊤ := by
  apply top_unique
  intro x _
  have hword : ∀ a : S3, ∃ b c : S3, b ^ 2 = 1 ∧ c ^ 2 = 1 ∧ a = b * c := by
    decide +kernel
  obtain ⟨b, c, hb, hc, hbc⟩ := hword (e x)
  have hpow (a : S3) (ha : a ^ 2 = 1) : e.symm a ∈ primeToResidual 2 D := by
    apply mem_primeToResidual_of_pow (n := 1)
    simpa only [pow_one, map_pow, map_one] using congrArg e.symm ha
  have hx := (primeToResidual 2 D).mul_mem (hpow b hb) (hpow c hc)
  simpa only [← map_mul, ← hbc, e.symm_apply_apply] using hx

private theorem threeCore_card : Nat.card (threeCore : Subgroup S3) = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem threeCore_prod_card : Nat.card (threeCore.prod threeCore : Subgroup G) = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem symmetricThree_card (K : Subgroup G) (e : K ≃* S3) :
    Nat.card K = 6 := by
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

private theorem intersection_card (K : Subgroup G) (e : K ≃* S3) :
    Nat.card (K ⊓ (threeCore.prod threeCore) : Subgroup G) = 3 := by
  let z : K := e.symm cycle
  have hzpow : (z : G) ^ 3 = 1 := by
    have h := congrArg e.symm (show cycle ^ 3 = 1 by decide)
    simpa [z] using congrArg Subtype.val h
  have hzne : (z : G) ≠ 1 := by
    intro hz
    have hz' : z = 1 := Subtype.ext hz
    have : cycle = 1 := by
      simpa [z] using congrArg e hz'
    exact (by decide : cycle ≠ 1) this
  have horder : orderOf (z : G) = 3 := by
    apply (Nat.dvd_prime Nat.prime_three |>.mp
      (orderOf_dvd_of_pow_eq_one hzpow)).resolve_left
    intro h
    exact hzne (orderOf_eq_one_iff.mp h)
  have hzmem : (z : G) ∈ (K ⊓ threeCore.prod threeCore : Subgroup G) := by
    refine ⟨z.property, ?_⟩
    change (z : G).1 ^ 3 = 1 ∧ (z : G).2 ^ 3 = 1
    constructor
    · simpa using congrArg Prod.fst hzpow
    · simpa using congrArg Prod.snd hzpow
  have hthree : 3 ∣ Nat.card (K ⊓ threeCore.prod threeCore : Subgroup G) := by
    have hzdiv := (K ⊓ threeCore.prod threeCore : Subgroup G).orderOf_dvd_natCard hzmem
    simpa [horder] using hzdiv
  have hdiv : Nat.card (K ⊓ threeCore.prod threeCore : Subgroup G) ∣ Nat.card K :=
    by
      have hdiv' := card_subgroup_dvd_card
        ((K ⊓ threeCore.prod threeCore : Subgroup G).subgroupOf K)
      rw [← Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv]
      exact hdiv'
  have hle : Nat.card (K ⊓ threeCore.prod threeCore : Subgroup G) ≤ 6 := by
    have hleK := Nat.le_of_dvd (Nat.card_pos (α := K)) hdiv
    simpa [symmetricThree_card K e] using hleK
  have hne : Nat.card (K ⊓ threeCore.prod threeCore : Subgroup G) ≠ 6 := by
    intro heq
    have hIntEq : K ⊓ threeCore.prod threeCore = K := by
      apply eq_of_le_of_card_ge inf_le_left
      rw [heq, symmetricThree_card K e]
    have hKle : K ≤ (threeCore.prod threeCore : Subgroup G) := by
      rw [← hIntEq]
      exact inf_le_right
    have hbad' := card_subgroup_dvd_card (K.subgroupOf (threeCore.prod threeCore : Subgroup G))
    have hbad : Nat.card K ∣ Nat.card (threeCore.prod threeCore : Subgroup G) := by
      rw [← Nat.card_congr (subgroupOfEquivOfLe hKle).toEquiv]
      exact hbad'
    rw [symmetricThree_card K e, threeCore_prod_card] at hbad
    norm_num at hbad
  have hpos : 0 < Nat.card (K ⊓ threeCore.prod threeCore : Subgroup G) :=
    Nat.card_pos (α := (K ⊓ threeCore.prod threeCore : Subgroup G))
  obtain ⟨n, hn⟩ := hthree
  have hnle : n ≤ 2 := by omega
  interval_cases n <;> omega

private theorem join_card (K : Subgroup G) (e : K ≃* S3) :
    Nat.card (K ⊔ threeCore.prod threeCore : Subgroup G) = 18 := by
  have hnorm : K ≤ normalizer (threeCore.prod threeCore : Set G) :=
    le_normalizer_of_normal
  have hmul := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (threeCore.prod threeCore : Subgroup G) K hnorm
  rw [threeCore_prod_card, inf_comm, intersection_card K e] at hmul
  have hKcard : Nat.card K = 6 := symmetricThree_card K e
  rw [hKcard] at hmul
  have hmul' : 54 = 3 * Nat.card (K ⊔ threeCore.prod threeCore : Subgroup G) := by
    simpa [sup_comm] using hmul
  omega

private theorem join_normal (K : Subgroup G) :
    (K ⊔ threeCore.prod threeCore : Subgroup G).Normal := by
  let A : Subgroup G := threeCore.prod threeCore
  let P : Subgroup G := K ⊔ A
  have hcomm (g x : G) : g * x * g⁻¹ * x⁻¹ ∈ A := by
    exact commutator_mem_threeCore g x
  have hnorm : P.Normal := by
    refine ⟨?_⟩
    intro x hx g
    change x ∈ K ⊔ A at hx
    rw [mem_sup_of_normal_right] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    have hy' : g * y * g⁻¹ ∈ P := by
      have hc : g * y * g⁻¹ * y⁻¹ ∈ A := hcomm g y
      have hm := P.mul_mem (mem_sup_right hc) (mem_sup_left hy)
      simpa [mul_assoc] using hm
    have hzA : g * z * g⁻¹ ∈ A := (inferInstance : A.Normal).conj_mem z hz g
    have hz' : g * z * g⁻¹ ∈ P := mem_sup_right hzA
    simpa [mul_assoc] using P.mul_mem hy' hz'
  exact hnorm

private def map_equiv_of_conj (K : Subgroup G) (g : G) (e : K ≃* S3) :
    K.map (MulAut.conj g).toMonoidHom ≃* S3 := by
  exact (MulEquiv.subgroupMap (MulAut.conj g) K).symm.trans e

/-- Every subnormal subgroup of `S₃ × S₃` with a specified `S₃` equivalence is normal. -/
private theorem subnormal_symmetricThree_normal_of_equiv (K : Subgroup G) (hK : K.IsSubnormal)
    (e : K ≃* S3) : K.Normal := by
  let A : Subgroup G := threeCore.prod threeCore
  let P : Subgroup G := K ⊔ A
  have hPnormal : P.Normal := join_normal K
  have hKP : K ≤ P := le_sup_left
  have hindex : K.relIndex P = 3 := by
    have hrel := relIndex_mul_card_of_le hKP
    rw [join_card K e] at hrel
    have hKcard : Nat.card K = 6 := symmetricThree_card K e
    rw [hKcard] at hrel
    omega
  have hresK : primeToResidual 2 (K.subgroupOf P) = ⊤ := by
    exact symmetricThree_primeToResidual ((subgroupOfEquivOfLe hKP).trans e)
  have hsubK : (K.subgroupOf P).IsSubnormal := hK.subgroupOf
  have hcop : Nat.Coprime 2 (K.subgroupOf P).index := by
    change Nat.Coprime 2 (K.relIndex P)
    simpa [hindex] using (show Nat.Coprime 2 3 by decide)
  have hEqK : primeToResidual 2 P = K.subgroupOf P :=
    primeToResidual_eq_of_subnormal_coprime_index 2 (K.subgroupOf P)
      hsubK hresK hcop
  have hconj (g : G) : K.map (MulAut.conj g).toMonoidHom = K := by
    let L : Subgroup G := K.map (MulAut.conj g).toMonoidHom
    have hLP : L ≤ P := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hyP := hPnormal.conj_mem y (mem_sup_left hy) g
      exact hyP
    have hsubL : (L.subgroupOf P).IsSubnormal :=
      (hK.map (MulAut.conj g).surjective).subgroupOf
    have hresL : primeToResidual 2 (L.subgroupOf P) = ⊤ := by
      exact symmetricThree_primeToResidual
        ((subgroupOfEquivOfLe hLP).trans (map_equiv_of_conj K g e))
    have hcopL : Nat.Coprime 2 (L.subgroupOf P).index := by
      have hcardL : Nat.card L = 6 := by
        change Nat.card (K.map (MulAut.conj g).toMonoidHom) = 6
        rw [card_map_of_injective (MulAut.conj g).injective]
        exact symmetricThree_card K e
      have hrelL := relIndex_mul_card_of_le hLP
      rw [join_card K e] at hrelL
      rw [hcardL] at hrelL
      have hrelidx : L.relIndex P = 3 := by omega
      change Nat.Coprime 2 (L.relIndex P)
      simpa [hrelidx] using (show Nat.Coprime 2 3 by decide)
    have hEqL : primeToResidual 2 P = L.subgroupOf P :=
      primeToResidual_eq_of_subnormal_coprime_index 2 (L.subgroupOf P)
        hsubL hresL hcopL
    have hsubeq : L.subgroupOf P = K.subgroupOf P := hEqL.symm.trans hEqK
    have hmapK := congrArg (fun H : Subgroup P => H.map P.subtype) hsubeq
    simpa only [map_subgroupOf_eq_of_le hKP, map_subgroupOf_eq_of_le hLP] using hmapK
  refine ⟨?_⟩
  intro x hx g
  have hmap := hconj g
  have hx' : g * x * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := by
    refine ⟨x, hx, ?_⟩
    simp [MulAut.conj_apply]
  rw [hmap] at hx'
  exact hx'

/-- Every subnormal subgroup of `S₃ × S₃` which is isomorphic to `S₃` is normal. -/
theorem subnormal_symmetricThree_normal (K : Subgroup G) (hK : K.IsSubnormal)
    (he : Nonempty (K ≃* S3)) : K.Normal := by
  obtain ⟨e⟩ := he
  exact subnormal_symmetricThree_normal_of_equiv K hK e

end SymmetricThreeProduct
