module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.ModuleSelection.Basic

/-!
# The finite permutation input to the four-space obstruction

The even stabilizer of three pairs and a singleton has order 24. The finite
calculation needed here says that every other even permutation can be multiplied
on the right by an element of that stabilizer to obtain an element of order five
or seven. Consequently any overgroup whose order divides 576 is the stabilizer
itself, and has index 105 in A₇.

`PermutationCertificate` records this calculation as an explicit outstanding
obligation. The deductions below do not assert that the certificate has been
constructed. No representation, model comparison or invariant plane appears in
its contract.

Source: the partition-stabilizer exclusion in Aschbacher–Smith,
*The Classification of Quasithin Groups*, 13.8.24, printed p.959/PDF p.976.
-/

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.ModuleSelection.FourSpace

/-- The finite A₇ calculation still required for the four-space exclusion. -/
@[expose] public def PermutationCertificate : Prop :=
  Nat.card evenPairStabilizer = 24 ∧
    ∀ g : A7, g ∉ evenPairStabilizer →
      ∃ p ∈ evenPairStabilizer, orderOf (g * p) = 5 ∨ orderOf (g * p) = 7

/-- A subgroup of order dividing 576 cannot properly contain the pair
stabilizer, provided the stated finite permutation calculation holds. -/
public theorem overgroup_eq_of_certificate (hcert : PermutationCertificate)
    (K : Subgroup A7) (hPK : evenPairStabilizer ≤ K) (hc : Nat.card K ∣ 576) :
    K = evenPairStabilizer := by
  apply le_antisymm _ hPK
  intro g hg
  by_contra hout
  obtain ⟨p, hp, ho | ho⟩ := hcert.2 g hout
  · have hd := (K.orderOf_dvd_natCard (K.mul_mem hg (hPK hp))).trans hc
    rw [ho] at hd
    norm_num at hd
  · have hd := (K.orderOf_dvd_natCard (K.mul_mem hg (hPK hp))).trans hc
    rw [ho] at hd
    norm_num at hd

/-- The cardinality clause gives index 105 in the actual alternating group. -/
public theorem pair_index_of_certificate (hcert : PermutationCertificate) :
    evenPairStabilizer.index = 105 := by
  have hc : Nat.card A7 = 2520 := by
    have h := two_mul_nat_card_alternatingGroup (α := Fin 7)
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at h ⊢
    omega
  have h := evenPairStabilizer.card_mul_index
  rw [hcert.1, hc] at h
  omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.ModuleSelection.FourSpace
