module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Inputs
public import Theory.Mathieu.M24.Properties.Order
public import Theory.GroupTheory.PrimeCyclicCoverage
public import Theory.GroupTheory.PrimeOrderLift
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu
public import Mathlib.GroupTheory.Perm.Centralizer

/-!
# The max1 subgroup has no element of order 35

In the concrete M₂₄ permutation model, a certified element of order five
has cycle type 5⁴1⁴. Its centralizer even in S₂₄ has order 360000, prime to
seven. Sylow conjugacy for cyclic subgroups of order five therefore
excludes order 35 from M₂₄. The certified elementary abelian kernel of
the max1-to-M₂₄ quotient has order 2¹¹, so an element of odd order 35
would retain its order in that quotient.

This is the max1 exclusion used by the J₄ conjugacy reduction. The actual
local quotient and matrix provenance are in `LocalStructure.Mathieu`;
no ambient J₄ order or overgroup classification is used here.
-/

public section

open Subgroup
open Sporadic.Mathieu

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy

private def fivePerm : Equiv.Perm (Fin 24) :=
  m24GeneratorA * m24GeneratorB * m24GeneratorA * m24GeneratorB *
    m24GeneratorA * m24GeneratorB * m24GeneratorB * m24GeneratorA *
      m24GeneratorB * m24GeneratorB

private noncomputable def five : M24 :=
  let a : M24 := ⟨m24GeneratorA, m24GeneratorA_mem⟩
  let b : M24 := ⟨m24GeneratorB, m24GeneratorB_mem⟩
  a * b * a * b * a * b * b * a * b * b

private theorem five_order : orderOf five = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [← Subgroup.orderOf_coe]
  change orderOf fivePerm = 5
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

private theorem centralizer_five_card :
    Nat.card (centralizer ({fivePerm} : Set (Equiv.Perm (Fin 24)))) = 360000 := by
  rw [Equiv.Perm.nat_card_centralizer]
  have ht : fivePerm.cycleType = {5, 5, 5, 5} := by decide +kernel
  rw [ht]
  decide +kernel

private theorem no_order_thirtyFive_of_five_centralizer
    {G A : Type*} [Group G] [Finite G] [Group A]
    (f : G →* A) (hf : Function.Injective f) (r : G) (hr : orderOf r = 5)
    (hsq : ¬ 5 ^ 2 ∣ Nat.card G)
    (hC : ¬ 7 ∣ Nat.card (centralizer ({f r} : Set A))) (x : G) :
    orderOf x ≠ 35 := by
  intro hx
  have hu : orderOf (x ^ 7) = 5 := by
    norm_num [orderOf_pow, hx]
  obtain ⟨k, g, hg⟩ :=
    PrimeCyclicCoverage.exists_conjugate_pow_of_prime_sq_not_dvd
      (by decide : Nat.Prime 5) hsq hu hr
  have hcomm : Commute (g * x * g⁻¹) r := by
    rw [hg]
    have h := (Commute.self_pow x (7 * k)).map (MulAut.conj g).toMonoidHom
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← pow_mul] using h
  let y : centralizer ({f r} : Set A) :=
    ⟨f (g * x * g⁻¹), mem_centralizer_singleton_iff.mpr (hcomm.map f).eq⟩
  have hy : orderOf y = 35 := by
    rw [← Subgroup.orderOf_coe]
    exact (orderOf_injective f hf _).trans (((MulAut.conj g).orderOf_eq x).trans hx)
  have hd := orderOf_dvd_natCard y
  rw [hy] at hd
  exact hC ((by decide : 7 ∣ 35).trans hd)

/-- The concrete Mathieu group M₂₄ omits order 35. -/
theorem m24_orderOf_ne_thirtyFive (x : M24) : orderOf x ≠ 35 := by
  apply no_order_thirtyFive_of_five_centralizer M24.subtype M24.subtype_injective
    five five_order (by rw [m24_order]; decide) ?_ x
  change ¬ 7 ∣ Nat.card (centralizer ({fivePerm} : Set (Equiv.Perm (Fin 24))))
  rw [centralizer_five_card]
  decide

/-- The literal max1 subgroup omits order 35. -/
theorem max1_orderOf_ne_thirtyFive (x : Janko4.Cardinality.max1Subgroup
    Janko4.matrixA_mul_self Janko4.matrixB_pow_four) : orderOf x ≠ 35 := by
  intro hx
  let e := Janko4.LocalStructure.localQuotientEquivM24
    Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  let f := e.toMonoidHom.comp (QuotientGroup.mk'
    (Janko4.Cardinality.localKernel Janko4.matrixA_mul_self Janko4.matrixB_pow_four))
  have hk : f.ker = Janko4.Cardinality.localKernel
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four := by
    ext y
    change e (QuotientGroup.mk' _ y) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective]
    exact QuotientGroup.eq_one_iff y
  have hp : IsPGroup 2 f.ker := by
    rw [hk]
    exact IsPGroup.of_card (n := 11) (Janko4.Cardinality.localKernel_card _ _)
  exact m24_orderOf_ne_thirtyFive (f x)
    ((f.orderOf_map_eq_of_coprime_of_isPGroup_ker hp x (by rw [hx]; decide)).trans hx)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy
