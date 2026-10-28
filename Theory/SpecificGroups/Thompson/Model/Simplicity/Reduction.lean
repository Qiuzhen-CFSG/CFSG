module

public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Normal-subgroup reduction for the Thompson matrix model

A nontrivial normal subgroup of a finite group contains an element of prime
order. Consequently, representatives meeting every prime-order cyclic class
prove simplicity once each representative normally generates the group. This
elementary reduction is adapted from the Janko4 matrix-model certification in
this repository; the remaining certificates must be proved for the actual
Thompson matrices.

The ATLAS standard-generator entry lists `(ab)^19 = 1`. If certified for the
matrices, this relation implies that either generator normally generates: in a
quotient killing one generator, the other has coprime power relations.

Source: https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Th/ .
-/

public section

namespace Thompson.Simplicity

/-- Noncommuting certified matrices give a nontrivial fixed carrier. -/
instance model_nontrivial : Nontrivial Model := by
  apply nontrivial_of_ne generatorA generatorB
  intro h
  exact generator_mul_ne (by rw [h])

/-- A subgroup containing the two certified matrices is the whole model. -/
theorem eq_top_of_generators_mem (H : Subgroup Model)
    (ha : generatorA ∈ H) (hb : generatorB ∈ H) : H = ⊤ := by
  apply top_unique
  rw [← closure_generators]
  apply (Subgroup.closure_le _).mpr
  rintro x (rfl | rfl)
  · exact ha
  · exact hb

/-- Prime-order cyclic coverage and normal generation imply simplicity. -/
theorem isSimpleGroup_of_prime_representatives
    {ι : Type*} (r : ι → Model)
    (hcover : ∀ x : Model, (orderOf x).Prime →
      ∃ i k g, r i = g * x ^ k * g⁻¹)
    (hgenerate : ∀ i, Subgroup.normalClosure ({r i} : Set Model) = ⊤) :
    IsSimpleGroup Model := by
  constructor
  intro N hN
  let : N.Normal := hN
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  right
  have : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hbot
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd
    (ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial N)))
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) p hpdvd
  have hxprime : (orderOf (x : Model)).Prime := by simpa using hx ▸ hp
  obtain ⟨i, k, g, hi⟩ := hcover x hxprime
  have hiN : r i ∈ N := hi ▸ hN.conj_mem _ (N.pow_mem x.property k) g
  have hle : Subgroup.normalClosure ({r i} : Set Model) ≤ N :=
    Subgroup.normalClosure_le_normal (by simpa using hiN)
  rw [hgenerate i] at hle
  exact top_unique hle

/-- A certified order-19 product relation makes the ATLAS involution a normal
generator of the actual matrix model. -/
theorem normalClosure_generatorA_of_ab19 (hab19 : (generatorA * generatorB) ^ 19 = 1) :
    Subgroup.normalClosure ({generatorA} : Set Model) = ⊤ := by
  let N := Subgroup.normalClosure ({generatorA} : Set Model)
  have haN : generatorA ∈ N := Subgroup.subset_normalClosure (Set.mem_singleton _)
  apply eq_top_of_generators_mem N haN
  let q := QuotientGroup.mk' N
  have hqa : q generatorA = 1 := (QuotientGroup.eq_one_iff generatorA).mpr haN
  have hqb3 : q generatorB ^ 3 = 1 := by simpa using congrArg q generatorB_cube
  have hqb19 : q generatorB ^ 19 = 1 := by simpa [hqa] using congrArg q hab19
  exact (QuotientGroup.eq_one_iff generatorB).mp
    ((pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 3 19)).mp ⟨hqb3, hqb19⟩)

/-- The same order-19 product relation makes the ATLAS order-three element
a normal generator of the actual matrix model. -/
theorem normalClosure_generatorB_of_ab19 (hab19 : (generatorA * generatorB) ^ 19 = 1) :
    Subgroup.normalClosure ({generatorB} : Set Model) = ⊤ := by
  let N := Subgroup.normalClosure ({generatorB} : Set Model)
  have hbN : generatorB ∈ N := Subgroup.subset_normalClosure (Set.mem_singleton _)
  apply eq_top_of_generators_mem N ?_ hbN
  let q := QuotientGroup.mk' N
  have hqb : q generatorB = 1 := (QuotientGroup.eq_one_iff generatorB).mpr hbN
  have hqa2 : q generatorA ^ 2 = 1 := by simpa using congrArg q generatorA_sq
  have hqa19 : q generatorA ^ 19 = 1 := by simpa [hqb] using congrArg q hab19
  exact (QuotientGroup.eq_one_iff generatorA).mp
    ((pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 2 19)).mp ⟨hqa2, hqa19⟩)

/-- The product of the two certified generators normally generates the model,
using only their orders two and three. -/
theorem normalClosure_ab :
    Subgroup.normalClosure ({generatorA * generatorB} : Set Model) = ⊤ := by
  let N := Subgroup.normalClosure ({generatorA * generatorB} : Set Model)
  have habN : generatorA * generatorB ∈ N :=
    Subgroup.subset_normalClosure (Set.mem_singleton _)
  let q := QuotientGroup.mk' N
  have hqab : q generatorA * q generatorB = 1 := by
    have hq : q (generatorA * generatorB) = 1 :=
      (QuotientGroup.eq_one_iff (generatorA * generatorB)).mpr habN
    simpa only [map_mul] using hq
  have hqb : q generatorB = (q generatorA)⁻¹ := eq_inv_of_mul_eq_one_right hqab
  have hqa2 : q generatorA ^ 2 = 1 := by simpa using congrArg q generatorA_sq
  have hqa3 : q generatorA ^ 3 = 1 := by
    have hb3 : q generatorB ^ 3 = 1 := by simpa using congrArg q generatorB_cube
    simpa [hqb] using hb3
  have haN : generatorA ∈ N := (QuotientGroup.eq_one_iff generatorA).mp
    ((pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 2 3)).mp ⟨hqa2, hqa3⟩)
  have hbN : generatorB ∈ N := by
    have h := N.mul_mem (N.inv_mem haN) habN
    simpa only [inv_mul_cancel_left] using h
  exact eq_top_of_generators_mem N haN hbN

end Thompson.Simplicity
