module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.AmbientExtensions.Structure
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup
public import Theory.AtlasPort.LinearGroups.G2.OrderChecks

/-!
# Order obstructions for the small offender actors

The actual actor equivalences determine its order. An odd divisor of the
ambient order must already divide the actor order, since D/N is a two-group.
This excludes large defining primes and the odd part of the triple-seven
covers without identifying any group by its order.

Source: Aschbacher–Smith, F.6.18, pp.309–310, compared with B.5.1,
pp.99–103, in 15.4.18, p.1163.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace QuasisimpleComparison
namespace AmbientExtensions
open GoldschmidtAlternatives

universe u v
variable {A : Type u} [Group A]

/-- The order of a perfect triple cover comes from its specified central quotient. -/
theorem tripleAlternating_card {n : ℕ} [Nontrivial (Fin n)] (h : TripleAlternating A n) :
    Nat.card A = 3 * (n.factorial / 2) := by
  obtain ⟨_, ⟨ez⟩, ⟨eq⟩⟩ := h
  rw [← (center A).card_mul_index, index_eq_card,
    Nat.card_congr ez.toEquiv, Nat.card_congr eq.toEquiv,
    nat_card_alternatingGroup, Nat.card_fin]
  simp [C]

/-- The symmetric triple cover uses its actual permutation quotient. -/
theorem tripleSymmetric_card {n : ℕ} (h : TripleSymmetric A n) :
    Nat.card A = 3 * n.factorial := by
  obtain ⟨f, hf, hz, _⟩ := h
  have he : Extension A (C 3) (Equiv.Perm (Fin n)) := ⟨f, hf, hz⟩
  rw [he.card]
  simp [C, Nat.card_eq_fintype_card, Fintype.card_perm]

/-- Exact orders obtained from the actual eight actor alternatives. -/
theorem actor_card (s : SmallActorModel A) :
    Nat.card A = 168 ∨ Nat.card A = 360 ∨ Nat.card A = 720 ∨
    Nat.card A = 2520 ∨ Nat.card A = 5040 ∨ Nat.card A = 1080 ∨
    Nat.card A = 6048 ∨ Nat.card A = 12096 := by
  cases s with
  | linearThree e =>
    exact Or.inl ((Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_SL)
  | alternatingSix e =>
    have hc : Nat.card A = 360 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num [Nat.factorial]
    tauto
  | symmetricSix e =>
    have hc : Nat.card A = 720 := by
      rw [Nat.card_congr e.toEquiv]
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    tauto
  | alternatingSeven e =>
    have hc : Nat.card A = 2520 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num [Nat.factorial]
    tauto
  | symmetricSeven e =>
    have hc : Nat.card A = 5040 := by
      rw [Nat.card_congr e.toEquiv]
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    tauto
  | tripleSix h =>
    have hc := tripleAlternating_card h
    norm_num [Nat.factorial] at hc
    tauto
  | g2Derived e =>
    have hc : Nat.card A = 6048 := by
      rw [Nat.card_congr e.toEquiv,
        Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
        Atlas.G2.BinaryException.card_H]
    tauto
  | g2 e =>
    have hc := (Nat.card_congr e.toEquiv).trans Atlas.G2.OrderChecks.binary_order
    tauto

/-- Every small actor has order at least 168. -/
theorem actor_card_lower (s : SmallActorModel A) : 168 ≤ Nat.card A := by
  have hc := actor_card s
  omega

/-- All actor orders divide this common multiple. -/
theorem actor_card_dvd (s : SmallActorModel A) : Nat.card A ∣ 60480 := by
  rcases actor_card s with h | h | h | h | h | h | h | h <;> rw [h] <;> decide

/-- The triple-seven odd part divides none of the actor orders. -/
theorem actor_not_945 (s : SmallActorModel A) : ¬ 945 ∣ Nat.card A := by
  rcases actor_card s with h | h | h | h | h | h | h | h <;> rw [h] <;> decide

variable {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D} {K : GroupClass.{u}}
attribute [local instance] offenderSubgroup_normal

/-- An odd divisor survives restriction to the literal offender subgroup. -/
theorem odd_dvd_actor (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    {m : ℕ} (hm : Nat.Coprime m 2) (hd : m ∣ Nat.card D) :
    m ∣ Nat.card (offenderSubgroup ρ) := by
  obtain ⟨a, ha⟩ := h.quotient_twoGroup.exists_card_eq
  have hc : Nat.card D = Nat.card (offenderSubgroup ρ) * 2 ^ a := by
    rw [← ha, ← index_eq_card, card_mul_index]
  rw [hc] at hd
  exact (hm.pow_right a).dvd_of_dvd_mul_right hd

/-- Ambient extensions introduce no prime greater than seven. -/
theorem no_large_prime (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (s : SmallActorModel (offenderSubgroup ρ))
    {p : ℕ} (hp : p.Prime) (hl : 7 < p) : ¬ p ∣ Nat.card D := by
  intro hd
  have hc : Nat.Coprime p 2 := hp.coprime_iff_not_dvd.mpr (by
    intro hd2
    have := Nat.le_of_dvd (by decide : 0 < 2) hd2
    omega)
  have hd' := (odd_dvd_actor h hc hd).trans (actor_card_dvd s)
  have hfactor : 60480 = 2 ^ 6 * 3 ^ 3 * 5 * 7 := by decide
  rw [hfactor] at hd'
  rcases hp.dvd_mul.mp hd' with hd' | hd'
  · rcases hp.dvd_mul.mp hd' with hd' | hd'
    · rcases hp.dvd_mul.mp hd' with hd' | hd'
      · have := Nat.le_of_dvd (by decide : 0 < 2) (hp.dvd_of_dvd_pow hd')
        omega
      · have := Nat.le_of_dvd (by decide : 0 < 3) (hp.dvd_of_dvd_pow hd')
        omega
    · have := Nat.le_of_dvd (by decide : 0 < 5) hd'
      omega
  · have := Nat.le_of_dvd (by decide : 0 < 7) hd'
    omega

/-- In particular an ambient triple-seven cover is impossible. -/
theorem ambient_not_945 (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (s : SmallActorModel (offenderSubgroup ρ)) : ¬ 945 ∣ Nat.card D :=
  fun hd => actor_not_945 s (odd_dvd_actor h (by decide) hd)

end AmbientExtensions
end QuasisimpleComparison
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
