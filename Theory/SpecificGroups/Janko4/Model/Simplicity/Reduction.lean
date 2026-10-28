module

public import Theory.SpecificGroups.Janko4.Model
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Data.Int.GCD

/-!
# Normal generation reductions for the J₄ matrix model

A nontrivial normal subgroup of a finite group contains an element of prime
order (Cauchy's theorem). Thus a list meeting all prime-order cyclic classes,
together with normal-generation certificates for its members, proves simplicity.
This is an elementary criterion, independent of recognition or classification.

For the actual matrix model, membership of the two generators proves a subgroup
is the whole group. The relation `(a*b)^37 = 1`, together with `b^4 = 1`, also
shows that `a` normally generates: in the quotient by its normal closure, the
image of `b` has order dividing both 4 and 37. These relations are the Type I
generator conditions at https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J4/ .
They remain explicit hypotheses here.
-/

public section

namespace Janko4.Simplicity

/-- A subgroup containing both certified source generators is the whole carrier. -/
theorem model_eq_top_of_generators_mem {a b : Model}
    (ha : toMatrix a = matrixA) (hb : toMatrix b = matrixB)
    (H : Subgroup Model) (haH : a ∈ H) (hbH : b ∈ H) : H = ⊤ := by
  have hmap : matrixGroup ≤ H.map toAmbient := by
    apply matrixGroup_le_iff _ |>.2
    intro g hg
    rcases hg with hg | hg
    · exact ⟨a, haH, Units.ext (ha.trans hg.symm)⟩
    · exact ⟨b, hbH, Units.ext (hb.trans hg.symm)⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, hyx⟩ := hmap x.property
  exact toAmbient_injective hyx ▸ hy

/-- Prime-order cyclic coverage and normal generation imply simplicity. -/
theorem isSimpleGroup_of_prime_representatives {G : Type*} [Group G] [Finite G]
    [Nontrivial G] {ι : Type*} (r : ι → G)
    (hcover : ∀ x : G, (orderOf x).Prime →
      ∃ i k g, r i = g * x ^ k * g⁻¹)
    (hgenerate : ∀ i, Subgroup.normalClosure ({r i} : Set G) = ⊤) :
    IsSimpleGroup G := by
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
  have hxprime : (orderOf (x : G)).Prime := by simpa using hx ▸ hp
  obtain ⟨i, k, g, hi⟩ := hcover x hxprime
  have hiN : r i ∈ N := hi ▸ hN.conj_mem _ (N.pow_mem x.property k) g
  have hle : Subgroup.normalClosure ({r i} : Set G) ≤ N :=
    Subgroup.normalClosure_le_normal (by simpa using hiN)
  rw [hgenerate i] at hle
  exact top_unique hle

/-- Killing the first generator kills the second, using coprime quotient orders. -/
theorem normalClosure_a_eq_top {a b : Model}
    (ha : toMatrix a = matrixA) (hb : toMatrix b = matrixB)
    (hb4 : b ^ 4 = 1) (hab37 : (a * b) ^ 37 = 1) :
    Subgroup.normalClosure ({a} : Set Model) = ⊤ := by
  let N := Subgroup.normalClosure ({a} : Set Model)
  have haN : a ∈ N := Subgroup.subset_normalClosure (Set.mem_singleton a)
  apply model_eq_top_of_generators_mem ha hb N haN
  let q := QuotientGroup.mk' N
  have hqa : q a = 1 := (QuotientGroup.eq_one_iff a).mpr haN
  have hqb4 : q b ^ 4 = 1 := by simpa using congrArg q hb4
  have hqb37 : q b ^ 37 = 1 := by simpa [hqa] using congrArg q hab37
  exact (QuotientGroup.eq_one_iff b).mp
    ((pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 4 37)).mp ⟨hqb4, hqb37⟩)
end Janko4.Simplicity
