module

public import Theory.SpecificGroups.BabyMonster.NormalSubgroups.Generation
public import Mathlib.Order.Atoms

/-!
# Reduction of normal-subgroup rigidity to a generator centralizer

For the fixed presentation, normal generation and perfectness reduce the
normal-subgroup dichotomy to two local statements: the first generator's
centralizer is maximal, and the center of this centralizer consists of the
identity and the generator. These local statements remain explicit hypotheses
in this module.

If a normal subgroup lies in the generator centralizer, its own centralizer
is normal and contains the generator, hence is the whole group. Otherwise,
maximality says that the normal subgroup and the generator centralizer together
cover the group. In the quotient the generator is then central. Normal
generation makes the quotient abelian, and perfectness makes it trivial.
The bound on the local center eliminates the remaining ambient center.

The intended local data concern the 2A involutions described in §§3.2 and 5.2
of Breuer–Magaard–Wilson (2019), https://arxiv.org/abs/1902.07758.
The reduction itself uses no order or finiteness assumption.
-/

public section
namespace BabyMonster

/-- If the generator centralizer is maximal, every normal subgroup is central
or is the entire group. -/
theorem normal_le_center_or_eq_top_of_generatorCentralizer_isCoatom
    (hmax : IsCoatom generatorCentralizer)
    (N : Subgroup Carrier) [N.Normal] : N ≤ Subgroup.center Carrier ∨ N = ⊤ := by
  by_cases hNC : N ≤ generatorCentralizer
  · left
    have hgen : generator 0 ∈ Subgroup.centralizer (N : Set Carrier) := by
      intro n hn
      exact Subgroup.mem_centralizer_singleton_iff.mp (hNC hn)
    have hC := normal_eq_top_of_generator_mem (Subgroup.centralizer (N : Set Carrier)) 0 hgen
    intro n hn
    apply Subgroup.mem_center_iff.mpr
    intro g
    have hg : g ∈ Subgroup.centralizer (N : Set Carrier) := by rw [hC]; trivial
    exact (hg n hn).symm
  · right
    have hsup : N ⊔ generatorCentralizer = ⊤ := by
      apply hmax.lt_iff.mp
      exact lt_of_le_of_ne le_sup_right (fun he => hNC (he ▸ le_sup_left))
    let q := QuotientGroup.mk' N
    have ht : q (generator 0) ∈ Subgroup.center (Carrier ⧸ N) := by
      apply Subgroup.mem_center_iff.mpr
      intro x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
      have hg : g ∈ N ⊔ generatorCentralizer := by rw [hsup]; trivial
      obtain ⟨n, hn, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
      have hnq : q n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
      change q (n * c) * q (generator 0) = q (generator 0) * q (n * c)
      rw [map_mul, hnq, one_mul, ← map_mul, ← map_mul]
      exact congrArg q (Subgroup.mem_centralizer_singleton_iff.mp hc)
    have hpre := normal_eq_top_of_generator_mem
      ((Subgroup.center (Carrier ⧸ N)).comap q) 0 ht
    have hcomm : IsMulCommutative (Carrier ⧸ N) := by
      apply Subgroup.center_eq_top_iff.mp
      apply top_unique
      intro x _
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
      have hg : g ∈ (Subgroup.center (Carrier ⧸ N)).comap q := by rw [hpre]; trivial
      exact hg
    apply top_unique
    intro x _
    exact (QuotientGroup.eq_one_iff _).mp (Subsingleton.elim (q x) 1)

/-- The small center of the generator centralizer rules out an ambient center
when this centralizer is proper. -/
theorem center_eq_bot_of_generatorCentralizer_center
    (hproper : generatorCentralizer ≠ ⊤)
    (hcenter : ∀ z : generatorCentralizer, z ∈ Subgroup.center generatorCentralizer →
      (z : Carrier) = 1 ∨ (z : Carrier) = generator 0) :
    Subgroup.center Carrier = ⊥ := by
  apply bot_unique
  intro z hz
  have hzC : z ∈ generatorCentralizer := Subgroup.center_le_centralizer _ hz
  have hzZ : (⟨z, hzC⟩ : generatorCentralizer) ∈ Subgroup.center generatorCentralizer := by
    apply Subgroup.mem_center_iff.mpr
    intro c
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz c)
  rcases hcenter ⟨z, hzC⟩ hzZ with h | h
  · exact Subgroup.mem_bot.mpr h
  · exfalso
    apply hproper
    apply top_unique
    intro g _
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rw [← h]
    exact Subgroup.mem_center_iff.mp hz g

/-- Normal-subgroup dichotomy from the two local centralizer statements.
The local hypotheses must be discharged for the fixed presentation. -/
theorem normal_eq_bot_or_eq_top_of_generatorCentralizer
    (hmax : IsCoatom generatorCentralizer)
    (hcenter : ∀ z : generatorCentralizer, z ∈ Subgroup.center generatorCentralizer →
      (z : Carrier) = 1 ∨ (z : Carrier) = generator 0)
    (N : Subgroup Carrier) [N.Normal] : N = ⊥ ∨ N = ⊤ := by
  rcases normal_le_center_or_eq_top_of_generatorCentralizer_isCoatom hmax N with h | h
  · left
    exact bot_unique (h.trans_eq (center_eq_bot_of_generatorCentralizer_center hmax.ne_top hcenter))
  · exact Or.inr h

end BabyMonster
