module

public import Theory.SpecificGroups.ONan.DerivedCover
public import Theory.GroupTheory.OddCentralInvolutionLifting
public import Mathlib.GroupTheory.PGroup

/-!
# Central-cover bounds from compatible O'Nan lifts

Restrict a compatible linear lift to the derived matrix group. Its image in
any perfect central cover is the whole group. The order-three kernel bound
from `DerivedCover` then bounds that cover's center, without requiring an
odd-primary hypothesis. Perfectness of the model follows from the actual
central-quotient isomorphism supplied by the consumer.

The odd-kernel involution argument also constructs unique lifts of every
involutory family, preserving all Coxeter relations.

The center bounds remain conditional transfer results. Existence of a compatible lift, or
universality of the derived matrix cover, is still unproved here. In
particular this module does not yet establish the unconditional O'Nan branch
of Aschbacher--Smith A.2.19 (printed pp.40--41) or the multiplier input to
I.2.1 (printed p.409). The source multiplier entry is GLS3 Table 5.3s,
printed p.280.
-/

namespace ONan.Cover

/-- A compatible map from the derived matrix cover to a perfect central
cover forces its center order to divide three. Perfectness of the model
and surjectivity of the map are deduced, not additional premises. -/
public theorem center_card_dvd_three_of_derived_lift
    {G : Type*} [Group G] [Group.IsPerfect G]
    (e : G ⧸ Subgroup.center G ≃* Model)
    (f : commutator linearSubgroup →* G)
    (hfac : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))).comp f =
      derivedProjection) : Nat.card (Subgroup.center G) ∣ 3 := by
  let : Group.IsPerfect Model := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let g := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))
  have hker : g.ker = Subgroup.center G := by
    ext x
    change e (QuotientGroup.mk' (Subgroup.center G) x) = 1 ↔ x ∈ Subgroup.center G
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hf : Function.Surjective f := by
    apply PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect g f
    · rw [hfac]
      exact derivedProjection_surjective
    · exact hker.le
  have h := Theory.GroupTheory.kernel_card_dvd_of_surjective_factor
    derivedProjection g f hf hfac
  rw [hker] at h
  exact h.trans derivedProjection_ker_card_dvd_three

/-- The original linear-lift interface already forces the sharper bound three,
without a primary or odd-order hypothesis on the center. -/
public theorem center_card_dvd_three_of_lift
    {G : Type*} [Group G] [Group.IsPerfect G]
    (e : G ⧸ Subgroup.center G ≃* Model)
    (f : linearSubgroup →* G)
    (hfac : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))).comp f =
      projection) : Nat.card (Subgroup.center G) ∣ 3 := by
  apply center_card_dvd_three_of_derived_lift e
    (f.comp (commutator linearSubgroup).subtype)
  rw [← MonoidHom.comp_assoc, hfac]
  rfl

/-- In a finite nontrivial central cover receiving a compatible linear lift,
the center has exactly three elements. The lift remains an explicit premise. -/
public theorem center_card_eq_three_of_lift
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    [Nontrivial (Subgroup.center G)]
    (e : G ⧸ Subgroup.center G ≃* Model)
    (f : linearSubgroup →* G)
    (hfac : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))).comp f =
      projection) : Nat.card (Subgroup.center G) = 3 := by
  have h := (Nat.dvd_prime Nat.prime_three).mp (center_card_dvd_three_of_lift e f hfac)
  exact h.resolve_left (ne_of_gt Finite.one_lt_card)

/-- Every involutory generating family of the actual projective model has
unique involutory lifts in an odd primary central cover, and all pairwise
Coxeter relations hold on those lifts. This supplies the initial lifting step
for an involutory presentation; its additional relators remain to be proved. -/
public theorem existsUnique_involution_lift_family
    {G ι : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (hP : IsPGroup p (Subgroup.center G))
    (e : G ⧸ Subgroup.center G ≃* Model)
    (t : ι → Model) (ht : ∀ i, t i ^ 2 = 1) :
    ∃! a : ι → G,
      (∀ i, e (QuotientGroup.mk' (Subgroup.center G) (a i)) = t i ∧ a i ^ 2 = 1) ∧
      (∀ i j n, (t i * t j) ^ n = 1 → (a i * a j) ^ n = 1) := by
  have : Fact p.Prime := ⟨hp⟩
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))
  have hq : Function.Surjective q :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = Subgroup.center G := by
    ext x
    change e (QuotientGroup.mk' (Subgroup.center G) x) = 1 ↔ x ∈ Subgroup.center G
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hodd : Odd (Nat.card q.ker) := by
    rw [hker]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
    rw [hn]
    exact (hp.odd_of_ne_two hpodd).pow
  have hex (i : ι) := OddCentralLifting.exists_involution_lift q hodd hq (t i) (ht i)
  let a : ι → G := fun i => Classical.choose (hex i)
  have ha (i : ι) : q (a i) = t i ∧ a i ^ 2 = 1 := Classical.choose_spec (hex i)
  refine ⟨a, ⟨ha, ?_⟩, ?_⟩
  · intro i j n hn
    apply OddCentralLifting.involution_product_relation q hodd hker.le
      (ha i).2 (ha j).2 n
    simpa only [(ha i).1, (ha j).1] using hn
  · intro b hb
    funext i
    exact OddCentralLifting.involution_lift_unique q hodd hker.le
      (hb.1 i).2 (ha i).2 ((hb.1 i).1.trans (ha i).1.symm)

end ONan.Cover
