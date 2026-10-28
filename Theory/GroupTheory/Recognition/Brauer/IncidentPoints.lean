module
public import Theory.GroupTheory.Recognition.Brauer.CommutingIncidence
public import Theory.GroupTheory.Recognition.Brauer.ContainingBlocks
public import Theory.GroupTheory.Recognition.Brauer.BlockIntersection
public import Mathlib.Data.Fintype.Option

/-!
# The distinguished incident points in Brauer's geometry

Brauer, *On finite Desarguesian planes I*, (2F), p. 121, constructs `q + 1`
distinct points on `[j2]`: the point `(j1)` and the points `(j * a)` for
`a` in `Mstar2`. This module retains that construction as a private injection
and proves its lower bound. With an explicit exact incidence count, finite
cardinality makes the injection surjective and gives the enumeration used
in (3C), p. 122. Keeping the count as a hypothesis on the seed makes the
same theorem applicable to the actual dual geometry without postulating
the dual of Brauer's postulate (V).

Distinct commuting involutions give incidence by (2D). The points `(j * a)`
are distinct because their underlying sets meet the base line in at most
one involution. The point `(j1)` is disjoint from that base line and hence
is different from all of them. The fixed-factor count gives `|Mstar2| = q`.
-/

open scoped Pointwise

namespace Theory.GroupTheory.BrauerPlaneSeed

variable {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G)

private theorem exists_distinguished_incident_injection (h2 : orderOf S.j2 = 2) :
    ∃ f : Option S.Mstar2 → {p : S.Point // p ∈ S.lineOf S.j2 h2},
      Function.Injective f ∧
      (f none).val = S.pointOf S.j1 S.j1_order ∧
      ∀ a : S.Mstar2, S.j * (a : G) ∈ ((f (some a)).val : Set G) := by
  classical
  have hj1ne : S.j1 ≠ 1 := by
    intro h
    have ho := S.j1_order
    simp [h] at ho
  have hjne : S.j ≠ 1 := by
    intro h
    have ho := S.j_order
    simp [h] at ho
  have hj1j2 : S.j1 ≠ S.j2 := by
    intro h
    have : (1 : G) * S.j1 = S.j * S.j1 := by simpa using h
    exact hjne (mul_right_cancel this).symm
  have hjj2 : Commute S.j S.j2 := (Commute.refl S.j).mul_right S.j_commute_j1
  have hj1j2c : Commute S.j1 S.j2 := S.j_commute_j1.symm.mul_right (Commute.refl S.j1)
  let l0 : S.Line := ⟨S.baseLine, MulAction.mem_orbit_self _⟩
  let l2 : S.Line := S.lineOf S.j2 h2
  let p1 : S.Point := S.pointOf S.j1 S.j1_order
  have hjl0 : S.j ∈ (l0 : Set G) :=
    Set.mem_smul_set.mpr ⟨1, S.Mstar.one_mem, mul_one S.j⟩
  have hp1l0 : p1 ∈ l0 := S.incident_of_distinct_commuting p1 l0
    S.j1_order S.j_order S.j_ne_j1.symm S.j_commute_j1.symm
    (S.mem_pointOf _ _) hjl0
  have hp1l2 : p1 ∈ l2 := S.incident_of_distinct_commuting p1 l2
    S.j1_order h2 hj1j2 hj1j2c (S.mem_pointOf _ _) (S.mem_lineOf _ _)
  have hmem (a : S.Mstar2) : S.j * (a : G) ∈ (l0 : Set G) :=
    Set.mem_smul_set.mpr ⟨a, a.property.1, rfl⟩
  have hord (a : S.Mstar2) : orderOf (S.j * (a : G)) = 2 :=
    S.orderOf_mem_line l0 (hmem a)
  let p (a : S.Mstar2) : S.Point := S.pointOf (S.j * (a : G)) (hord a)
  have hp (a : S.Mstar2) : S.j * (a : G) ∈ (p a : Set G) := S.mem_pointOf _ _
  have hne (a : S.Mstar2) : S.j * (a : G) ≠ S.j2 := by
    intro heq
    have ha : (a : G) = S.j1 := mul_left_cancel heq
    have hj1C : S.j1 ∈ Subgroup.centralizer {S.j} :=
      Subgroup.mem_centralizer_singleton_iff.mpr S.j_commute_j1.symm.eq
    have hj1mem : S.j1 ∈ S.Mstar ⊓ Subgroup.centralizer {S.j} :=
      ⟨ha ▸ a.property.1, hj1C⟩
    exact hj1ne (by simpa only [S.disjoint_Mstar_centralizer.eq_bot, Subgroup.mem_bot] using hj1mem)
  have hinc (a : S.Mstar2) : p a ∈ l2 := by
    have hac : Commute (a : G) S.j2 :=
      Subgroup.mem_centralizer_singleton_iff.mp a.property.2
    exact S.incident_of_distinct_commuting (p a) l2 (hord a) h2 (hne a)
      (hjj2.mul_left hac) (hp a) (S.mem_lineOf _ _)
  have hpinj : Function.Injective p := by
    intro a b hab
    apply Subtype.ext
    apply mul_left_cancel (a := S.j)
    exact S.point_line_intersection_subsingleton (p a) l0
      ⟨hp a, hmem a⟩ ⟨hab.symm ▸ hp b, hmem b⟩
  have hsep (a : S.Mstar2) : p1 ≠ p a := by
    intro heq
    exact (Set.disjoint_left.mp ((S.mem_iff_disjoint p1 l0).mp hp1l0))
      (heq.symm ▸ hp a) (hmem a)
  let f : Option S.Mstar2 → {p : S.Point // p ∈ l2}
    | none => ⟨p1, hp1l2⟩
    | some a => ⟨p a, hinc a⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => exact (hsep b hab').elim
    | some a =>
      cases b with
      | none => exact (hsep a hab'.symm).elim
      | some b => exact congrArg some (hpinj hab')
  exact ⟨f, hf, rfl, hp⟩

private theorem card_distinguished_parameters : Nat.card (Option S.Mstar2) = S.q + 1 := by
  classical
  let _ := Fintype.ofFinite S.Mstar2
  have hoption : Nat.card (Option S.Mstar2) = Nat.card S.Mstar2 + 1 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_option]
  rw [hoption, S.fixed_factors.2.2.2.2.2.2.2.1]

/-- Brauer I (2F): the line `[j2]` has at least `q + 1` incident points. -/
public theorem distinguished_incident_points_lower_bound (h2 : orderOf S.j2 = 2) :
    S.q + 1 ≤ Nat.card {p : S.Point // p ∈ S.lineOf S.j2 h2} := by
  obtain ⟨f, hf, _⟩ := S.exists_distinguished_incident_injection h2
  simpa only [S.card_distinguished_parameters] using Nat.card_le_card_of_injective f hf

/-- Brauer I (2F) with the exact count from (3A): the points incident with
`[j2]` are `(j1)` and the points containing `j * a`, for `a` in `Mstar2`. -/
public theorem incident_iff_distinguished_point (h2 : orderOf S.j2 = 2)
    (hcount : Nat.card {p : S.Point // p ∈ S.lineOf S.j2 h2} = S.q + 1)
    (p : S.Point) :
    p ∈ S.lineOf S.j2 h2 ↔
      p = S.pointOf S.j1 S.j1_order ∨ ∃ a : S.Mstar2, S.j * (a : G) ∈ (p : Set G) := by
  obtain ⟨f, hf, hnone, hsome⟩ := S.exists_distinguished_incident_injection h2
  have hsurj : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr
      ⟨hf, S.card_distinguished_parameters.trans hcount.symm⟩).2
  constructor
  · intro hp
    obtain ⟨a, ha⟩ := hsurj ⟨p, hp⟩
    have haval : (f a).val = p := congrArg Subtype.val ha
    cases a with
    | none => exact Or.inl (haval.symm.trans hnone)
    | some a => exact Or.inr ⟨a, haval ▸ hsome a⟩
  · rintro (rfl | ⟨a, ha⟩)
    · exact hnone ▸ (f none).property
    · have hord : orderOf (S.j * (a : G)) = 2 := S.orderOf_mem_point p ha
      have heq : (f (some a)).val = p :=
        ((S.pointOf_eq_iff _ hord _).mpr (hsome a)).symm.trans
          ((S.pointOf_eq_iff _ hord _).mpr ha)
      exact heq ▸ (f (some a)).property

end Theory.GroupTheory.BrauerPlaneSeed
