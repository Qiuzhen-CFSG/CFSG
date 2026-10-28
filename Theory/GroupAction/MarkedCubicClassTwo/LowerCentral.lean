module

public import Theory.GroupAction.MarkedCubicClassTwo.Defs

/-!
# Third-layer persistence and class-three quotients

A nonzero term of the lower central series of a nilpotent group strictly
contains the next term: equality would make every later term stabilize.
Thus a nontrivial third layer survives modulo the fourth and is central
there. Any subsequent quotient retaining a cubic third layer has class
exactly three, with both inequalities verified on the literal quotient.

Source: the descending-central-series step in Aschbacher–Smith F.6.16,
printed p.308, combined manuscript of 1 March 2004. Lean indexes the
initial whole-group term by zero, so the third and fourth source layers
are `lowerCentralSeries 2` and `lowerCentralSeries 3`.
-/

public section


open Subgroup
namespace MarkedCubicClassTwo
variable {P : Type*} [Group P]

/-- A nonzero lower-central term cannot stabilize in a nilpotent group. -/
theorem lowerCentralSeries_strict_of_ne_bot [Group.IsNilpotent P] {n : ℕ}
    (hn : (⊤ : Subgroup P).lowerCentralSeries n ≠ ⊥) :
    (⊤ : Subgroup P).lowerCentralSeries (n + 1) < (⊤ : Subgroup P).lowerCentralSeries n := by
  apply lt_of_le_of_ne (Subgroup.lowerCentralSeries_antitone ⊤ (Nat.le_succ n))
  intro he
  have hstable (k : ℕ) : (⊤ : Subgroup P).lowerCentralSeries (n + k) =
      (⊤ : Subgroup P).lowerCentralSeries n := by
    induction k with
    | zero => rw [Nat.add_zero]
    | succ k ih =>
      rw [Nat.add_succ, Subgroup.lowerCentralSeries_succ, ih, ← Subgroup.lowerCentralSeries_succ, he]
  obtain ⟨m, hm⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp (inferInstance : Group.IsNilpotent P)
  have hzero : (⊤ : Subgroup P).lowerCentralSeries (n + m) = ⊥ := by
    apply le_bot_iff.mp
    rw [← hm]
    exact Subgroup.lowerCentralSeries_antitone ⊤ (Nat.le_add_left m n)
  exact hn ((hstable m).symm.trans hzero)

/-- The contrary class-greater-than-two branch survives modulo the fourth term. -/
theorem third_layer_mod_fourth_nontrivial [Finite P] (hP : IsPGroup 3 P)
    (hn : (⊤ : Subgroup P).lowerCentralSeries 2 ≠ ⊥) :
    ((⊤ : Subgroup P).lowerCentralSeries 2).map
      (QuotientGroup.mk' ((⊤ : Subgroup P).lowerCentralSeries 3)) ≠ ⊥ := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let := hP.isNilpotent
  have hlt := lowerCentralSeries_strict_of_ne_bot hn
  intro he
  have hle : (⊤ : Subgroup P).lowerCentralSeries 2 ≤
      (⊤ : Subgroup P).lowerCentralSeries 3 := by
    intro x hx
    apply (QuotientGroup.eq_one_iff _).mp
    exact mem_bot.mp (he ▸ mem_map_of_mem _ hx)
  exact hlt.not_ge hle

/-- Killing the fourth term and retaining a cubic third term gives exact class three. -/
theorem quotient_has_class_three [Finite P] (N : Subgroup P) [N.Normal]
    (hfour : (⊤ : Subgroup P).lowerCentralSeries 3 ≤ N)
    (hcard : Nat.card (((⊤ : Subgroup P).lowerCentralSeries 2).map (QuotientGroup.mk' N)) = 3) :
    Group.nilpotencyClass (P ⧸ N) = 3 := by
  have hmap (n : ℕ) : ((⊤ : Subgroup P).lowerCentralSeries n).map (QuotientGroup.mk' N) =
      (⊤ : Subgroup (P ⧸ N)).lowerCentralSeries n := by
    rw [map_lowerCentralSeries, map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  have h3 : (⊤ : Subgroup (P ⧸ N)).lowerCentralSeries 3 = ⊥ := by
    rw [← hmap]
    apply eq_bot_iff.mpr
    rintro _ ⟨x, hx, rfl⟩
    exact mem_bot.mpr ((QuotientGroup.eq_one_iff _).mpr (hfour hx))
  have h2 : (⊤ : Subgroup (P ⧸ N)).lowerCentralSeries 2 ≠ ⊥ := by
    intro he
    rw [hmap 2, he] at hcard
    have hc : Nat.card (⊥ : Subgroup (P ⧸ N)) = 1 := card_eq_one.mpr rfl
    omega
  let : Group.IsNilpotent (P ⧸ N) := Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨3, h3⟩
  have hle := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp h3
  have hgt : ¬ Group.nilpotencyClass (P ⧸ N) ≤ 2 :=
    fun h => h2 (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr h)
  omega


/-- The surviving third term is central in the literal fourth-term quotient. -/
theorem third_layer_mod_fourth_le_center :
    ((⊤ : Subgroup P).lowerCentralSeries 2).map
      (QuotientGroup.mk' ((⊤ : Subgroup P).lowerCentralSeries 3)) ≤
      center (P ⧸ (⊤ : Subgroup P).lowerCentralSeries 3) := by
  let W := (⊤ : Subgroup P).lowerCentralSeries 3
  let q := QuotientGroup.mk' W
  apply commutator_top_right_eq_bot_iff_le_center.mp
  rw [← map_top_of_surjective q (QuotientGroup.mk'_surjective W), ← map_commutator]
  change W.map q = ⊥
  exact QuotientGroup.map_mk'_self W

end MarkedCubicClassTwo
