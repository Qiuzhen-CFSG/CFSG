module

public import Theory.SpecificGroups.LeechRelated.HSRecognition.RankThreeData
public import Theory.GroupAction.ThreeSuborbits

/-!
# Subdegrees and primitivity for the rank-three HS recognition problem

The given rank-three quotient and the 22-point suborbit force the other
nontrivial suborbit to have length 77. A block through the base point is a
union of these orbits, so its size is 1, 23, 78 or 100. Divisibility by the
degree rules out the two intermediate sizes and proves primitivity.

This supplies the preliminary hypotheses for Wales, "Uniqueness of the
graph of a rank three group", Pacific J. Math. 30 (1969), pp.271--274.
It concerns the arbitrary permutation group in `RankThreeData`, with no
simplicity or identification with either concrete HS model assumed.
-/

public section
open MulAction
namespace Sporadic.LeechRelated.HS

private theorem orbit_base (P : Subgroup (Equiv.Perm (Fin 100))) :
    orbit (stabilizer P (0 : Fin 100)) (0 : Fin 100) = {0} := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact g.property
  · rintro rfl
    exact mem_orbit_self _

private theorem third_orbit {P : Subgroup (Equiv.Perm (Fin 100))}
    (h : RankThreeData P) (b : Fin 100)
    (hb : (0 : Fin 100) ∉ orbit (stabilizer P (0 : Fin 100)) b) :
    ∃ c : Fin 100, orbit (stabilizer P (0 : Fin 100)) c =
      (({0} : Set (Fin 100)) ∪ orbit (stabilizer P (0 : Fin 100)) b)ᶜ := by
  classical
  let K := stabilizer P (0 : Fin 100)
  let Q := orbitRel.Quotient K (Fin 100)
  let : Fintype Q := Fintype.ofFinite _
  let q : Fin 100 → Q := Quotient.mk''
  have hq {x y : Fin 100} : q x = q y ↔ x ∈ orbit K y := Quotient.eq''
  have h0b : q 0 ≠ q b := fun he => hb (hq.mp he)
  let T : Finset Q := {q 0, q b}
  have hTc : T.card = 2 := by simp [T, h0b]
  have hQc : Fintype.card Q = 3 := (Nat.card_eq_fintype_card.symm).trans h.rank_three
  have hcomp : Tᶜ.card = 1 := by rw [Finset.card_compl, hQc, hTc]
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hcomp
  have hqr (s : Q) : s = r ↔ s ≠ q 0 ∧ s ≠ q b := by
    have hh : s ∈ Tᶜ ↔ s = r := by rw [hr]; simp
    simpa [T, not_or] using hh.symm
  obtain ⟨c, hc⟩ := Quotient.exists_rep r
  refine ⟨c, ?_⟩
  ext x
  rw [← hq, show q c = r from hc, hqr]
  have hbase : q x = q 0 ↔ x = 0 := by
    rw [hq, orbit_base P]
    rfl
  change (q x ≠ q 0 ∧ q x ≠ q b) ↔ ¬(x = 0 ∨ x ∈ orbit K b)
  rw [not_or]
  exact and_congr (not_congr hbase) (not_congr hq)

/-- The complement of the fixed point and a 22-point suborbit is a 77-point suborbit. -/
theorem RankThreeData.complementary_suborbit {P : Subgroup (Equiv.Perm (Fin 100))} (h : RankThreeData P)
    (b : Fin 100) (hb : Nat.card (orbit (stabilizer P (0 : Fin 100)) b) = 22) :
    ∃ c : Fin 100, orbit (stabilizer P (0 : Fin 100)) c =
      (({0} : Set (Fin 100)) ∪ orbit (stabilizer P (0 : Fin 100)) b)ᶜ ∧
      Nat.card (orbit (stabilizer P (0 : Fin 100)) c) = 77 := by
  have h0b : (0 : Fin 100) ∉ orbit (stabilizer P (0 : Fin 100)) b := by
    intro hh
    have he := orbit_eq_iff.mpr hh
    rw [← he, orbit_base] at hb
    simp at hb
  obtain ⟨c, hc⟩ := third_orbit h b h0b
  refine ⟨c, hc, ?_⟩
  rw [hc]
  change ((({0} : Set (Fin 100)) ∪ orbit (stabilizer P (0 : Fin 100)) b)ᶜ).ncard = 77
  rw [Set.ncard_compl, Set.ncard_union_eq (Set.disjoint_singleton_left.mpr h0b)]
  simp only [Nat.card_fin, Set.ncard_singleton]
  change 100 - (1 + Nat.card (orbit (stabilizer P (0 : Fin 100)) b)) = 77
  omega

/-- Actual representatives of all three stabilizer orbits. -/
theorem RankThreeData.suborbits {P : Subgroup (Equiv.Perm (Fin 100))}
    (h : RankThreeData P) :
    ∃ b c : Fin 100,
      (0 : Fin 100) ∉ orbit (stabilizer P (0 : Fin 100)) b ∧
      Nat.card (orbit (stabilizer P (0 : Fin 100)) b) = 22 ∧
      Nat.card (orbit (stabilizer P (0 : Fin 100)) c) = 77 ∧
      orbit (stabilizer P (0 : Fin 100)) c =
        (({0} : Set (Fin 100)) ∪ orbit (stabilizer P (0 : Fin 100)) b)ᶜ := by
  obtain ⟨b, hb⟩ := h.subdegree_twenty_two
  obtain ⟨c, hc, hcard⟩ := h.complementary_suborbit b hb
  refine ⟨b, c, ?_, hb, hcard, hc⟩
  intro hh
  have he := orbit_eq_iff.mpr hh
  rw [← he, orbit_base] at hb
  simp at hb

/-- The exact list of possible subdegrees. -/
theorem RankThreeData.subdegree_cases {P : Subgroup (Equiv.Perm (Fin 100))}
    (h : RankThreeData P) (x : Fin 100) :
    Nat.card (orbit (stabilizer P (0 : Fin 100)) x) = 1 ∨
    Nat.card (orbit (stabilizer P (0 : Fin 100)) x) = 22 ∨
    Nat.card (orbit (stabilizer P (0 : Fin 100)) x) = 77 := by
  obtain ⟨b, c, _, hb, hc, hcover⟩ := h.suborbits
  by_cases hx : x = 0
  · subst x
    left
    rw [orbit_base]
    simp
  by_cases hxb : x ∈ orbit (stabilizer P (0 : Fin 100)) b
  · exact Or.inr (Or.inl ((Nat.card_congr (Equiv.setCongr (orbit_eq_iff.mpr hxb))).trans hb))
  · have hxc : x ∈ orbit (stabilizer P (0 : Fin 100)) c := by
      rw [hcover]
      exact fun hh => hh.elim hx hxb
    exact Or.inr (Or.inr ((Nat.card_congr (Equiv.setCongr (orbit_eq_iff.mpr hxc))).trans hc))

/-- Distinct stabilizer orbits have distinct lengths. -/
theorem RankThreeData.suborbit_eq_of_card_eq {P : Subgroup (Equiv.Perm (Fin 100))}
    (h : RankThreeData P) {x y : Fin 100}
    (hxy : Nat.card (orbit (stabilizer P (0 : Fin 100)) x) =
      Nat.card (orbit (stabilizer P (0 : Fin 100)) y)) :
    orbit (stabilizer P (0 : Fin 100)) x = orbit (stabilizer P (0 : Fin 100)) y := by
  obtain ⟨b, c, _, hb, hc, hcover⟩ := h.suborbits
  have hcases (z : Fin 100) :
      orbit (stabilizer P (0 : Fin 100)) z = {0} ∨
      orbit (stabilizer P (0 : Fin 100)) z = orbit (stabilizer P (0 : Fin 100)) b ∨
      orbit (stabilizer P (0 : Fin 100)) z = orbit (stabilizer P (0 : Fin 100)) c := by
    by_cases hz : z = 0
    · exact Or.inl (hz ▸ orbit_base P)
    by_cases hzb : z ∈ orbit (stabilizer P (0 : Fin 100)) b
    · exact Or.inr (Or.inl (orbit_eq_iff.mpr hzb))
    · right; right
      apply orbit_eq_iff.mpr
      rw [hcover]
      exact fun hh => hh.elim hz hzb
  rcases hcases x with hx | hx | hx <;> rcases hcases y with hy | hy | hy
  all_goals first
    | exact hx.trans hy.symm
    | exfalso; rw [hx, hy] at hxy; simp only [Nat.card_unique, hb, hc] at hxy; omega

/-- The intrinsic rank-three data already imply primitivity. -/
theorem RankThreeData.primitive {P : Subgroup (Equiv.Perm (Fin 100))}
    (h : RankThreeData P) : IsPreprimitive P (Fin 100) := by
  let := h.transitive
  obtain ⟨b, c, h0b, hb, hc, hcover⟩ := h.suborbits
  let d : Fin 3 → ℕ := ![1, 22, 77]
  apply Atlas.GroupTheory.primitive_of_rankThree_nondivisibility (0 : Fin 100)
    (ThreeSuborbits.family (K := stabilizer P (0 : Fin 100)) 0 b)
    ((ThreeSuborbits.family_zero 0 b 0).mpr rfl)
    (fun _ _ hh => ThreeSuborbits.transitive 0 b c h0b hcover hh) d rfl
  · intro i
    simpa only [hb, hc] using ThreeSuborbits.fiber_card 0 b c h0b hcover i
  · exact Nat.card_fin 100
  · rw [Nat.card_fin]
    change ¬23 ∣ 100
    decide
  · rw [Nat.card_fin]
    change ¬78 ∣ 100
    decide
end Sporadic.LeechRelated.HS
