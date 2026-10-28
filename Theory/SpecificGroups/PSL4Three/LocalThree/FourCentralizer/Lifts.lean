module

public import Theory.SpecificGroups.PSL4Three.LocalThree.Trace
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer.ProjectiveTransfer
public import Theory.ElementaryAbelian.Basic

/-!
# Four-group lifts and the full central quotient

Choose two distinct nonidentity elements in an elementary four-group. Their
lifts and their product have trace zero. Projective commutation means literal
commutation or anticommutation, since the scalar kernel is {I,-I}.
The central-quotient counting theorem retains both scalar commutator rows:
the full projective pair-centralizer order divides four times the ordinary
pair-centralizer order.

Source application: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4,
repeated as Theorem 0.1.1(4), printed p.482 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Matrix Subgroup
open scoped commutatorElement IsMulCommutative
namespace Matrix.PSL4Three.LocalThree.FourCentralizer

/-- The defining projection has precisely the center as its kernel. -/
theorem project_ker : project.ker = center SL := by
  ext g
  exact project_eq_one_iff g

/-- All scalar commutators are retained in the projective centralizer bound. -/
theorem project_centralizer_pair_card_dvd (a b : SL) :
    Nat.card (centralizer ({project a, project b} : Set P)) ∣
      4 * Nat.card (centralizer ({a, b} : Set SL)) := by
  have h := Subgroup.centralizer_pair_card_dvd_of_central_kernel
    project project_surjective (by rw [project_ker]) a b
  simpa only [project_ker, card_center, show (2 : ℕ) ^ 2 = 4 from rfl] using h

/-- An ordinary lift-pair bound controls the full projective centralizer. -/
theorem centralizer_not_nine_dvd_of_lift_pair (A : Subgroup P)
    (a b : SL) (ha : project a ∈ A) (hb : project b ∈ A)
    (h : ¬ 3 ^ 2 ∣ Nat.card (centralizer ({a, b} : Set SL))) :
    ¬ 3 ^ 2 ∣ Nat.card (centralizer (A : Set P)) := by
  intro hdiv
  have hle : centralizer (A : Set P) ≤
      centralizer ({project a, project b} : Set P) := by
    apply centralizer_le
    intro x hx
    rcases hx with rfl | hx
    · exact ha
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact hb
  have hh := hdiv.trans ((card_dvd_of_le hle).trans
    (project_centralizer_pair_card_dvd a b))
  exact h ((show Nat.Coprime (3 ^ 2) 4 from by decide).dvd_mul_left.mp hh)

/-- The two possible scalar commutators give literal commutation or anticommutation. -/
theorem commute_or_anticommute (a b : SL)
    (hab : Commute (project a) (project b)) :
    Commute a b ∨ (a : Mat) * (b : Mat) = -((b : Mat) * (a : Mat)) := by
  have hz : ⁅a, b⁆ ∈ center SL := (project_eq_one_iff _).mp (by
    rw [map_commutatorElement]
    exact hab.commutator_eq)
  obtain ⟨c, hc, he⟩ := SpecialLinearGroup.mem_center_iff.mp hz
  have hcs : c = 1 ∨ c = -1 :=
    (by decide : ∀ c : ZMod 3, c ^ 4 = 1 → c = 1 ∨ c = -1) c hc
  rcases hcs with rfl | rfl
  · left
    apply commutatorElement_eq_one_iff_commute.mp
    apply Subtype.ext
    change ((⁅a, b⁆ : SL) : Mat) = 1
    simpa only [map_one] using he.symm
  · right
    have hprod : a * b = ⁅a, b⁆ * (b * a) := by
      simp only [commutatorElement_def]
      group
    have h := congrArg (fun g : SL => (g : Mat)) hprod
    change (a : Mat) * (b : Mat) = ((⁅a, b⁆ : SL) : Mat) * ((b : Mat) * (a : Mat)) at h
    rw [← he] at h
    simpa only [map_neg, map_one, neg_mul, one_mul] using h

private theorem exists_distinct_nonidentity (A : Subgroup P) (hA : Nat.card A = 4) :
    ∃ x ∈ A, ∃ y ∈ A, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  classical
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hx⟩ := exists_ne (1 : A)
  obtain ⟨y, hy1, hyx⟩ : ∃ y : A, y ≠ 1 ∧ y ≠ x := by
    by_contra hn
    have hall : (Set.univ : Set A) ⊆ {1, x} := by
      intro y _
      by_cases hy : y = 1
      · exact Or.inl hy
      · exact Or.inr (Classical.byContradiction fun hyx => hn ⟨y, hy, hyx⟩)
    have hh := Set.ncard_mono hall
    rw [Set.ncard_univ, Set.ncard_pair (Ne.symm hx), hA] at hh
    omega
  exact ⟨x, x.property, y, y.property,
    fun h => hx (Subtype.ext h), fun h => hy1 (Subtype.ext h),
    fun h => hyx (Subtype.ext h.symm)⟩

/-- Reduction to two ordinary matrix centralizer calculations. The trace input
is discharged by the projective involution trace theorem. -/
theorem four_centralizer_not_nine_dvd_of_lift_bounds
    (hcommuting : ∀ a b : SL, (project a) ^ 2 = 1 → (project b) ^ 2 = 1 →
      Commute a b → trace (a : Mat) = 0 → trace (b : Mat) = 0 →
      trace ((a * b : SL) : Mat) = 0 →
      ¬ 3 ^ 2 ∣ Nat.card (centralizer ({a, b} : Set SL)))
    (hanticommuting : ∀ a b : SL, (project a) ^ 2 = 1 → (project b) ^ 2 = 1 →
      (a : Mat) * (b : Mat) = -((b : Mat) * (a : Mat)) →
      ¬ 3 ^ 2 ∣ Nat.card (centralizer ({a, b} : Set SL)))
    (A : Subgroup P) (hEA : IsElementaryAbelian 2 A) (hA : Nat.card A = 4) :
    ¬ 3 ^ 2 ∣ Nat.card (centralizer (A : Set P)) := by
  classical
  let := hEA
  obtain ⟨x, hx, y, hy, hx1, hy1, hxy⟩ := exists_distinct_nonidentity A hA
  obtain ⟨a, rfl⟩ := project_surjective x
  obtain ⟨b, rfl⟩ := project_surjective y
  have ha2 : (project a) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hx
  have hb2 : (project b) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hy
  have hab : Commute (project a) (project b) :=
    congrArg Subtype.val (mul_comm (⟨project a, hx⟩ : A) (⟨project b, hy⟩ : A))
  apply centralizer_not_nine_dvd_of_lift_pair A a b hx hy
  rcases commute_or_anticommute a b hab with hc | hc
  · apply hcommuting a b ha2 hb2 hc
      (trace_eq_zero_of_projective_involution a hx1 ha2)
      (trace_eq_zero_of_projective_involution b hy1 hb2)
    apply trace_eq_zero_of_projective_involution
    · rw [map_mul]
      intro he
      apply hxy
      calc
        project a = project a * (project b * project b) := by
          rw [← pow_two, hb2, mul_one]
        _ = (project a * project b) * project b := (mul_assoc _ _ _).symm
        _ = project b := by rw [he, one_mul]
    · rw [map_mul, hab.mul_pow, ha2, hb2, one_mul]
  · exact hanticommuting a b ha2 hb2 hc

end Matrix.PSL4Three.LocalThree.FourCentralizer
