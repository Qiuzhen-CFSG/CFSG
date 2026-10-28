module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer.Lifts
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer.Commuting
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer.Anticommuting
public import Theory.ElementaryAbelian.Basic

/-!
# Four-group centralizers in the field-nine projective unitary model

Choose two distinct nonidentity elements of an elementary four-group and lift
them to the actual SU₄ over Nine. The projective-involution trace premise gives
trace zero for both lifts and their product. Their scalar commutator is 1 or
-1. The central-extension counting theorem then reduces exclusion of nine in
the full projective centralizer to the ordinary SU centralizer in these two
cases. All scalar commutators in the projective centralizer are included.

The commuting calculation uses the four joint character lines; the anticommuting
calculation embeds the common centralizer into a full unitary plane group of
order 96. The final theorem discharges both ordinary-centralizer bounds, leaving
only the projective-involution trace premise. Its independent proof belongs to
the parent assembly of the defining-prime rank bound.

Source obligation: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4, repeated as
Theorem 0.1.1(4), printed p.482 of `refs/quasithin.pdf`. The source conclusion
includes PSU₄(3); the centralizer bound here is a local ingredient for its QT
condition, with the SU-to-PSU convention of GLS3, chapter 2.
-/

public noncomputable section

open Matrix BenderSuzuki.MatrixGroups Subgroup
open scoped commutatorElement IsMulCommutative
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer

/-- The actual scalar kernel contributes a factor dividing sixteen. -/
theorem project_centralizer_pair_card_dvd (a b : SU) :
    Nat.card (centralizer ({project 4 a, project 4 b} : Set (Carrier 4))) ∣
      16 * Nat.card (centralizer ({a, b} : Set SU)) := by
  have hk : Nat.card (project 4).ker = 4 :=
    IsotropicStabilizers.scalarKernel_card (form 4) (form_conj_cube 4)
  have hh := Subgroup.centralizer_pair_card_dvd_of_central_kernel
    (project 4) (project_surjective 4) project_kernel_central a b
  simpa only [hk, show (4 : ℕ) ^ 2 = 16 from rfl] using hh

/-- A bound for an ordinary lift centralizer controls the full projective centralizer. -/
theorem centralizer_not_nine_dvd_of_lift_pair (A : Subgroup (Carrier 4))
    (a b : SU) (ha : project 4 a ∈ A) (hb : project 4 b ∈ A)
    (h : ¬ 3 ^ 2 ∣ Nat.card (centralizer ({a, b} : Set SU))) :
    ¬ 3 ^ 2 ∣ Nat.card (centralizer (A : Set (Carrier 4))) := by
  intro hdiv
  have hle : centralizer (A : Set (Carrier 4)) ≤
      centralizer ({project 4 a, project 4 b} : Set (Carrier 4)) := by
    apply centralizer_le
    intro x hx
    rcases hx with rfl | hx
    · exact ha
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact hb
  have hh := hdiv.trans ((card_dvd_of_le hle).trans
    (project_centralizer_pair_card_dvd a b))
  exact h ((show Nat.Coprime (3 ^ 2) 16 from by decide).dvd_mul_left.mp hh)

private theorem exists_distinct_nonidentity (A : Subgroup (Carrier 4))
    (hA : Nat.card A = 4) :
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

/-- Conditional assembly of the four-group bound from the two matrix calculations.
The commuting and anticommuting ordinary-centralizer bounds remain explicit premises. -/
theorem four_centralizer_not_nine_dvd_of_lift_bounds
    (htrace : ∀ g : SU, project 4 g ≠ 1 → (project 4 g) ^ 2 = 1 →
      Matrix.trace g.val.val = 0)
    (hcommuting : ∀ a b : SU, (project 4 a) ^ 2 = 1 → (project 4 b) ^ 2 = 1 →
      Commute a b → Matrix.trace a.val.val = 0 → Matrix.trace b.val.val = 0 →
      Matrix.trace (a * b).val.val = 0 →
      ¬ 3 ^ 2 ∣ Nat.card (centralizer ({a, b} : Set SU)))
    (hanticommuting : ∀ a b : SU, (project 4 a) ^ 2 = 1 → (project 4 b) ^ 2 = 1 →
      a.val.val * b.val.val = -(b.val.val * a.val.val) →
      ¬ 3 ^ 2 ∣ Nat.card (centralizer ({a, b} : Set SU)))
    (A : Subgroup (Carrier 4)) (hEA : IsElementaryAbelian 2 A)
    (hA : Nat.card A = 4) :
    ¬ 3 ^ 2 ∣ Nat.card (centralizer (A : Set (Carrier 4))) := by
  classical
  let := hEA
  obtain ⟨x, hx, y, hy, hx1, hy1, hxy⟩ := exists_distinct_nonidentity A hA
  obtain ⟨a, rfl⟩ := project_surjective 4 x
  obtain ⟨b, rfl⟩ := project_surjective 4 y
  have ha2 : (project 4 a) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hx
  have hb2 : (project 4 b) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hy
  have hab : Commute (project 4 a) (project 4 b) :=
    congrArg Subtype.val (mul_comm (⟨project 4 a, hx⟩ : A) (⟨project 4 b, hy⟩ : A))
  apply centralizer_not_nine_dvd_of_lift_pair A a b hx hy
  rcases commute_or_anticommute a b ha2 hab with hc | hc
  · apply hcommuting a b ha2 hb2 hc (htrace a hx1 ha2) (htrace b hy1 hb2)
    apply htrace
    · rw [map_mul]
      intro he
      apply hxy
      calc
        project 4 a = project 4 a * (project 4 b * project 4 b) := by
          rw [← pow_two, hb2, mul_one]
        _ = (project 4 a * project 4 b) * project 4 b := (mul_assoc _ _ _).symm
        _ = project 4 b := by rw [he, one_mul]
    · rw [map_mul, hab.mul_pow, ha2, hb2, one_mul]
  · exact hanticommuting a b ha2 hb2 hc

/-- The centralizer of every elementary four-group in the actual PSU₄(3) model
has order indivisible by nine, assuming only the projective-involution trace
identity. Both ordinary lift-centralizer calculations and the full scalar
commutator transfer are discharged here. -/
theorem four_centralizer_not_nine_dvd_of_trace
    (htrace : ∀ g : SU, project 4 g ≠ 1 → (project 4 g) ^ 2 = 1 →
      Matrix.trace g.val.val = 0)
    (A : Subgroup (Carrier 4)) (hEA : IsElementaryAbelian 2 A)
    (hA : Nat.card A = 4) :
    ¬ 3 ^ 2 ∣ Nat.card (centralizer (A : Set (Carrier 4))) :=
  four_centralizer_not_nine_dvd_of_lift_bounds htrace
    commuting_lift_centralizer_not_nine_dvd
    anticommuting_lift_centralizer_not_nine_dvd A hEA hA

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer
