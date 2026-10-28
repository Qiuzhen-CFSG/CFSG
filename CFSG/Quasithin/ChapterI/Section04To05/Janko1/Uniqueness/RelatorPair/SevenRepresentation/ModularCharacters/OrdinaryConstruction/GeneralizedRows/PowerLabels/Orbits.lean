module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.GeneralizedRows.PowerLabels.Action

/-!
# Prime and mixed-order power orbits

The two classes of order five are exchanged by squaring. On the three classes
of order nineteen, squaring is injective and has no fixed point, hence is one
of the two three-cycles. Squaring order-ten elements and cubing order-fifteen
elements separate their two classes: a suitable coprime power exchanges the
two fifth-order images. These facts orient the literal ordinary power table.

Source: the conjugacy-class stage of Janko, J. Algebra 3 (1966), 147–186,
as described by Gorenstein, printed p.482. The argument uses only the supplied
class census and group order; it introduces no character assumptions.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
namespace PowerLabelConstruction
variable {G : Type*} [Group G] [Finite G] (c : OrdinaryClassData G)

public theorem order_five_iff (j : Fin 15) : classOrder j = 5 ↔ j = 3 ∨ j = 4 := by
  revert j; decide +kernel

public theorem order_nineteen_iff (j : Fin 15) :
    classOrder j = 19 ↔ j = 12 ∨ j = 13 ∨ j = 14 := by
  revert j; decide +kernel

public theorem square_five (horder : Nat.card G = 175560) :
    power c 3 2 = 4 ∧ power c 4 2 = 3 := by
  have h3 := power_order c 3 2
  have h4 := power_order c 4 2
  change classOrder (power c 3 2) = 5 at h3
  change classOrder (power c 4 2) = 5 at h4
  rw [order_five_iff] at h3 h4
  have hn3 := square_ne c horder 3 (Or.inl rfl)
  have hn4 := square_ne c horder 4 (Or.inl rfl)
  exact ⟨h3.resolve_left hn3, h4.resolve_right hn4⟩

private theorem square_injective_nineteen {i j : Fin 15}
    (hi : classOrder i = 19) (hj : classOrder j = 19)
    (he : power c i 2 = power c j 2) : i = j := by
  have he' := congrArg (fun k => power c k 10) he
  rw [power_mul, power_mul, ← power_mod c i 20, ← power_mod c j 20, hi, hj] at he'
  simpa using he'

public theorem square_nineteen (horder : Nat.card G = 175560) :
    (power c 12 2 = 13 ∧ power c 13 2 = 14 ∧ power c 14 2 = 12) ∨
    (power c 12 2 = 14 ∧ power c 14 2 = 13 ∧ power c 13 2 = 12) := by
  have h12 := power_order c 12 2
  have h13 := power_order c 13 2
  have h14 := power_order c 14 2
  change classOrder (power c 12 2) = 19 at h12
  change classOrder (power c 13 2) = 19 at h13
  change classOrder (power c 14 2) = 19 at h14
  rw [order_nineteen_iff] at h12 h13 h14
  have hn12 := square_ne c horder 12 (Or.inr rfl)
  have hn13 := square_ne c horder 13 (Or.inr rfl)
  have hn14 := square_ne c horder 14 (Or.inr rfl)
  rcases h12 with h12 | h12 | h12 <;>
    rcases h13 with h13 | h13 | h13 <;>
    rcases h14 with h14 | h14 | h14 <;> try contradiction
  all_goals first
    | exact Or.inl ⟨h12, h13, h14⟩
    | exact Or.inr ⟨h12, h14, h13⟩
    | have he : (12 : Fin 15) = 13 := square_injective_nineteen c rfl rfl (h12.trans h13.symm)
      exact absurd he (by decide)
    | have he : (12 : Fin 15) = 14 := square_injective_nineteen c rfl rfl (h12.trans h14.symm)
      exact absurd he (by decide)
    | have he : (13 : Fin 15) = 14 := square_injective_nineteen c rfl rfl (h13.trans h14.symm)
      exact absurd he (by decide)

public theorem power_five (hfive : power c 3 2 = 4 ∧ power c 4 2 = 3)
    (j : Fin 15) (hj : classOrder j = 5) (n : ℕ) :
    power c j n = ordinaryPowerClass j n := by
  have h34 : power c 3 4 = 3 := by
    simpa [hfive.1, hfive.2] using (power_mul c 3 2 2).symm
  have h44 : power c 4 4 = 4 := by
    simpa [hfive.1, hfive.2] using (power_mul c 4 2 2).symm
  have h33 : power c 3 3 = 4 := by
    have he := (power_mul c 3 4 2).symm
    rw [← power_mod c 3 8] at he
    simpa [classOrder, h34, hfive.1] using he
  have h43 : power c 4 3 = 3 := by
    have he := (power_mul c 4 4 2).symm
    rw [← power_mod c 4 8] at he
    simpa [classOrder, h44, hfive.2] using he
  rw [← power_mod c j n]
  unfold ordinaryPowerClass
  have hm : n % classOrder j < 5 := by
    rw [hj]; exact Nat.mod_lt n (by decide)
  generalize n % classOrder j = r at *
  rcases (order_five_iff j).mp hj with rfl | rfl <;>
    interval_cases r <;>
    simp [ordinaryPowerCycle, hfive.1, hfive.2, h34, h44, h33, h43]

private theorem order_ten_iff (j : Fin 15) : classOrder j = 10 ↔ j = 7 ∨ j = 8 := by
  revert j; decide +kernel

private theorem order_fifteen_iff (j : Fin 15) : classOrder j = 15 ↔ j = 10 ∨ j = 11 := by
  revert j; decide +kernel

public theorem mixed_ten (hfive : power c 3 2 = 4 ∧ power c 4 2 = 3) :
    (power c 7 2 = 3 ∧ power c 8 2 = 4) ∨
    (power c 7 2 = 4 ∧ power c 8 2 = 3) := by
  have h7 : classOrder (power c 7 2) = 5 := power_order c 7 2
  have h73 : classOrder (power c 7 3) = 10 := power_order c 7 3
  have hc : power c (power c 7 3) 2 = power c (power c 7 2) 3 := by
    rw [power_mul, power_mul]
  have h33 : power c 3 3 = 4 := power_five c hfive 3 rfl 3
  have h43 : power c 4 3 = 3 := power_five c hfive 4 rfl 3
  rcases (order_five_iff _).mp h7 with h7 | h7 <;>
    rcases (order_ten_iff _).mp h73 with h73 | h73
  · rw [h73, h7, h33] at hc; exact absurd hc (by decide)
  · exact Or.inl ⟨h7, by simpa only [h73, h7, h33] using hc⟩
  · rw [h73, h7, h43] at hc; exact absurd hc (by decide)
  · exact Or.inr ⟨h7, by simpa only [h73, h7, h43] using hc⟩

public theorem mixed_fifteen (hfive : power c 3 2 = 4 ∧ power c 4 2 = 3) :
    (power c 10 3 = 3 ∧ power c 11 3 = 4) ∨
    (power c 10 3 = 4 ∧ power c 11 3 = 3) := by
  have h10 : classOrder (power c 10 3) = 5 := power_order c 10 3
  have h102 : classOrder (power c 10 2) = 15 := power_order c 10 2
  have hc : power c (power c 10 2) 3 = power c (power c 10 3) 2 := by
    rw [power_mul, power_mul]
  rcases (order_five_iff _).mp h10 with h10 | h10 <;>
    rcases (order_fifteen_iff _).mp h102 with h102 | h102
  · rw [h102, h10, hfive.1] at hc; exact absurd hc (by decide)
  · exact Or.inl ⟨h10, by simpa only [h102, h10, hfive.1] using hc⟩
  · rw [h102, h10, hfive.2] at hc; exact absurd hc (by decide)
  · exact Or.inr ⟨h10, by simpa only [h102, h10, hfive.2] using hc⟩

end PowerLabelConstruction
end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
