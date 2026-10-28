module
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic

/-!
# A fixed point with orbit order prime to three on four points

For any group action on a four-element type, a supplied fixed point of t
can be replaced by a t-fixed point whose full group orbit has order coprime
to three. The acting group need not be finite, and no order condition on t,
faithfulness, transitivity, or exact count of fixed points is assumed.

If the supplied point's orbit has order other than three, its positive
order is one, two, or four. Otherwise its complement is a singleton. Every
group element preserves that complement, so its unique point is globally
fixed and has orbit order one.

This elementary orbit argument supplies the point in the actual affine
four-element coset in Stellmacher (10.1), source (16), printed p.64.
The application retains its own conjugation action and affine fiber.
-/

namespace MulAction

public theorem exists_fixed_point_three_coprime_orbit_of_card_four
    {K X : Type*} [Group K] [MulAction K X] [Finite X]
    (hfour : Nat.card X=4) (t : K) (x : X) (htx : t • x=x) :
    ∃ y : X, t • y=y ∧ Nat.Coprime 3 (Nat.card (orbit K y)) := by
  classical
  simp only [Nat.card_coe_set_eq]
  by_cases hthree : (orbit K x).ncard=3
  · have hc : (orbit K x)ᶜ.ncard=1 := by
      rw [Set.ncard_compl,hfour,hthree]
    obtain ⟨y,hy⟩ := Set.ncard_eq_one.mp hc
    have hyout : y∉orbit K x := by
      have hh : y∈(orbit K x)ᶜ := by rw [hy]; exact Set.mem_singleton y
      exact hh
    have hfixed (g : K) : g • y=y := by
      have hout : g • y∈(orbit K x)ᶜ := by
        rintro ⟨k,hk⟩
        apply hyout
        refine ⟨g⁻¹*k,?_⟩
        change (g⁻¹*k) • x=y
        change k • x=g • y at hk
        rw [mul_smul,hk,inv_smul_smul]
      rw [hy] at hout
      exact Set.mem_singleton_iff.mp hout
    have horbit : orbit K y={y} := by
      ext z
      constructor
      · rintro ⟨g,rfl⟩
        exact Set.mem_singleton_iff.mpr (hfixed g)
      · intro hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact mem_orbit_self y
    refine ⟨y,hfixed t,?_⟩
    rw [horbit,Set.ncard_singleton]
    decide
  · refine ⟨x,htx,?_⟩
    have hpos : 0<(orbit K x).ncard := (Set.ncard_pos).mpr ⟨x,mem_orbit_self x⟩
    have hbound : (orbit K x).ncard≤4 := hfour ▸ Set.ncard_le_card _
    have hcases : (orbit K x).ncard=1 ∨ (orbit K x).ncard=2 ∨ (orbit K x).ncard=4 := by omega
    rcases hcases with h | h | h <;> rw [h] <;> decide

end MulAction
