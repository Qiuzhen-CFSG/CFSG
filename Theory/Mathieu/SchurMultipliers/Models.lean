module

public import Theory.GroupTheory.Covering
public import Theory.Mathieu.M12.Properties.Simplicity
public import Theory.Mathieu.M24.Properties.Simplicity

/-!
# Quasisimplicity of the native Mathieu models

The certified orders are composite, so each proved simple Mathieu group is
nonabelian and perfect. Its center is trivial, and its central quotient is
simple. These instances let the multiplier calculations use the literal
finite quasisimple covering interface, without extra model hypotheses.

Source: the Mathieu simple groups in Aschbacher–Smith A.2.2–A.2.3 and
I.1.3, with the concrete order and simplicity proofs imported above.
-/

open Subgroup Theory.GroupTheory

namespace Sporadic.Mathieu.SchurMultipliers

private theorem quasisimple_of_simple_composite {S : Type*} [Group S]
    (hs : IsSimpleGroup S) (hc : ¬ (Nat.card S).Prime) : IsQuasisimple S := by
  let := hs
  have hn : ¬ IsMulCommutative S := by
    intro ha
    let := ha
    exact hc (Group.is_simple_iff_prime_card.mp hs)
  let : Group.IsPerfect S := ⟨by
    rcases (inferInstance : (commutator S).Normal).eq_bot_or_eq_top with h | h
    · exact (hn ((commutator_eq_bot_iff S).mp h)).elim
    · exact h⟩
  have hz : center S = ⊥ := by
    rcases (inferInstance : (center S).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (hn (center_eq_top_iff.mp h)).elim
  exact { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup }

/-- Quasisimplicity of the actual eleven-point Mathieu model. -/
public instance m11Quasisimple : IsQuasisimple M11 :=
  quasisimple_of_simple_composite m11_isSimpleGroup (by rw [m11_order]; norm_num)

/-- Quasisimplicity of the actual twelve-point Mathieu model. -/
public instance m12Quasisimple : IsQuasisimple M12 :=
  quasisimple_of_simple_composite m12_isSimpleGroup (by rw [m12_order]; norm_num)

/-- Quasisimplicity of the actual twenty-three-point Mathieu model. -/
public instance m23Quasisimple : IsQuasisimple M23 :=
  quasisimple_of_simple_composite m23_isSimpleGroup (by rw [m23_order]; norm_num)

/-- Quasisimplicity of the actual twenty-four-point Mathieu model. -/
public instance m24Quasisimple : IsQuasisimple M24 :=
  quasisimple_of_simple_composite m24_isSimpleGroup (by rw [m24_order]; norm_num)

end Sporadic.Mathieu.SchurMultipliers
