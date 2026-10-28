module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# A normal subgroup with a unique nonidentity fixed point

The fixed points of a normal subgroup are invariant under the whole acting
group. If there is exactly one nonidentity fixed point, every actor fixes it.
If its stabilizer and a subgroup fixing a second point have the same finite
order, the whole group fixes the second point as well.

This elementary action argument supplies the fixed-line step in
Aschbacher–Smith, proof of Lemma 16.4.7, printed p.1187. It requires normality
in the acting group, with no ambient normality or assumed symmetry automorphism.
-/

public section

namespace MulDistribMulAction

variable {H V : Type*} [Group H] [Group V] [MulDistribMulAction H V]

/-- A normal subgroup's unique nonidentity fixed point is fixed by every actor. -/
theorem fixes_unique_nonidentity_fixedPoint (B : Subgroup H) [B.Normal]
    (z : V) (hz : z ≠ 1)
    (hfixed : ∀ v : V, v ∈ MulAction.fixedPoints B V ↔ v = 1 ∨ v = z) :
    ∀ h : H, h • z = z := by
  intro h
  have hzfix : z ∈ MulAction.fixedPoints B V := (hfixed z).mpr (Or.inr rfl)
  have himage := smul_mem_fixedPoints_of_normal h hzfix
  rcases (hfixed (h • z)).mp himage with hbad | hgood
  · have he := congrArg (fun v => h⁻¹ • v) hbad
    exact (hz (by simpa using he)).elim
  · exact hgood

/-- Equal stabilizer orders implement the two marked points' symmetry.
The normal subgroup cannot move the second point in this configuration. -/
theorem fixedPoint_stabilizer_obstruction [Finite H]
    (z r : V) (hz : z ≠ 1) (B : Subgroup H) [B.Normal]
    (hfixed : ∀ v : V, v ∈ MulAction.fixedPoints B V ↔ v = 1 ∨ v = z)
    (K J : Subgroup H) (hK : K = MulAction.stabilizer H z)
    (hJ : J ≤ MulAction.stabilizer H r)
    (hcard : Nat.card K ≤ Nat.card J)
    (hmove : ∃ b : B, b • r ≠ r) : False := by
  have hfix := fixes_unique_nonidentity_fixedPoint B z hz hfixed
  have hKtop : K = ⊤ := by
    rw [hK]
    exact top_unique fun h _ => hfix h
  have hJtop : J = ⊤ :=
    Subgroup.eq_of_le_of_card_ge le_top (by simpa [hKtop] using hcard)
  obtain ⟨b, hb⟩ := hmove
  exact hb (hJ (by rw [hJtop]; trivial))

end MulDistribMulAction
