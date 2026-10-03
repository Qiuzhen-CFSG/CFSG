module

public import Theory.GroupAction.SylowCentralizer

/-!
# Counting criterion for transitivity of a Sylow subgroup

Centralizer containment makes every orbit away from the chosen Sylow subgroup
have its full order. Consequently an upper bound of `|P| + 1` on the number
of Sylow subgroups forces each such orbit to exhaust the complement.

This is the final counting-to-action step in Suzuki, *Finite groups with
nilpotent centralizers* (1961), Part I, Theorem 2, printed p. 432.
-/

namespace Sylow

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- The sharp upper bound on the number of Sylows implies root transitivity. -/
public theorem transitive_of_centralizer_le_of_card_le (P : Sylow p G)
    (hcent : ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ≤ (P : Subgroup G))
    (hcard : Nat.card (Sylow p G) ≤ Nat.card P + 1) :
    ∀ Q R : Sylow p G, Q ≠ P → R ≠ P → ∃ x : P, (x : G) • Q = R := by
  classical
  intro Q R hQ hR
  let X := {S : Sylow p G // S ≠ P}
  have hne (x : P) : (x : G) • Q ≠ P := by
    intro he
    have hxP : (x : G) • P = P :=
      Sylow.smul_eq_iff_mem_normalizer.mpr ((P : Subgroup G).le_normalizer x.property)
    exact hQ (smul_left_cancel (x : G) (he.trans hxP.symm))
  let f : P → X := fun x => ⟨(x : G) • Q, hne x⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have hxy' : (x : G) • Q = (y : G) • Q := congrArg Subtype.val hxy
    have he : y⁻¹ * x = 1 := P.eq_one_of_smul_eq_of_centralizer_le Q hcent hQ
      (y⁻¹ * x) (by
        change ((y : G)⁻¹ * (x : G)) • Q = Q
        rw [mul_smul, hxy', inv_smul_smul])
    exact (inv_mul_eq_one.mp he).symm
  have hX : Nat.card X < Nat.card (Sylow p G) := by
    let := Fintype.ofFinite (Sylow p G)
    let := Fintype.ofFinite X
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_subtype_lt (p := fun S : Sylow p G => S ≠ P) (x := P) (by simp))
  have hle : Nat.card X ≤ Nat.card ↥P := by
    change Nat.card (Sylow p G) ≤ Nat.card ↥P + 1 at hcard
    omega
  obtain ⟨x, hx⟩ := (hinj.bijective_of_nat_card_le hle).surjective ⟨R, hR⟩
  exact ⟨x, congrArg Subtype.val hx⟩

end Sylow
