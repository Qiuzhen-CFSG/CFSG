module

public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.PGroup.Omega

/-!
# Restricting characteristic subgroups to the center

A nontrivial normal subgroup of a finite p-group meets the center nontrivially.
Consequently, if B is characteristic in P and D is a nontrivial characteristic
subgroup of B of exponent dividing p, then Z(P) ∩ D is a nontrivial
characteristic subgroup contained in Ω₁(Z(P)). The nontriviality follows from
the fixed-point theorem for the conjugation action; the omega containment
follows by inserting each central element into the defining generators.

This is the subgroup construction used in Aschbacher–Smith, *The Classification
of Quasithin Groups*, combined manuscript (1 March 2004), Remark C.1.19.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- A nontrivial normal subgroup of a finite p-group meets its center. -/
theorem center_inf_ne_bot_of_normal [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p G) (D : Subgroup G) [D.Normal] (hne : D ≠ ⊥) :
    center G ⊓ D ≠ ⊥ := by
  let : Fact (IsPGroup p G) := ⟨hp⟩
  let : Nontrivial D := (nontrivial_iff_ne_bot D).mpr hne
  obtain ⟨x, hx, hz⟩ := exists_nontrivial_center_mem_normal (p := p) D
  intro h
  have hx1 : (x : G) = 1 := by
    have hm : (x : G) ∈ center G ⊓ D := ⟨hz, x.property⟩
    rwa [h, mem_bot] at hm
  exact hx (Subtype.ext hx1)

/-- A central intersection of exponent dividing p lies in the first omega center. -/
theorem center_inf_le_omega_center {p : ℕ} (D : Subgroup G)
    (hp : ∀ x ∈ D, x ^ p = 1) :
    center G ⊓ D ≤ (omega₁ (center G) (p := p)).map (center G).subtype := by
  rintro x ⟨hz, hd⟩
  refine ⟨⟨x, hz⟩, subset_closure ?_, rfl⟩
  change (⟨x, hz⟩ : center G) ^ (p ^ 1) = 1
  apply Subtype.ext
  simpa using hp x hd

/-- Restrict a characteristic subgroup of a characteristic subgroup to the
ambient center, retaining characteristicity, nontriviality and its exponent bound. -/
theorem characteristic_center_reduction [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p G) (B : Subgroup G) [B.Characteristic]
    (D : Subgroup B) [D.Characteristic] (hne : D ≠ ⊥)
    (hexp : ∀ x ∈ D, x ^ p = 1) :
    (center G ⊓ D.map B.subtype).Characteristic ∧
      center G ⊓ D.map B.subtype ≠ ⊥ ∧
      center G ⊓ D.map B.subtype ≤
        (omega₁ (center G) (p := p)).map (center G).subtype := by
  refine ⟨inferInstance, center_inf_ne_bot_of_normal hp _ ?_,
    center_inf_le_omega_center _ ?_⟩
  · exact fun h => hne ((D.map_eq_bot_iff_of_injective B.subtype_injective).mp h)
  · rintro x ⟨y, hy, rfl⟩
    exact congrArg B.subtype (hexp y hy)

end Subgroup
