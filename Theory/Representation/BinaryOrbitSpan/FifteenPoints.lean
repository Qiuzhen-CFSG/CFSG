module

public import Theory.Representation.BinaryOrbitSpan
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Data.Fintype.Card

/-!
# A fifteen-point binary spanning orbit

A twice-transitive orbit containing the nonzero vectors of a plane is the set
of all nonzero vectors, by `orbit_eq_nonzero_of_pair_transitive`. If it has
fifteen points, the whole binary space has sixteen vectors and dimension four.
The subgroup classification producing two-transitivity is separate.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), the final step of B.4.12(2), printed p.97.
-/

@[expose] public section

namespace Representation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Two-transitivity stated directly on the orbit of the original vector. -/
def PairTransitiveOrbit (ρ : Representation (ZMod 2) G V) (v : V) : Prop :=
  ∀ a ∈ Set.range (fun g => ρ g v), ∀ b ∈ Set.range (fun g => ρ g v), a ≠ b →
    ∀ c ∈ Set.range (fun g => ρ g v), ∀ d ∈ Set.range (fun g => ρ g v), c ≠ d →
      ∃ g : G, ρ g a = c ∧ ρ g b = d

/-- The linear-algebra conclusion of a fifteen-point, twice-transitive orbit. -/
theorem finrank_eq_four_of_fifteen_point_orbit
    (ρ : Representation (ZMod 2) G V) (v : V)
    (hspan : Submodule.span (ZMod 2) (Set.range fun g => ρ g v) = ⊤)
    (U : Submodule (ZMod 2) V) (hU : 1 < Module.finrank (ZMod 2) U)
    (hUorb : ∀ u ∈ U, u ≠ 0 → u ∈ Set.range (fun g => ρ g v))
    (htrans : PairTransitiveOrbit ρ v)
    (hcard : Nat.card (Set.range fun g => ρ g v) = 15) :
    Module.finrank (ZMod 2) V = 4 ∧
      Set.range (fun g => ρ g v) = {w : V | w ≠ 0} := by
  classical
  have horb := orbit_eq_nonzero_of_pair_transitive ρ v hspan U hU hUorb htrans
  refine ⟨?_, horb⟩
  rw [horb] at hcard
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Fintype V := Fintype.ofFinite V
  have hnz : Fintype.card {w : V // w ≠ 0} = 15 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hcount := Fintype.card_subtype_compl (fun w : V => w = 0)
  have hpow : 2 ^ Module.finrank (ZMod 2) V = 16 := by
    change Fintype.card {w : V // w ≠ 0} = Fintype.card V - _ at hcount
    rw [hnz, Fintype.card_subtype_eq] at hcount
    have hc : Fintype.card V = 16 := by omega
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card] at hc
    exact hc
  exact Nat.pow_right_injective (by decide : 1 < 2) (by simpa using hpow)

end Representation
