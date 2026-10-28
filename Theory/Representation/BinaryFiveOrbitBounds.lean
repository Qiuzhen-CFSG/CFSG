module

public import Theory.Representation.BinaryFiveOrbit
public import Theory.Representation.BinaryPrimeDegree

/-!
# Dimension bounds for a binary five-point spanning orbit

A vector fixed by a Sylow two-subgroup of index five has an orbit spanning
at most five dimensions. If the representation is faithful, the prime five
dividing the group order forces at least four dimensions. Thus the space
has dimension four or five, and cardinality sixteen or thirty-two.

The upper bound is the surjective pentagon orbit map; the lower bound is
the multiplicative order of two modulo five. The intended source application
is Aschbacher–Smith 14.2.20(1), printed p.987.
-/

public section

namespace BinaryPentagon

variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W]
  [Module (ZMod 2) W]

/-- A binary module spanned by a Sylow-fixed vector has dimension at most
five when that Sylow subgroup has index five. -/
theorem finrank_le_five_of_index_five_orbit
    (ρ : Representation (ZMod 2) H W) (S : Sylow 2 H) (hi : S.index = 5)
    (w : W) (hw : ∀ s : S, ρ s w = w)
    (hspan : Submodule.span (ZMod 2) (Set.range (fun h : H => ρ h w)) = ⊤) :
    Module.finrank (ZMod 2) W ≤ 5 := by
  obtain ⟨a, ha, hcomp⟩ := exists_five_complement S hi
  obtain ⟨f, hf, _, _⟩ := exists_five_orbit_map ρ S a ha hcomp w hw hspan
  simpa only [Space, Module.finrank_pi, Fintype.card_fin] using
    LinearMap.finrank_le_finrank_of_surjective hf

variable [FiniteDimensional (ZMod 2) W]

/-- Faithfulness gives the matching lower bound from the prime five. -/
theorem finrank_eq_four_or_five_of_index_five_orbit
    (ρ : Representation (ZMod 2) H W) (hρ : Function.Injective ρ)
    (S : Sylow 2 H) (hi : S.index = 5)
    (w : W) (hw : ∀ s : S, ρ s w = w)
    (hspan : Submodule.span (ZMod 2) (Set.range (fun h : H => ρ h w)) = ⊤) :
    Module.finrank (ZMod 2) W = 4 ∨ Module.finrank (ZMod 2) W = 5 := by
  have hlo := Representation.BinaryPrimeDegree.orderOf_le_finrank ρ hρ
    (by decide : Nat.Prime 5) (by decide : 5 ≠ 2)
    (hi ▸ (S : Subgroup H).index_dvd_card)
  rw [Representation.BinaryPrimeDegree.orderOf_two_mod_five] at hlo
  have hhi := finrank_le_five_of_index_five_orbit ρ S hi w hw hspan
  omega

/-- The cardinal alternatives for a faithful binary five-point spanning orbit. -/
theorem card_eq_sixteen_or_thirtyTwo_of_index_five_orbit
    (ρ : Representation (ZMod 2) H W) (hρ : Function.Injective ρ)
    (S : Sylow 2 H) (hi : S.index = 5)
    (w : W) (hw : ∀ s : S, ρ s w = w)
    (hspan : Submodule.span (ZMod 2) (Set.range (fun h : H => ρ h w)) = ⊤) :
    Nat.card W = 16 ∨ Nat.card W = 32 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rcases finrank_eq_four_or_five_of_index_five_orbit ρ hρ S hi w hw hspan with h | h
  · left
    simp only [h]
    norm_num
  · right
    simp only [h]
    norm_num

end BinaryPentagon
