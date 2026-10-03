module

public import Theory.SpecificGroups.C4SquareSignSwap
public import Mathlib.Tactic.Group

/-!
# Recognition of the C₄-square inverter core

An index-two subgroup isomorphic to C₄ × C₄, together with an outside
involution acting by inversion, identifies the group with the inverter core
of the sign-and-swap model. The map sends the model's base coordinates through
the supplied equivalence and its sign coordinate to the involution. The two
cosets prove surjectivity, and the order proves injectivity.

This is the presentation step for the small-order recognition used alongside
Janko–Thompson, Math. Z. 113 (1970), results 1.3–1.4, printed p.386.
-/

namespace C4SquareSignSwap

private def coreElement (x : Base) (c : C2) : inverterCore := ⟨⟨x, (c, 1)⟩, rfl⟩

private theorem coreElement_mul (x y : Base) (c d : C2) :
    coreElement x c * coreElement y d =
      coreElement (x * if c = 1 then y else y⁻¹) (c * d) := by
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change x * action (c, 1) y = x * (if c = 1 then y else y⁻¹)
    change x * twist (c, 1) y = _
    simp [twist]
  · rfl

private theorem coreElement_cases (g : inverterCore) :
    g = coreElement g.val.left g.val.right.1 := by
  apply Subtype.ext
  exact SemidirectProduct.ext rfl (Prod.ext rfl g.property)

private def inverterHom {G : Type*} [Group G] (f : Base →* G)
    (t : G) (ht : t ^ 2 = 1) (hi : ∀ x, t * f x * t⁻¹ = f x⁻¹) :
    inverterCore →* G where
  toFun g := f g.val.left * t ^ g.val.right.1.toAdd.val
  map_one' := by simp
  map_mul' g h := by
    obtain ⟨x, c, rfl⟩ : ∃ x c, g = coreElement x c :=
      ⟨_, _, coreElement_cases g⟩
    obtain ⟨y, d, rfl⟩ : ∃ y d, h = coreElement y d :=
      ⟨_, _, coreElement_cases h⟩
    rw [coreElement_mul]
    have hc : c = 1 ∨ c = Multiplicative.ofAdd 1 := (by decide : ∀ c : C2,
      c = 1 ∨ c = Multiplicative.ofAdd 1) c
    have hd : d = 1 ∨ d = Multiplicative.ofAdd 1 := (by decide : ∀ c : C2,
      c = 1 ∨ c = Multiplicative.ofAdd 1) d
    have hv : (1 : ZMod 2).val = 1 := by decide
    have hmul : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide
    have ht' : t * t = 1 := by simpa only [pow_two] using ht
    have hrel (y : Base) : t * f y = f y⁻¹ * t := by
      rw [← hi y, mul_assoc, inv_mul_cancel, mul_one]
    have htr (y : Base) : t * (f y * t) = (f y)⁻¹ := by
      rw [← mul_assoc, hrel, mul_assoc, ht', mul_one, map_inv]
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
      simp [coreElement, hmul, hv, map_mul, hrel, mul_assoc, htr]


/-- An inverted C₄-square base and an outside involution determine the core. -/
public theorem recognition_of_inverted_base {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 32) (A : Subgroup G) (hi : A.index = 2)
    (e : A ≃* Base) (t : G) (htA : t ∉ A) (ht : t ^ 2 = 1)
    (hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹) :
    Nonempty (G ≃* inverterCore) := by
  let f : Base →* G := A.subtype.comp e.symm.toMonoidHom
  have hcompat (x : Base) : t * f x * t⁻¹ = f x⁻¹ := by
    change t * (e.symm x : G) * t⁻¹ = (e.symm x⁻¹ : G)
    rw [map_inv]
    exact hinv _ (e.symm x).property
  let F := inverterHom f t ht hcompat
  have hsurj : Function.Surjective F := by
    intro g
    by_cases hg : g ∈ A
    · refine ⟨coreElement (e ⟨g, hg⟩) 1, ?_⟩
      simp [F, inverterHom, coreElement, f]
    · have hgt : g * t⁻¹ ∈ A := (A.mul_mem_iff_of_index_two hi).mpr (by
        simpa only [A.inv_mem_iff] using (iff_of_false hg htA))
      refine ⟨coreElement (e ⟨g * t⁻¹, hgt⟩) (Multiplicative.ofAdd 1), ?_⟩
      simp [F, inverterHom, coreElement, f, show (1 : ZMod 2).val = 1 by decide]
  exact ⟨(MulEquiv.ofBijective F (hsurj.bijective_of_nat_card_le (by
    rw [hcard, card_inverterCore]))).symm⟩

end C4SquareSignSwap
