module

public import Theory.SpecificGroups.ExoticTwoGroup.LiftCorrection
public import Theory.GroupTheory.CharacteristicInverterSquare
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

/-!
# The inversion lift has square one

Suppose the abelian base of an exotic action frame is the Frattini subgroup
of the centralizer of its elementary four. An automorphism of that centralizer
preserves the base and hence sends the inversion lift to another inverter.
Self-centralization makes the two squares equal. The square lies in the four,
where transitivity on involutions rules out a nonidentity fixed element.

The Frattini identity and transitivity are explicit inputs; no order-three
automorphism or additional lift relation is assumed. This is the square
consequence of MacWilliams, Trans. Amer. Math. Soc. 150 (1970), §4, (ii) and
(xviii), printed pp.387 and 396, for the presentation in Janko–Thompson,
Math. Z. 113 (1970), 1.4(c), printed p.386.
-/

open Subgroup
namespace ExoticTwoGroup.ActionFrame
variable {P : Type*} [Group P] [Finite P] {D W B : Subgroup P}

/-- The inverter is an involution when its base is the Frattini subgroup
of the four-centralizer and that centralizer is transitive on the four's
involutions. -/
public theorem z_sq_eq_one_of_frattini
    (f : ActionFrame D W B) [IsMulCommutative D] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (hWD : W ≤ D)
    (hDC : centralizer (D : Set P) ≤ D)
    (hDO : (omega₁ D (p := 2)).map D.subtype = W)
    (htrans : ∀ x y : centralizer (W : Set P), (x : P) ∈ W → (y : P) ∈ W →
      orderOf x = 2 → orderOf y = 2 →
      ∃ α : MulAut (centralizer (W : Set P)), α x = y)
    (hPhi : D = (frattini (centralizer (W : Set P))).map
      (centralizer (W : Set P)).subtype) : f.z₀ ^ 2 = 1 := by
  let C := centralizer (W : Set P)
  have hzC : f.z₀ ∈ C := by
    intro w hw
    have hw2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) w hw
    have hwi : w⁻¹ = w := (eq_inv_iff_mul_eq_one.mpr (by simpa [pow_two] using hw2)).symm
    have hi := f.z_inverts_base (hWD hw)
    rw [hwi] at hi
    exact (mul_inv_eq_iff_eq_mul.mp hi).symm
  let z : C := ⟨f.z₀, hzC⟩
  have hPhiC : centralizer (frattini C : Set C) ≤ frattini C := by
    intro x hx
    apply (mem_map_iff_mem C.subtype_injective).mp
    change (x : P) ∈ (frattini C).map C.subtype
    rw [← hPhi]
    apply hDC
    intro d hd
    obtain ⟨a, ha, rfl⟩ := hPhi.le hd
    exact congrArg Subtype.val (hx a ha)
  have hinv : ∀ a ∈ frattini C, z * a * z⁻¹ = a⁻¹ := by
    intro a ha
    apply Subtype.ext
    exact f.z_inverts_base (hPhi.ge (mem_map_of_mem C.subtype ha))
  have hfix (α : MulAut C) : α (z ^ 2) = z ^ 2 :=
    automorphism_sq_eq_of_characteristic_inverted (frattini C) hPhiC z hinv α
  by_contra hn
  have hz2 : orderOf (z ^ 2) = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      simpa only [coe_pow, coe_one, ← pow_mul] using f.z_four hDC
    · intro h
      exact hn (congrArg Subtype.val h)
  have hs2 : orderOf (f.z₀ ^ 2) = 2 := (orderOf_coe (z ^ 2)).trans hz2
  have hnot : ¬ W ≤ zpowers (f.z₀ ^ 2) := by
    intro h
    have hh := card_le_of_le h
    rw [Nat.card_zpowers, hs2, hW] at hh
    omega
  obtain ⟨x, hxW, hxK⟩ := SetLike.not_le_iff_exists.mp hnot
  let xC : C := ⟨x, le_centralizer W hxW⟩
  have hx2 : orderOf xC = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) x hxW
    · intro h
      apply hxK
      have hx1 : x = 1 := congrArg Subtype.val h
      rw [hx1]
      exact one_mem _
  obtain ⟨α, hα⟩ := htrans (z ^ 2) xC (f.z_sq_mem_four hDC hDO) hxW hz2 hx2
  have he : x = f.z₀ ^ 2 := congrArg Subtype.val (hα.symm.trans (hfix α))
  apply hxK
  rw [he]
  exact mem_zpowers _
end ExoticTwoGroup.ActionFrame
