module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Aligning an elementary eight and a central nonsquare in C₂ × D₈

`CyclicTwoDihedralFour.exists_alignment` simultaneously sends the canonical
first-factor involution to any supplied central nonsquare and sends the
canonical reflection centralizer to any supplied elementary subgroup of order
eight. The statement uses the literal finite model and requires no ambient
recognition hypotheses.

Commuting involutions lie in one of the two reflection centralizers; their
orders identify an arbitrary elementary eight with one of these centralizers.
The automorphism fixing the rotation and shifting reflection indices by one
interchanges the two subgroups and fixes the first-factor involution. A second
automorphism multiplies that involution by the central rotation of order two
and preserves both subgroups. These handle the two possible central nonsquares.
All computations on the sixteen-element model are checked by Lean's kernel.

This intrinsic coordinate calculation supplies the alignment used in the
order-32 Sylow argument of Kurzweil–Stellmacher, *The Theory of Finite Groups*,
Chapter 12, printed p. 367 (`refs/latex/kurzweil.tex`). The resulting embedding
can use the canonical coordinates of `CyclicTwoDihedralFourExtension`.
-/

namespace CyclicTwoDihedralFour

open scoped IsMulCommutative

private abbrev Model := Multiplicative (ZMod 2) × DihedralGroup 4
private def c : Model := (Multiplicative.ofAdd 1, 1)
private def z : Model := (1, .r 2)
private def b : Model := (1, .sr 0)
private def b' : Model := (1, .sr 1)
private def leftPlane : Subgroup Model := Subgroup.centralizer {b}
private def rightPlane : Subgroup Model := Subgroup.centralizer {b'}

private instance (x : Model) : Decidable (x ∈ leftPlane) :=
  decidable_of_iff (x * b = b * x) Subgroup.mem_centralizer_singleton_iff.symm
private instance (x : Model) : Decidable (x ∈ rightPlane) :=
  decidable_of_iff (x * b' = b' * x) Subgroup.mem_centralizer_singleton_iff.symm

private theorem plane_cards : Nat.card leftPlane = 8 ∧ Nat.card rightPlane = 8 := by
  simp only [Nat.card_eq_fintype_card]
  decide

set_option maxRecDepth 20000 in
set_option synthInstance.maxSize 256 in
private theorem commuting_involutions : ∀ x y : Model,
    x ^ 2 = 1 → y ^ 2 = 1 → x * y = y * x →
    x ∉ leftPlane → y ∈ rightPlane := by decide

private theorem plane_cases (E : Subgroup Model)
    (hE : IsElementaryAbelian 2 E) (hcard : Nat.card E = 8) :
    E = leftPlane ∨ E = rightPlane := by
  classical
  let := hE
  by_cases hle : E ≤ leftPlane
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge hle (by rw [plane_cards.1, hcard]))
  right
  obtain ⟨x, hx, hout⟩ := SetLike.not_le_iff_exists.mp hle
  apply Subgroup.eq_of_le_of_card_ge ?_ (by rw [plane_cards.2, hcard])
  intro y hy
  apply commuting_involutions x y
    (elemPow_eq_one_of_isElementaryAbelian x hx)
    (elemPow_eq_one_of_isElementaryAbelian y hy) _ hout
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : E) ⟨y, hy⟩)

private def swapFun (x : Model) : Model :=
  (x.1, match x.2 with | .r j => .r j | .sr j => .sr (j + 1))
private def swapInv (x : Model) : Model :=
  (x.1, match x.2 with | .r j => .r j | .sr j => .sr (j - 1))

set_option maxRecDepth 20000 in
private def swap : Model ≃* Model where
  toFun := swapFun
  invFun := swapInv
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

private def twistFun (x : Model) : Model :=
  (x.1, (if x.1 = 1 then 1 else DihedralGroup.r 2) * x.2)

set_option maxRecDepth 20000 in
private def twist : Model ≃* Model where
  toFun := twistFun
  invFun := twistFun
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

private theorem swap_c : swap c = c := by decide
private theorem twist_c : twist c = c * z := by decide

private theorem swap_plane : leftPlane.map swap.toMonoidHom = rightPlane := by
  apply Subgroup.eq_of_le_of_card_ge ?_ ?_
  · have h := Subgroup.map_centralizer_le_centralizer_image ({b} : Set Model)
      swap.toMonoidHom
    simpa only [leftPlane, rightPlane, Set.image_singleton, MulEquiv.coe_toMonoidHom,
      show swap b = b' from by decide] using h
  · rw [Subgroup.card_map_of_injective swap.injective, plane_cards.1, plane_cards.2]

private theorem twist_stable : ∀ x : Model,
    (x ∈ leftPlane → twist x ∈ leftPlane) ∧
      (x ∈ rightPlane → twist x ∈ rightPlane) := by decide

private theorem twist_plane (P : Subgroup Model) (hP : P = leftPlane ∨ P = rightPlane) :
    P.map twist.toMonoidHom = P := by
  apply Subgroup.eq_of_le_of_card_ge ?_ (Subgroup.card_map_of_injective twist.injective).ge
  rintro _ ⟨x, hx, rfl⟩
  rcases hP with rfl | rfl
  · exact (twist_stable x).1 hx
  · exact (twist_stable x).2 hx

private theorem nonsquare_cases : ∀ t : Model, t ∈ Subgroup.center Model →
    (∀ x : Model, x ^ 2 ≠ t) → t = c ∨ t = c * z := by decide

/-- An automorphism aligns the canonical elementary eight and first-factor
involution with any elementary eight and central nonsquare in `C₂ × D₈`. -/
public theorem exists_alignment
    (E : Subgroup (Multiplicative (ZMod 2) × DihedralGroup 4))
    (hE : IsElementaryAbelian 2 E) (hcard : Nat.card E = 8)
    (t : Multiplicative (ZMod 2) × DihedralGroup 4)
    (ht : t ∈ Subgroup.center (Multiplicative (ZMod 2) × DihedralGroup 4))
    (hns : ∀ x : Multiplicative (ZMod 2) × DihedralGroup 4, x ^ 2 ≠ t) :
    ∃ e : (Multiplicative (ZMod 2) × DihedralGroup 4) ≃*
        (Multiplicative (ZMod 2) × DihedralGroup 4),
      e (Multiplicative.ofAdd 1, 1) = t ∧
      (Subgroup.centralizer
        ({(1, DihedralGroup.sr 0)} : Set (Multiplicative (ZMod 2) × DihedralGroup 4))).map
        e.toMonoidHom = E := by
  obtain rfl | rfl := plane_cases E hE hcard
  all_goals obtain rfl | rfl := nonsquare_cases t ht hns
  · exact ⟨MulEquiv.refl _, rfl, by simp [leftPlane, b]⟩
  · exact ⟨twist, twist_c, twist_plane _ (Or.inl rfl)⟩
  · exact ⟨swap, swap_c, swap_plane⟩
  · refine ⟨swap.trans twist, ?_, ?_⟩
    · exact (congrArg twist swap_c).trans twist_c
    · change leftPlane.map (twist.toMonoidHom.comp swap.toMonoidHom) = rightPlane
      rw [← Subgroup.map_map]
      exact (congrArg (fun P => P.map twist.toMonoidHom) swap_plane).trans
        (twist_plane _ (Or.inr rfl))

end CyclicTwoDihedralFour
