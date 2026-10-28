module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure.Actions
/-!
# Coordinates on the marked cubic actor centralizer

A nonidentity cubic fixing one definite plane has trivial permutation part
and acts only on the companion plane. Commuting actors therefore preserve
both planes. Evaluation identifies its centralizer with SL₂(2) times the
order-three centralizer on the companion plane. The first factor acts by
the prescribed natural binary-plane action. Every nonidentity involution
in this centralizer fixes exactly eight vectors in the full module.

The commutation calculation uses the wreath multiplication symbolically;
only the small binary-plane and supported-involution calculations use
kernel-checked finite certificates.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), setup of
15.3.60, printed p.1150. These are model facts for the actual action, not
an assumed centralizer splitting in the ambient group.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure
open OrthogonalGeometry
namespace ActorCentralizer
local instance : MulDistribMulAction OrthogonalActor OrthogonalVector := orthogonalAction
local instance : MulDistribMulAction OrthogonalPlaneActor OrthogonalPlaneVector := FourGroupMatrixCoordinates.naturalAction
private instance : DecidableEq OrthogonalActor := (RegularWreathProduct.equivProd _ _).decidableEq
private instance : Fintype OrthogonalActor := Fintype.ofEquiv
  ((OrthogonalPlaneIndex → OrthogonalPlaneActor) × OrthogonalPlaneIndex)
  (RegularWreathProduct.equivProd _ _).symm
@[expose] def other (i : OrthogonalPlaneIndex) : OrthogonalPlaneIndex := i * Multiplicative.ofAdd 1
theorem other_ne : ∀ i : OrthogonalPlaneIndex, other i ≠ i := by decide +kernel
theorem index_cases : ∀ i j : OrthogonalPlaneIndex, j = i ∨ j = other i := by decide +kernel
set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 4000 in
theorem marked_coordinates : ∀ (i : OrthogonalPlaneIndex) (a : OrthogonalActor),
    a ^ 3 = 1 → a ≠ 1 →
    (∀ w : OrthogonalVector, (∀ j, j ≠ i → w j = 1) → a • w = w) →
    a.right = 1 ∧ a.left i = 1 ∧ a.left (other i) ^ 3 = 1 ∧ a.left (other i) ≠ 1 := by
  decide +kernel
theorem commute_coordinates (i : OrthogonalPlaneIndex) (a x : OrthogonalActor)
    (hr : a.right = 1) (hi : a.left i = 1) (hne : a.left (other i) ≠ 1) :
    x * a = a * x ↔ x.right = 1 ∧
      x.left (other i) * a.left (other i) = a.left (other i) * x.left (other i) := by
  constructor
  · intro h
    have hx : x.right = 1 := by
      by_contra hx
      have hind : x.right⁻¹ * i = other i := (index_cases i _).resolve_left (by
        intro he
        have hh : x.right⁻¹ = 1 := mul_right_cancel (he.trans (one_mul i).symm)
        exact hx (inv_eq_one.mp hh))
      have hh := congrArg (fun y : OrthogonalActor => y.left i) h
      change x.left i * a.left (x.right⁻¹ * i) = a.left i * x.left (a.right⁻¹ * i) at hh
      rw [hind, hr, inv_one, one_mul, hi, one_mul] at hh
      exact hne (mul_left_cancel (hh.trans (mul_one _).symm))
    refine ⟨hx, ?_⟩
    have hh := congrArg (fun y : OrthogonalActor => y.left (other i)) h
    simpa only [RegularWreathProduct.mul_left, Pi.mul_apply, hr, hx, inv_one, one_mul] using hh
  · rintro ⟨hx, hc⟩
    apply RegularWreathProduct.ext
    · funext j
      rcases index_cases i j with rfl | rfl
      · simp only [RegularWreathProduct.mul_left, Pi.mul_apply, hr, hx, inv_one, one_mul, hi, mul_one]
      · simpa only [RegularWreathProduct.mul_left, Pi.mul_apply, hr, hx, inv_one, one_mul] using hc
    · simp [hr, hx]

private theorem cubic_involution : ∀ b c : OrthogonalPlaneActor,
    b ^ 3 = 1 → b ≠ 1 → c ^ 2 = 1 → c * b = b * c → c = 1 := by decide +kernel

set_option maxRecDepth 4000 in
private theorem supported_involution_fixed : ∀ (i : OrthogonalPlaneIndex) (x : OrthogonalActor),
    x.right = 1 → x.left (other i) = 1 → x ^ 2 = 1 → x ≠ 1 →
    Fintype.card {v : OrthogonalVector // x • v = v} = 8 := by decide +kernel

theorem involution_fixed (i : OrthogonalPlaneIndex) (a x : OrthogonalActor)
    (hr : a.right = 1) (hi : a.left i = 1)
    (hp : a.left (other i) ^ 3 = 1) (hn : a.left (other i) ≠ 1)
    (hc : x * a = a * x) (hx : x ^ 2 = 1) (hne : x ≠ 1) :
    Fintype.card {v : OrthogonalVector // x • v = v} = 8 := by
  obtain ⟨hrx, hcx⟩ := (commute_coordinates i a x hr hi hn).mp hc
  have hpx : x.left (other i) ^ 2 = 1 := by
    have h := congrArg (fun y : OrthogonalActor => y.left (other i)) hx
    simpa only [pow_two, RegularWreathProduct.mul_left, Pi.mul_apply,
      hrx, inv_one, one_mul, RegularWreathProduct.one_left, Pi.one_apply] using h
  exact supported_involution_fixed i x hrx (cubic_involution _ _ hp hn hpx hcx) hx hne
theorem cubic_centralizer_card : ∀ b : OrthogonalPlaneActor,
    b ^ 3 = 1 → b ≠ 1 → Fintype.card {x : OrthogonalPlaneActor // x * b = b * x} = 3 := by
  decide +kernel

/-- Evaluation on the fixed plane and its companion identifies the actual actor centralizer. -/
@[expose] def coordinates (i : OrthogonalPlaneIndex) (a : OrthogonalActor)
    (hr : a.right = 1) (hi : a.left i = 1) (hn : a.left (other i) ≠ 1) :
    centralizer ({a} : Set OrthogonalActor) ≃*
      OrthogonalPlaneActor × centralizer ({a.left (other i)} : Set OrthogonalPlaneActor) where
  toFun x := (x.val.left i, ⟨x.val.left (other i), mem_centralizer_singleton_iff.mpr
    ((commute_coordinates i a x hr hi hn).mp (mem_centralizer_singleton_iff.mp x.property)).2⟩)
  invFun y := ⟨⟨fun j => if j = i then y.1 else y.2, 1⟩,
    mem_centralizer_singleton_iff.mpr ((commute_coordinates i a _ hr hi hn).mpr
      ⟨rfl, by simpa only [if_neg (other_ne i)] using mem_centralizer_singleton_iff.mp y.2.property⟩)⟩
  left_inv x := by
    apply Subtype.ext
    apply RegularWreathProduct.ext
    · funext j
      rcases index_cases i j with rfl | rfl
      · exact if_pos rfl
      · exact if_neg (other_ne i)
    · exact ((commute_coordinates i a x hr hi hn).mp
        (mem_centralizer_singleton_iff.mp x.property)).1.symm
  right_inv y := by
    apply Prod.ext
    · exact if_pos rfl
    · exact Subtype.ext (if_neg (other_ne i))
  map_mul' x y := by
    have hx := ((commute_coordinates i a x hr hi hn).mp
      (mem_centralizer_singleton_iff.mp x.property)).1
    apply Prod.ext
    · change x.val.left i * y.val.left (x.val.right⁻¹ * i) = x.val.left i * y.val.left i
      rw [hx, inv_one, one_mul]
    · apply Subtype.ext
      change x.val.left (other i) * y.val.left (x.val.right⁻¹ * other i) =
        x.val.left (other i) * y.val.left (other i)
      rw [hx, inv_one, one_mul]

theorem card_companion (b : OrthogonalPlaneActor) (hp : b ^ 3 = 1) (hn : b ≠ 1) :
    Nat.card (centralizer ({b} : Set OrthogonalPlaneActor)) = 3 := by
  have e := Equiv.subtypeEquivRight (fun x : OrthogonalPlaneActor =>
    mem_centralizer_singleton_iff (g := b) (k := x))
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  exact cubic_centralizer_card b hp hn

theorem companion_zpowers_top (b : OrthogonalPlaneActor) (hp : b ^ 3 = 1) (hn : b ≠ 1) :
    zpowers (⟨b, mem_centralizer_singleton_iff.mpr rfl⟩ :
      centralizer ({b} : Set OrthogonalPlaneActor)) = ⊤ := by
  apply eq_of_le_of_card_ge le_top
  rw [card_top, card_companion b hp hn, Nat.card_zpowers]
  have ho : orderOf (⟨b, mem_centralizer_singleton_iff.mpr rfl⟩ :
      centralizer ({b} : Set OrthogonalPlaneActor)) = 3 := by
    apply orderOf_eq_prime
    · exact Subtype.ext hp
    · intro he
      exact hn (congrArg Subtype.val he)
  exact ho.ge

end ActorCentralizer
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure
