module

public import Theory.GroupAction.TernaryFusedFour.MatrixClassification.Listing
public import Theory.GroupAction.TernaryFusedFour.Reduction
/-!
# The order-twelve matrix node and its normal Sylow subgroup

A certified twelve-element list proves the exact order of node 16. A separate
matrix calculation proves closure of its square-one elements under products.
In any group, these elements form a normal two-subgroup when they are closed
under products. Each elementary Sylow two-subgroup lies in it, so Sylow
maximality gives normality. This uses the actual matrix node, without an
assumed alternating-group identification or subgroup-order certificate.

Source application: Bender (1974), (4.1), p.225, citing Janko (1966), Lemma 3.1.
-/

namespace TernaryFusedFour.MatrixClassification
open Matrix Matrix.PSL3Three Matrix.PSL3Three.CertifiedEnumeration

private theorem normal_sylow_of_square_closed {G : Type*} [Group G]
    (hclosed : ∀ a b : G, a ^ 2 = 1 → b ^ 2 = 1 → (a * b) ^ 2 = 1)
    (hel : ∀ P : Sylow 2 G, IsElementaryAbelian 2 P) :
    ∀ P : Sylow 2 G, (P : Subgroup G).Normal := by
  let Q : Subgroup G := {
    carrier := {x | x ^ 2 = 1}
    one_mem' := one_pow 2
    mul_mem' := fun ha hb => hclosed _ _ ha hb
    inv_mem' := by
      intro x hx
      change x ^ 2 = 1 at hx
      change (x⁻¹) ^ 2 = 1
      rw [inv_pow, hx, inv_one] }
  have hQ : Q.Normal := by
    constructor
    intro x hx g
    change (g * x * g⁻¹) ^ 2 = 1
    change ((MulAut.conj g) x) ^ 2 = 1
    rw [← map_pow, show x ^ 2 = 1 from hx, map_one]
  have hp : IsPGroup 2 Q := isPGroup_iff_pow_pow_eq_one.mpr (fun x =>
    ⟨1, Subtype.ext x.property⟩)
  intro P
  have heq : Q = (P : Subgroup G) := P.is_maximal' hp (by
    let := hel P
    intro x hx
    exact elemPow_eq_one_of_isElementaryAbelian x hx)
  rw [← heq]
  exact hQ
private def listing16 : Listing 16 12 where
  code := ![6643, 2259, 2223, 1707, 1947, 1221, 975, 6725, 13285, 13205, 4419, 4437]
  previous := ![0, 0, 0, 1, 1, 2, 2, 3, 4, 4, 7, 7]
  letter := (show Fin 12 → Fin 2 from ![0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1])
  next := ![![1, 3, 5, 0, 8, 9, 7, 10, 11, 2, 6, 4], ![2, 4, 6, 7, 9, 8, 0, 11, 10, 1, 5, 3], ![3, 0, 9, 1, 11, 2, 10, 6, 4, 5, 7, 8], ![6, 9, 0, 11, 1, 10, 2, 3, 5, 4, 8, 7]]

private theorem listing16_checked : listing16.check = true := by decide +kernel

public theorem card_properNode16 : Nat.card (properNode 16) = 12 :=
  (listing16.sound (by decide) listing16_checked).1

private theorem square_closed_checked : ∀ r s : Fin 12,
    (decodeMatrix (listing16.code r)) ^ 2 = 1 →
    (decodeMatrix (listing16.code s)) ^ 2 = 1 →
    (decodeMatrix (listing16.code r) * decodeMatrix (listing16.code s)) ^ 2 = 1 := by
  decide +kernel

public theorem normal_sylow_properNode16
    (hel : ∀ P : Sylow 2 (properNode 16), IsElementaryAbelian 2 P) :
    ∀ P : Sylow 2 (properNode 16), (P : Subgroup (properNode 16)).Normal := by
  apply normal_sylow_of_square_closed _ hel
  intro a b ha hb
  obtain ⟨r, hr⟩ := (listing16.sound (by decide) listing16_checked).2 a a.property
  obtain ⟨s, hs⟩ := (listing16.sound (by decide) listing16_checked).2 b b.property
  have ha' : a.val.val ^ 2 = 1 := congrArg (fun x : properNode 16 => x.val.val) ha
  have hb' : b.val.val ^ 2 = 1 := congrArg (fun x : properNode 16 => x.val.val) hb
  apply Subtype.ext
  apply Subtype.ext
  change (a.val.val * b.val.val) ^ 2 = 1
  rw [hr, hs]
  rw [hr] at ha'
  rw [hs] at hb'
  exact square_closed_checked r s ha' hb'

end TernaryFusedFour.MatrixClassification
