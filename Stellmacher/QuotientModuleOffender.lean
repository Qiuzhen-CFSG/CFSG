module
public import Stellmacher.QuotientModuleFixedPoints
public import Stellmacher.QuotientModuleImageCard

/-!
# Transporting ambient offenders into the faithful quotient

If an elementary subgroup Y lies in T and its fixed-module index is at most
its faithful image order, then its projection belongs to Section 1's offender
family for the projected T. The statement uses the exact action carried by a
centralizer quotient-module witness.

Fixed-point transport identifies the vector factor, while the shared
kernel-image cardinal formula identifies the faithful actor order. Canceling
the positive centralizer order turns the ambient inequality into m ≤ 1;
containment and elementary abelian structure pass to the image. No Section 1
structural theorem is needed for this translation.

This supplies the step placing the projected opposite endpoint center in
J(Z_a, barred S) in Stellmacher (8.1), journal p.37.
-/

namespace Stellmacher.Later

universe u

/-- An ambient faithful-index offender projects into Section 1's oneA family. -/
public theorem QuotientModuleWitness.oneA_of_card_le
    {G : Type u} [Group G] [Finite G] {A V : Subgroup G}
    (w : QuotientModuleWitness A (A ⊓ Subgroup.centralizer (V : Set G)) V)
    (Y T : Subgroup G) (hYT : Y ≤ T) (hTA : T ≤ A)
    [IsElementaryAbelian 2 Y]
    (hcard : Nat.card V * Nat.card (Y ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) ≤
      Nat.card Y * Nat.card (V ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G)) :
    let _ := w.groupX
    let _ := w.finiteX
    let _ := MulDistribMulAction.compHom V w.action
    SectionOne.oneA (G := w.X) (V := V)
      ((T.subgroupOf A).map w.projection) ((Y.subgroupOf A).map w.projection) := by
  let := w.groupX
  let := w.finiteX
  let := MulDistribMulAction.compHom V w.action
  let Yb : Subgroup w.X := (Y.subgroupOf A).map w.projection
  let K : Subgroup G := Y ⊓ Subgroup.centralizer (V : Set G)
  let F : Subgroup G := V ⊓ Subgroup.centralizer (Y : Set G)
  let : IsElementaryAbelian 2 (Y.subgroupOf A) :=
    IsElementaryAbelian.subgroupOf (hYT.trans hTA)
  let : IsElementaryAbelian 2 Yb := IsElementaryAbelian.map w.projection
  refine ⟨Subgroup.map_mono (show Y.subgroupOf A ≤ T.subgroupOf A from
    fun _ hx ↦ hYT hx), inferInstance, ?_⟩
  have himage := w.image_card_mul_centralizer_card Y (hYT.trans hTA)
  change Nat.card Yb * Nat.card K = Nat.card Y at himage
  have hfix := w.fixedPoints_card Y (hYT.trans hTA)
  change Nat.card (FixedPoints.subgroup Yb V) = Nat.card F at hfix
  have hh : Nat.card K * Nat.card V ≤ Nat.card K * (Nat.card F * Nat.card Yb) := by
    change Nat.card V * Nat.card K ≤ Nat.card Y * Nat.card F at hcard
    rw [← himage] at hcard
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcard
  have hnum : Nat.card V ≤ Nat.card F * Nat.card Yb :=
    Nat.le_of_mul_le_mul_left hh Nat.card_pos
  change (Nat.card V : ℚ) /
    ((Nat.card (FixedPoints.subgroup Yb V) : ℚ) * (Nat.card Yb : ℚ)) ≤ 1
  have hpos : (0 : ℚ) <
      (Nat.card (FixedPoints.subgroup Yb V) : ℚ) * (Nat.card Yb : ℚ) :=
    mul_pos (by exact_mod_cast Nat.card_pos) (by exact_mod_cast Nat.card_pos)
  apply (div_le_iff₀ hpos).mpr
  rw [one_mul, hfix]
  exact_mod_cast hnum

end Stellmacher.Later

