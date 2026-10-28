module

public import Theory.GroupAction.CommutatorSemidirect
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.Tactic

/-!
# The common-center bound in the rank-two five-primary case

Each of the two factor involutions moves a binary plane. If both act
nontrivially on D with a common center of order two, that center lies in
both moved planes. The product-order formula then bounds the whole moved
subgroup by order eight, contradicting its order sixteen.

The proof works for any finite abelian module. It first proves that the
moved subgroup of a generated actor group is the join of the two moved
subgroups, then uses their nontrivial restrictions to identify the common
line. Merely assuming that D has codimension two would not give this bound.
The source factor analysis must supply the plane dimensions and the
faithful common-center action furnished by F.9.16(2).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951, the paragraph excluding |Uγ*|=4.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
open Subgroup
variable {W : Type*} [CommGroup W]

private def fixesModulo (S : Subgroup W) : Subgroup (MulAut W) where
  carrier := {a | ∀ w, w⁻¹ * a w ∈ S}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb w
    have hm := S.mul_mem (ha (b w)) (hb w)
    convert hm using 1
    change w⁻¹ * a (b w) = _
    calc
      w⁻¹ * a (b w) = (w⁻¹ * a (b w)) * ((b w)⁻¹ * b w) := by simp
      _ = _ := by ac_rfl
  inv_mem' := by
    intro a ha w
    have hm := S.inv_mem (ha (a⁻¹ w))
    simpa only [MulAut.apply_inv_self, mul_inv_rev, inv_inv] using hm

private theorem commutatorAction_le_iff (A : Subgroup (MulAut W)) (S : Subgroup W) :
    commutatorAction A W ≤ S ↔ A ≤ fixesModulo S := by
  change Subgroup.closure _ ≤ S ↔ _
  rw [closure_le]
  constructor
  · intro hh a ha w
    exact hh ⟨⟨a, ha⟩, w, mem_top w, rfl⟩
  · rintro hh _ ⟨a, w, _, rfl⟩
    exact hh a.property w

/-- The moved subgroup of a generated actor group is the sum of the
moved subgroups of its generators, on the whole abelian module. -/
theorem commutatorAction_sup (A B : Subgroup (MulAut W)) :
    commutatorAction (A ⊔ B : Subgroup (MulAut W)) W =
      commutatorAction A W ⊔ commutatorAction B W := by
  apply le_antisymm
  · apply (commutatorAction_le_iff _ _).mpr
    exact sup_le ((commutatorAction_le_iff _ _).mp le_sup_left)
      ((commutatorAction_le_iff _ _).mp le_sup_right)
  · have h := (commutatorAction_le_iff (A ⊔ B) _).mp le_rfl
    exact sup_le ((commutatorAction_le_iff _ _).mpr (le_sup_left.trans h))
      ((commutatorAction_le_iff _ _).mpr (le_sup_right.trans h))

private theorem line_le_moved [Finite W]
    (A : Subgroup (MulAut W)) (D Z : Subgroup W)
    (hZ : Nat.card Z = 2) (hne : commutatorSubgroup A W D ≠ ⊥)
    (hline : commutatorSubgroup A W D ≤ Z) : Z ≤ commutatorAction A W := by
  have hpos := Nat.card_pos (α := commutatorSubgroup A W D)
  have hnot : Nat.card (commutatorSubgroup A W D) ≠ 1 :=
    fun he => hne (card_eq_one.mp he)
  have he : commutatorSubgroup A W D = Z :=
    eq_of_le_of_card_ge hline (by omega)
  exact he.symm.le.trans (commutatorSubgroup_mono le_top)

/-- Two rank-two displacements sharing a nonzero transvection center have
total rank at most three. The nontrivial restrictions to D are needed:
a center containment alone does not give the bound. -/
theorem moved_card_le_eight_of_common_center [Finite W]
    (A B : Subgroup (MulAut W)) (D Z : Subgroup W)
    (hZ : Nat.card Z = 2)
    (hA : Nat.card (commutatorAction A W) = 4)
    (hB : Nat.card (commutatorAction B W) = 4)
    (hneA : commutatorSubgroup A W D ≠ ⊥)
    (hneB : commutatorSubgroup B W D ≠ ⊥)
    (hlineA : commutatorSubgroup A W D ≤ Z)
    (hlineB : commutatorSubgroup B W D ≤ Z) :
    Nat.card (commutatorAction (A ⊔ B : Subgroup (MulAut W)) W) ≤ 8 := by
  have hZA := line_le_moved A D Z hZ hneA hlineA
  have hZB := line_le_moved B D Z hZ hneB hlineB
  have hi := card_le_of_le (le_inf hZA hZB)
  rw [hZ] at hi
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (commutatorAction A W) (commutatorAction B W) le_normalizer_of_normal
  rw [hA, hB] at hc
  rw [commutatorAction_sup]
  nlinarith

/-- The common-center action furnished by F.9.16(2) is incompatible with
the four-dimensional moved space in the rank-two five-primary case. -/
theorem no_rank_two_common_center [Finite W]
    (A B : Subgroup (MulAut W)) (D Z : Subgroup W)
    (hZ : Nat.card Z = 2)
    (hA : Nat.card (commutatorAction A W) = 4)
    (hB : Nat.card (commutatorAction B W) = 4)
    (hneA : commutatorSubgroup A W D ≠ ⊥)
    (hneB : commutatorSubgroup B W D ≠ ⊥)
    (hlineA : commutatorSubgroup A W D ≤ Z)
    (hlineB : commutatorSubgroup B W D ≤ Z)
    (hfull : Nat.card (commutatorAction (A ⊔ B : Subgroup (MulAut W)) W) = 16) :
    False := by
  have hh := moved_card_le_eight_of_common_center A B D Z hZ hA hB
    hneA hneB hlineA hlineB
  omega

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end
