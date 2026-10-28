module
public import ABG.ChapterII.Section3.CharacteristicPowerDefs
public import GorensteinWalter.SL2ProjectiveCover

/-!
# Solvability forces source characteristic power three

For a finite solvable group H, any source-stage characteristic datum has
field order three. The datum uses the actual characteristic SL2 subgroup
of H/O(H), so this conclusion is available before the final GL2/GU2
centralizer description in the ABG main theorems.

Solvability passes to the odd-core quotient, to its specified subgroup, and
through the supplied SL2 equivalence. If the field order exceeds three,
SL2 is perfect and has a nontrivial projective quotient; that quotient
cannot also be solvable. The odd prime-power condition leaves order three.

Source: ABG II.2 Lemma 1(vi), article p17, and II.3 Definitions 1-2,
article p23. This supplies the source characteristic parameter in the N2
semidihedral specialization without any main classification assumption.
-/

namespace ABG
universe u

public theorem HasSourceQCharacteristicPower.eq_three_of_isSolvable
    {H : Type u} [Group H] [Finite H] [Group.IsSolvable H] {q : ℕ}
    (hq : HasSourceQCharacteristicPower H q) : q = 3 := by
  obtain ⟨F, iF, fF, hF, hq, L, hL, ⟨eL⟩⟩ := hq
  let : Field F := iF
  let : Finite F := fF
  have hSL : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Group.isSolvable_of_surjective (f := eL.toMonoidHom) eL.surjective
  let := hSL
  have hle : Nat.card F ≤ 3 := by
    by_contra hle
    let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
      GorensteinWalter.sl2_isPerfect_of_card_gt_three F (by omega)
    exact Group.IsPerfect.not_isSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
      inferInstance
  obtain ⟨p, n, hp, hpodd, hn, hcard⟩ := hF
  have ho : Odd (Nat.card F) := hcard ▸ hpodd.pow
  have hgt : 1 < Nat.card F := by
    rw [hcard]
    exact Nat.one_lt_pow (by omega) hp.one_lt
  have := Nat.odd_iff.mp ho
  omega

end ABG
