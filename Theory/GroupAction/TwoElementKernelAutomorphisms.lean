module
public import Theory.GroupAction.HomomorphismFixingAutomorphisms
import Mathlib.Tactic

/-!
# A two-group automorphism kernel over a kernel of order at most two

An automorphism preserving a homomorphism with kernel of order at most two
fixes that kernel pointwise. The displacement embedding therefore makes
all such automorphisms a two-group. This is used on the literal map from
the tilded module to the central quotient in original 14.3.13.
-/

public section
namespace MonoidHom
variable {P D : Type*} [Group P] [Finite P] [Group D]

theorem isPGroup_fixingAut_of_kernel_card_le_two (d : P →* D)
    (hc : Nat.card d.ker ≤ 2) : IsPGroup 2 d.fixingAut := by
  have hp : IsPGroup 2 d.ker := by
    by_cases he : Nat.card d.ker = 1
    · let : Subsingleton d.ker := Finite.card_le_one_iff_subsingleton.mp he.le
      exact IsPGroup.of_subsingleton 2 _
    · exact IsPGroup.of_card (n := 1) (by have := Nat.card_pos (α := d.ker); simpa using (show Nat.card d.ker = 2 by omega))
  let : Subsingleton (MulAut d.ker) := by
    refine ⟨fun a b => ?_⟩
    have hfix : ∀ (a : MulAut d.ker) (x : d.ker), a x = x := by
      intro a x
      by_cases he : Nat.card d.ker ≤ 1
      · let : Subsingleton d.ker := Finite.card_le_one_iff_subsingleton.mp he
        exact Subsingleton.elim _ _
      have ht : Nat.card d.ker = 2 := by omega
      obtain ⟨z,_,hz⟩ := (Nat.card_eq_two_iff' (1 : d.ker)).mp ht
      by_cases hx : x = 1
      · simp [hx]
      have hax : a x ≠ 1 := fun h => hx (a.injective (h.trans a.map_one.symm))
      exact (hz _ hax).trans (hz _ hx).symm
    exact MulEquiv.ext (fun x => (hfix a x).trans (hfix b x).symm)
  exact d.isPGroup_fixingAut hp (IsPGroup.of_subsingleton 2 _)
end MonoidHom
