module

public import Theory.Mathieu.M12.Properties.Sylow3
import all Theory.Mathieu.M12.Properties.Sylow3
public import Theory.GroupTheory.PrimeRankWitness

/-!
# An elementary nine in M₁₂

The first and central coordinates of the certified Heisenberg Sylow subgroup
commute and embed C₃ × C₃ in the actual Steiner-system carrier of M₁₂.
The internal import gives this coordinate proof access to the certified
Heisenberg operations without exposing their bodies in the public API.
This supplies the three-rank lower bound used in Aschbacher–Smith, 16.3.10,
combined manuscript of 1 March 2004, printed p.1181.
-/

namespace Sporadic.Mathieu

private abbrev E := Multiplicative (ZMod 3 × ZMod 3)

private def heisenbergPlane : E →* M12Heisenberg where
  toFun a := ⟨a.toAdd.1, 0, a.toAdd.2⟩
  map_one' := rfl
  map_mul' a b := by
    change M12Heisenberg.mk (a.toAdd.1 + b.toAdd.1) 0 (a.toAdd.2 + b.toAdd.2) =
      m12HeisenbergMul ⟨a.toAdd.1, 0, a.toAdd.2⟩ ⟨b.toAdd.1, 0, b.toAdd.2⟩
    simp [m12HeisenbergMul]

private theorem heisenbergPlane_injective : Function.Injective heisenbergPlane := by
  intro a b h
  apply (Multiplicative.toAdd : E ≃ _).injective
  exact Prod.ext (congrArg M12Heisenberg.i h) (congrArg M12Heisenberg.k h)

private theorem plane_cube (a : E) : a ^ 3 = 1 := by
  change Multiplicative.ofAdd (3 • a.toAdd) = Multiplicative.ofAdd 0
  exact congrArg Multiplicative.ofAdd (Prod.ext
    (ZModModule.char_nsmul_eq_zero 3 a.toAdd.1)
    (ZModModule.char_nsmul_eq_zero 3 a.toAdd.2))

/-- The certified Heisenberg subgroup contains an elementary abelian nine. -/
public theorem m12_three_rank_ge_two : 2 ≤ primeRank 3 M12 := by
  let f := m12Sylow3Subgroup.subtype.comp
    (m12Sylow3Subgroup_mulEquiv_heisenberg.symm.toMonoidHom.comp heisenbergPlane)
  exact primeRank_ge_of_elementary_embedding plane_cube
    (by simp [E, Nat.card_eq_fintype_card]) f
    (Subtype.val_injective.comp
      (m12Sylow3Subgroup_mulEquiv_heisenberg.symm.injective.comp heisenbergPlane_injective))

end Sporadic.Mathieu
