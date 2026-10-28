module

public import Theory.SpecificGroups.PSL3Three.SylowFixers
public import Theory.SpecificGroups.PSL3Three.EvenLocals
public import Theory.GroupAction.InnerSylowFixers

/-!
# Inner implementations of pointwise Sylow fixers in PSL₃(3)

The proved two-element bound for the full Sylow fixer, together with the
nontrivial Sylow center and centerlessness, identifies every fixer as inner
by an element of that very Sylow subgroup. The canonical projective
isomorphism keeps the original Sylow subtype. This is the PSL₃(3) input to
Aschbacher--Smith 2.5.8(4), printed pp.556--557.
-/

public section
open Subgroup
namespace Matrix.PSL3Three

/-- Every pointwise fixer is conjugation by a central element of the specified Sylow. -/
theorem sylow_fixed_inner (P : Sylow 2 PSL) (a : MulAut PSL)
    (ha : ∀ x ∈ P, a x = x) : ∃ z ∈ P, a = MulAut.conj z := by
  have hPc : Nat.card P = 16 := by
    rw [P.card_eq_multiplicity, card_PSL]
    decide +kernel
  let : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hZ : center PSL = ⊥ := by
    apply eq_bot_iff.mpr
    intro g hg
    have hh : equiv.symm g ∈ center SL := by
      apply mem_center_iff.mpr
      intro x
      apply equiv.injective
      simpa only [map_mul, equiv.apply_symm_apply] using mem_center_iff.mp hg (equiv x)
    have hg1 : equiv.symm g = 1 := by simpa only [center_eq_bot, mem_bot] using hh
    exact equiv.symm.injective (hg1.trans (map_one equiv.symm).symm)
  obtain ⟨z, hz⟩ := Theory.GroupAction.sylow_fixer_inner_of_card_le_two hZ P
    (SylowFixers.sylow_fixer_card_le_two P) a ha
  exact ⟨z.val, z.val.property, hz⟩

end Matrix.PSL3Three
