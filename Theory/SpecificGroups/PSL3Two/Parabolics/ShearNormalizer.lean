module

public import Theory.SpecificGroups.PSL3Two.Parabolics.LineCore
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals
public import Theory.GroupTheory.LocalNormalizerUniqueness
import Mathlib.Tactic.FinCases

/-!
# Normalizer of the binary shear radical

The shear four-group in SL₃(2) fixes exactly the coordinate plane v₂ = 0.
Its normalizer preserves that plane and is the full line parabolic. The
reverse inclusion follows from the previously identified parabolic two-core.
The parabolic has order 24 and its embedded two-residual has order 12.
Conjugation transports both statements without changing the matrix marking.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, the concrete
SL₃(2) radical-normalizer calculation used in Lemma 13.7.4(1), printed p.938,
and Lemma 13.8.19, printed p.953.
-/

public section
open Subgroup Representation BinaryLinearThree Matrix
namespace Matrix.PSL3Two

private theorem fixed_shear_radical_iff (v : Vector) :
    (∀ r ∈ R, (r : BinaryLinearThree.Group) • v = v) ↔ v 2 = 0 := by
  constructor
  · intro h
    have he := congrFun (h (shear (Multiplicative.ofAdd (1, 0))) ⟨_, rfl⟩) 0
    change (!![1,0,1; 0,1,0; 0,0,1].mulVec v) 0 = v 0 at he
    have hv : v 0 + v 2 = v 0 := by
      simpa [mulVec, dotProduct, Fin.sum_univ_three] using he
    exact add_left_cancel (hv.trans (add_zero (v 0)).symm)
  · intro hv r hr
    obtain ⟨c, rfl⟩ := hr
    change !![1,0,c.toAdd.1; 0,1,c.toAdd.2; 0,0,1].mulVec v = v
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three, hv]

/-- The shear four-group has full normalizer equal to the line parabolic. -/
theorem normalizer_shear_radical :
    normalizer (R : Set SL) = lineParabolicSL := by
  apply le_antisymm
  · intro g hg
    rw [lineParabolicSL, MulAction.mem_stabilizer_set' (Set.toFinite _)]
    intro v hv
    apply (fixed_shear_radical_iff _).mp
    intro r hr
    have hr' : g⁻¹ * r * g ∈ R := by
      simpa using (mem_normalizer_iff.mp
        ((normalizer (R : Set SL)).inv_mem hg) r).mp hr
    have he := (fixed_shear_radical_iff v).mpr hv _ hr'
    have he' := congrArg (fun w : Vector => g • w) he
    simpa only [mul_smul, smul_inv_smul] using he'
  · rw [← lineParabolicSL_pCoreIn_two_eq_R]
    exact lineParabolicSL.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

theorem card_normalizer_shear_radical :
    Nat.card (normalizer (R : Set SL)) = 24 := by
  rw [normalizer_shear_radical, card_lineParabolicSL]

theorem card_residual_normalizer_shear_radical :
    Nat.card ((pResidual 2 (normalizer (R : Set SL))).map
      (normalizer (R : Set SL)).subtype) = 12 := by
  rw [normalizer_shear_radical]
  exact MarkedAutomorphisms.card_line_residual

theorem normalizer_shear_conjugate (g : SL) :
    normalizer (R.map (MulAut.conj g).toMonoidHom : Set SL) =
      lineParabolicSL.map (MulAut.conj g).toMonoidHom := by
  rw [← map_equiv_normalizer_eq, normalizer_shear_radical]

theorem card_normalizer_shear_conjugate (g : SL) :
    Nat.card (normalizer (R.map (MulAut.conj g).toMonoidHom : Set SL)) = 24 := by
  rw [normalizer_shear_conjugate, card_map_of_injective (MulAut.conj g).injective,
    card_lineParabolicSL]

theorem card_residual_normalizer_shear_conjugate (g : SL) :
    Nat.card ((pResidual 2 (normalizer
      (R.map (MulAut.conj g).toMonoidHom : Set SL))).map
      (normalizer (R.map (MulAut.conj g).toMonoidHom : Set SL)).subtype) = 12 := by
  rw [← map_equiv_normalizer_eq]
  rw [← map_embedded_pResidual, card_map_of_injective (MulAut.conj g).injective]
  exact card_residual_normalizer_shear_radical

end Matrix.PSL3Two
