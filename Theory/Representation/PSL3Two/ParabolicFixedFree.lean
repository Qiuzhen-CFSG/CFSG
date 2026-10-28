module

public import Theory.Representation.PSL3Two.SmallModules
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals

/-!
# The line-parabolic residual has no natural fixed vectors

The actual embedded two-residual O²(P) of the line parabolic in SL₃(2)
contains a cubic acting without fixed points on its marked plane and a
shear moving the complementary coordinate. Their common fixed space is
zero. The same calculation applies componentwise to two identically marked
natural summands. These are statements about the full residual, not merely
its cyclic Levi subgroup (which does have a fixed vector).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.22, printed p.932, using B.4.8 and C.1.34.
-/

@[expose] public section
open Matrix Representation Subgroup
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace BinaryLinearThree.ParabolicFixedFree

private def lineCubic : Group := ⟨!![0,1,0;1,1,0;0,0,1], by decide⟩
private def lineShear : Group := ⟨!![1,0,1;0,1,0;0,0,1], by decide⟩

private theorem lineCubic_mem : lineCubic ∈ lineA := by decide +kernel
private theorem lineShear_mem : lineShear ∈ lineA := by decide +kernel
private theorem common_fixed : ∀ w : Vector, W lineCubic w = w →
    W lineShear w = w → w = 0 := by decide +kernel

/-- C_W(O²(P)) = 0 for the literal line parabolic and the natural module. -/
theorem natural_fixed_eq_zero (w : Vector)
    (hw : ∀ g ∈ residual lineParabolicSL, W g w = w) : w = 0 := by
  apply common_fixed w
  · exact hw _ (line_residual ▸ lineCubic_mem)
  · exact hw _ (line_residual ▸ lineShear_mem)

/-- Both natural summands use the same group coordinates. -/
theorem doubled_fixed_eq_zero (w : Vector × Vector)
    (hw : ∀ g ∈ residual lineParabolicSL, (W.prod W) g w = w) : w = 0 := by
  apply Prod.ext
  · exact natural_fixed_eq_zero w.1 (fun g hg => congrArg Prod.fst (hw g hg))
  · exact natural_fixed_eq_zero w.2 (fun g hg => congrArg Prod.snd (hw g hg))

/-- The actual fixed submodule vanishes, without a dimension argument. -/
theorem natural_fixedSpace : Representation.BinaryOffender.fixedSpace W
    (residual lineParabolicSL) = ⊥ := by
  apply le_bot_iff.mp
  intro w hw
  exact natural_fixed_eq_zero w (fun g hg => hw ⟨g, hg⟩)

/-- The corresponding fixed submodule in the doubled natural module. -/
theorem doubled_fixedSpace : Representation.BinaryOffender.fixedSpace (W.prod W)
    (residual lineParabolicSL) = ⊥ := by
  apply le_bot_iff.mp
  intro w hw
  exact doubled_fixed_eq_zero w (fun g hg => hw ⟨g, hg⟩)

end BinaryLinearThree.ParabolicFixedFree
