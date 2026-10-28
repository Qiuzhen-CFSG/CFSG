module
public import Theory.SpecificGroups.PSL3Two.Parabolics.LineCore
public import Theory.Representation.PSL3Two.FanoLocalStructure.ParabolicSpaces
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual

/-!
# Dual-natural displacement under the line-parabolic radical

The literal two-core of the line stabilizer in SL₃(2) consists of four
shears. On the dual-natural three-space every displacement lies in the
line fixed by that parabolic. A certificate on four shears and eight vectors
proves this in graph coordinates; the contragredient equivalence transfers
it to the actual dual representation.

This is the constituent calculation in Aschbacher–Smith 13.4.15,
printed p.912, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Representation Representation.BinaryOffender Matrix.PSL3Two
namespace BinaryLinearThree
open AutomorphismAction FanoLocalStructure.ParabolicSpaces

private theorem shear_dual_displacement : ∀ c : Multiplicative (ZMod 2 × ZMod 2), ∀ v : Vector,
    W (graph (shear c)) v - v = 0 ∨
      W (graph (shear c)) v - v = ![0,0,1] := by
  decide +kernel

/-- The line radical displaces the dual-natural space into its parabolic fixed line. -/
theorem dual_line_radical_displacement (r : Group)
    (hr : r ∈ lineParabolicSL.pCoreIn 2) (v : Module.Dual (ZMod 2) Vector) :
    W.dual r v - v ∈ fixedSpace W.dual lineParabolicSL := by
  rw [lineParabolicSL_pCoreIn_two_eq_R] at hr
  obtain ⟨c,rfl⟩ := hr
  let e := graphNaturalDual
  obtain ⟨w,rfl⟩ := e.surjective v
  have he (g : Group) (x : Vector) : e (W (graph g) x) = W.dual g (e x) :=
    LinearMap.congr_fun (e.isIntertwining' g) x
  change W.dual (shear c) (e w) - e w ∈ fixedSpace W.dual lineParabolicSL
  rw [←he,←map_sub]
  have hw : W (graph (shear c)) w - w ∈
      fixedSpace (W.comp graph.toMonoidHom) lineParabolicSL := by
    rcases shear_dual_displacement c w with hz | hz
    · rw [hz]; exact Submodule.zero_mem _
    · rw [hz]
      intro g
      exact congrArg (fun x : Fano.Line => x.normal.val)
        ((mem_lineParabolic_iff_fixes_line g.val).mp g.property)
  intro g
  exact (he g.val _).symm.trans (congrArg e (hw g))
end BinaryLinearThree
