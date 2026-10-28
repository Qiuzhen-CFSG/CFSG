module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Coordinates
public import Theory.Representation.PSL3Two.DoubledFixedSpace

/-!
# The component pointwise fixer in the original doubled marking

Transport the concrete fixed-space calculation through the single supplied
intertwiner. An element of the original K fixes all marked radical-fixed
vectors in U_K exactly when its literal component action lies in R.
This supplies the component part of the pointwise-centralizer condition
in B.2.20; the full T_v fixer still requires the normalizer calculation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.6.20, printed p.931.
-/

public section
open Subgroup Representation BinaryLinearThree Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson
open ComponentSelection
variable {G : Type*} [_root_.Group G] {K L T : Subgroup G} {z v : G}
    {hK : K ≤ Gv v} {hL : Tv T v ≤ normalizer (Lv L v : Set G)}
    {hz : Tv T v ≤ centralizer ({z} : Set G)}

/-- Pointwise fixation in the original U_K is equivalent to membership
in the radical under the same component marking. -/
theorem component_fixes_fixedSpace_iff
    (d : DoubledCoordinates K L T z v hK hL hz) (k : K) :
    (∀ u : UK K L T z v,
      (d.moduleEquiv u).toAdd ∈ fixedSpace (W.prod W) R →
        conjugationAction _ _ (K_normalizes_UK K L T z v hL hz) k u = u) ↔
      d.actionMap k ∈ R := by
  rw [← DoubledFixedSpace.fixes_fixedSpace_iff]
  constructor
  · intro h w hw
    obtain ⟨u, hu⟩ := d.moduleEquiv.surjective (Multiplicative.ofAdd w)
    have hf := h u (by simpa only [hu, toAdd_ofAdd] using hw)
    have he := congrArg (fun x : UK K L T z v => (d.moduleEquiv x).toAdd) hf
    rw [d.equivariant] at he
    simpa only [hu, toAdd_ofAdd, DoubledCoordinates.actionMap,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using he
  · intro h u hu
    apply d.moduleEquiv.injective
    rw [d.equivariant]
    change Multiplicative.ofAdd ((W.prod W) (d.actionMap k) (d.moduleEquiv u).toAdd) =
      Multiplicative.ofAdd (d.moduleEquiv u).toAdd
    rw [h _ hu]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson
