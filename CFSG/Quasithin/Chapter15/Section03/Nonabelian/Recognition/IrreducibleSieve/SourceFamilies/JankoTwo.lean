module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.MarkedAutomorphism
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InvolutionFixedCubic

/-!
# The Hall--Janko source component exclusion

The actual marked component automorphism fixes an order-three element by the
certified Hall--Janko involution fixed-group calculation. Its image under the
literal component inclusion contradicts the original centralizer restriction.

Source: Aschbacher--Smith, 15.3.58, printed p.1149.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

/-- The actual simple-component J₂ branch of 15.3.58 is impossible. -/
theorem SourceData.not_j2_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (e : K ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  obtain ⟨a, ha, _, hfixed⟩ := h.marked_automorphism hK e
  obtain ⟨d, hd, hda⟩ := Sporadic.LeechRelated.J2.exists_fixed_cubic_of_involution a ha
  exact h.no_model_cubic_commuting e d hd ((hfixed d).mp hda)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
