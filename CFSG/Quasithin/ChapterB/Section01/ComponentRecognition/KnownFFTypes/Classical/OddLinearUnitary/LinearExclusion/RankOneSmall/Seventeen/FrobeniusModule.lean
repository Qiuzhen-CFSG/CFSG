module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Seventeen.Reduction
public import Theory.Representation.SeventeenFrobeniusModule

/-!
# The Frobenius-module calculation in the original PSL₂(17) source action

The actual central-quotient witness and the degree upper bound give degree eight.
For an explicit pair of elements with the `17:8` relations, the faithful source
action therefore has fixed dimensions one, two and four, and displacements
seven, six and four. The last theorem supplies the two numerical premises of
`source_exclusion_of_local_calculations` on these same elements in the original
group. The independent fusion and centralizer-product geometry remains explicit;
constructing the pair and discharging that geometry belongs to the Seventeen
assembly owner.

Source: Aschbacher--Smith K.2, printed p.453; Guralnick--Malle,
*Classification of 2F-modules I*, Proposition 4.1, manuscript p.9.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Seventeen
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
include h

/-- Fixed dimensions for the literal Frobenius pair in the source group. -/
theorem source_frobenius_fixed_dimensions
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 17)
    (hd : Module.finrank (ZMod 2) V ≤ 8)
    (x r : G) (hx : orderOf x = 17) (hr : orderOf r = 8)
    (hrel : r * x * r⁻¹ = x ^ 2) :
    Module.finrank (ZMod 2) (fixedSpace ρ (zpowers r)) = 1 ∧
    Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (r ^ 2))) = 2 ∧
    Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (r ^ 4))) = 4 :=
  SeventeenFrobeniusModule.fixed_dimensions ρ h.faithful
    (source_degree_eq_eight ρ h hm hd) x r hx hr hrel

/-- The complement displacements are seven, six and four in the original action. -/
theorem source_frobenius_fixed_codimensions
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 17)
    (hd : Module.finrank (ZMod 2) V ≤ 8)
    (x r : G) (hx : orderOf x = 17) (hr : orderOf r = 8)
    (hrel : r * x * r⁻¹ = x ^ 2) :
    fixedCodim ρ (zpowers r) = 7 ∧
    fixedCodim ρ (zpowers (r ^ 2)) = 6 ∧
    fixedCodim ρ (zpowers (r ^ 4)) = 4 :=
  SeventeenFrobeniusModule.fixed_codimensions ρ h.faithful
    (source_degree_eq_eight ρ h hm hd) x r hx hr hrel

/-- The source's single size-eight unipotent block, expressed as nilpotence
and indecomposability of the polynomial module with variable acting by `ρ r`. -/
theorem source_frobenius_single_block
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 17)
    (hd : Module.finrank (ZMod 2) V ≤ 8)
    (x r : G) (hx : orderOf x = 17) (hr : orderOf r = 8)
    (hrel : r * x * r⁻¹ = x ^ 2) :
    (ρ r - 1) ^ 8 = 0 ∧
      Module.IsIndecomposable (Polynomial (ZMod 2)) (Module.AEval' (ρ r)) :=
  SeventeenFrobeniusModule.single_block ρ h.faithful
    (source_degree_eq_eight ρ h hm hd) x r hx hr hrel

/-- Apply the source actor contradiction with both Frobenius displacement
premises discharged. Fusion and centralizer-product geometry remain explicit. -/
theorem source_exclusion_of_frobenius_pair
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 17)
    (hd : Module.finrank (ZMod 2) V ≤ 8)
    (x r : G) (hx : orderOf x = 17) (hr : orderOf r = 8)
    (hrel : r * x * r⁻¹ = x ^ 2)
    (hfusion : ∀ t : G, orderOf t = 2 → IsConj (r ^ 4) t)
    (hproducts : ∀ A : Subgroup G, IsElementaryTwo A → rank A = 2 →
      ∃ t g a b : G, t ∈ A ∧ orderOf t = 2 ∧ Commute g t ∧ a ∈ A ∧ b ∈ A ∧
        IsConj (r ^ 2) (a * (g * b * g⁻¹))) :
    2 < cubicRatio ρ := by
  obtain ⟨_, htwo, hfour⟩ := source_frobenius_fixed_codimensions ρ h hm hd x r hx hr hrel
  exact source_exclusion_of_local_calculations ρ h hm r hfour htwo hfusion hproducts

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Seventeen
