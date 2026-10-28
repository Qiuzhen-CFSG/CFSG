module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.SourceTransport
/-!
# Fixed-complement transport on the same acting group

A subrepresentation with a fixed complementary summand has the same fixed
codimensions and cubic conditions as the original action. Hence its cubic
minimum and its inclusion-minimal starred actors are unchanged on the literal
ambient group.

Source: Aschbacher–Smith D.2.14, printed p.187.
-/

public section
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
open Subgroup Representation.BinaryOffender
open scoped ENNReal
variable {G V : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Removing a pointwise fixed complementary span preserves the cubic minimum
and exactly the starred actors on the original acting group. -/
theorem fixed_complement_transport (W : Subrepresentation ρ)
    (hs : W.toSubmodule ⊔ fixedSpace ρ ⊤ = ⊤) :
    cubicRatio W.toRepresentation = cubicRatio ρ ∧
    (∀ A : Subgroup G, A ∈ QhatStar W.toRepresentation ↔ A ∈ QhatStar ρ) := by
  have hc (A : Subgroup G) : fixedCodim W.toRepresentation A = fixedCodim ρ A := by
    apply (fixedCodim_subrepresentation_eq_iff ρ W A).mpr
    apply top_unique
    rw [← hs]
    exact sup_le_sup_left (fixedSpace_antitone ρ le_top) _
  have hr (A : Subgroup G) : actionRatio W.toRepresentation A = actionRatio ρ A := by
    rw [actionRatio,actionRatio,hc]
  have he : cubicRatio W.toRepresentation = cubicRatio ρ := by
    unfold cubicRatio
    apply iInf_congr
    intro A
    rw [SourceReduction.cubic_fixed_complement_iff ρ W hs A,hr]
  have hmin (A : Subgroup G) : A ∈ QhatMin W.toRepresentation ↔ A ∈ QhatMin ρ := by
    simp only [QhatMin,Set.mem_ofPred_eq,he,hr,
      SourceReduction.cubic_fixed_complement_iff ρ W hs]
  refine ⟨he,fun A => ?_⟩
  simp only [QhatStar,Set.mem_ofPred_eq,hmin]

end CFSG.Quasithin.ChapterD.RatioDecomposition
