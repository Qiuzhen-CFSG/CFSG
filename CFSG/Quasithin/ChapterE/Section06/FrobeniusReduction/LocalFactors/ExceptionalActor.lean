module

public import Theory.Representation.RegularCyclicNormalClosure.FrobeniusKernel
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalGeometry

/-!
# The original distinguished-factor action in E.6.25

The induced action of C_M(V₂) fixes V₂ pointwise. The two summands are
complementary, and the decomposition permutes its actual factors and summands.
The complementary pointwise kernel is therefore the distinguished Frobenius
factor, by its self-normalization in the actual GL(V₁). This supplies the
single-summand action used by the exceptional enlargement, with no binary
overgroup hypothesis or replacement representation.

Source: Aschbacher–Smith, E.6.25, printed p.255 (PDF p.266).
-/

public section
open Subgroup
open scoped IsMulCommutative
open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U X : Subgroup G}

/-- The actual complementary centralizer induces only the distinguished factor. -/
theorem exceptional_inducedAutomizer_le_factor [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (j : Fin D.size) (hij : D.distinguished ≠ j)
    (htwo : ∀ k, k = D.distinguished ∨ k = j)
    (hdim : ∀ i, Module.finrank (ZMod 2) (D.summand i) = 3)
    (hmodel : Nonempty (D.factor D.distinguished ≃* Frobenius21.Model)) :
    inducedAutomizer V (M ⊓ centralizer (subspaceGroup (D.summand j) : Set G)) ≤
      D.factor D.distinguished := by
  obtain ⟨e⟩ := hmodel
  have hk := D.pointwise_kernel_le_factor (automizerRepresentation_injective V)
    D.distinguished j hij htwo (two_summands_isCompl h hU hX D j hij htwo)
    (hdim D.distinguished) ((Nat.card_congr e.toEquiv).trans Frobenius21.card_model)
  apply le_trans ?_ hk
  have hn := h.localCentralizer_le_normalizer
    (subspaceGroup_ne_bot_of_finrank_pos (D.summand j) (by rw [hdim]; decide))
    (subspaceGroup_le (D.summand j))
  intro a ha
  refine ⟨mem_top _, ?_⟩
  intro v hv
  have hvF : v ∈ fixedSpace (automizerRepresentation V)
      (inducedAutomizer V (M ⊓ centralizer (subspaceGroup (D.summand j) : Set G))) :=
    (mem_fixedSpace_inducedAutomizer V _ hn v).mpr
      ((le_centralizer_iff.mpr (show M ⊓ centralizer (subspaceGroup (D.summand j) : Set G) ≤
        centralizer (subspaceGroup (D.summand j) : Set G) from inf_le_right))
        ((mem_subspaceGroup (D.summand j) v).mpr hv))
  exact hvF ⟨a, ha⟩

/-- Discharge the exact single-summand action premise of the E.6.25 enlargement. -/
theorem exceptional_distinguished_action [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (hsize : D.size = 2)
    (hdim : ∀ i, Module.finrank (ZMod 2) (D.summand i) = 3)
    (hmodel : Nonempty (D.factor D.distinguished ≃* Frobenius21.Model)) :
    ∀ a ∈ inducedAutomizer V
        (M ⊓ centralizer (subspaceGroup (D.summand (otherIndex hsize D.distinguished)) : Set G)),
      ∃ b ∈ D.factor D.distinguished, ∀ v ∈ D.summand D.distinguished,
        automizerRepresentation V a v = automizerRepresentation V b v := by
  intro a ha
  exact ⟨a, exceptional_inducedAutomizer_le_factor h hU hX D _
    (otherIndex_ne hsize D.distinguished) (eq_or_otherIndex hsize D.distinguished)
    hdim hmodel ha, fun _ _ => rfl⟩
end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors
