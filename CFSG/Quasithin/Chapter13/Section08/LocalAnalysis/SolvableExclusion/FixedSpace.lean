module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Elementary

/-!
# The fixed-space calculation at the end of 13.8.13

Write F_H for the inverse image of the Uγ-fixed space on U_H/V₁. If D_H
has index two and [U_H,Uγ] is not contained in A₁V₁, then F_H lies in D_H.
Indeed otherwise the two subgroups generate U_H and bound its commutator
by A₁V₁. Once V₁ and A₁ are disjoint, F_H is the actual centralizer C_H.

All normality assumptions are relative normalization statements for U_H.
No subgroup of the ambient simple group is asserted normal there.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), the final
paragraph of 13.8.13, printed p.951. The preceding representation calculation
must still supply the index and the noncontainment of the moved space.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion
open Subgroup
variable {G : Type*} [Group G]

/-- The inverse image of C_{Ũ_H}(Uγ). Its denominator is V₁, not A₁. -/
def fixedPreimage (UH Uγ V₁ : Subgroup G) : Subgroup G :=
  commutatorPreimage UH Uγ V₁

/-- The fixed-space preimage is contained in the source hyperplane D_H. -/
theorem fixedPreimage_le_DH
    (UH Uγ A₁ V₁ : Subgroup G)
    (hindex : (Source.DH UH Uγ A₁).relIndex UH = 2)
    (hnA : UH ≤ normalizer (A₁ : Set G))
    (hnV : UH ≤ normalizer (V₁ : Set G))
    (hmoved : ¬ ⁅UH, Uγ⁆ ≤ A₁ ⊔ V₁) :
    fixedPreimage UH Uγ V₁ ≤ Source.DH UH Uγ A₁ := by
  let C := commutatorPreimage UH Uγ (A₁ ⊔ V₁)
  have hn : UH ≤ normalizer (A₁ ⊔ V₁ : Subgroup G) :=
    (le_inf hnA hnV).trans (normalizer_inf_normalizer_le_normalizer_sup A₁ V₁)
  have hD : Source.DH UH Uγ A₁ ≤ C :=
    le_commutatorPreimage (commutatorPreimage_le _ _ _)
      ((commutator_commutatorPreimage_le _ _ _ hnA).trans le_sup_left)
  have hF : fixedPreimage UH Uγ V₁ ≤ C :=
    le_commutatorPreimage (commutatorPreimage_le _ _ _)
      ((commutator_commutatorPreimage_le _ _ _ hnV).trans le_sup_right)
  have hnot : ¬ UH ≤ C := by
    intro h
    exact hmoved ((commutator_mono h le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hn))
  have he := flag_intersection_of_index_two UH (Source.DH UH Uγ A₁) C
    (le_inf (commutatorPreimage_le _ _ _) hD) hindex hnot
  rw [inf_eq_right.mpr (commutatorPreimage_le _ _ _)] at he
  exact hF.trans he.symm.le

/-- Disjoint source lines remove the quotient ambiguity: the inverse image
of the fixed space is precisely the centralizer in U_H. -/
theorem fixedPreimage_eq_centralizer
    (UH Uγ A₁ V₁ : Subgroup G)
    (hindex : (Source.DH UH Uγ A₁).relIndex UH = 2)
    (hnA : UH ≤ normalizer (A₁ : Set G))
    (hnV : UH ≤ normalizer (V₁ : Set G))
    (hmoved : ¬ ⁅UH, Uγ⁆ ≤ A₁ ⊔ V₁)
    (hdis : Disjoint V₁ A₁) :
    fixedPreimage UH Uγ V₁ = UH ⊓ centralizer (Uγ : Set G) := by
  have hF := fixedPreimage_le_DH UH Uγ A₁ V₁ hindex hnA hnV hmoved
  apply le_antisymm
  · refine le_inf (commutatorPreimage_le _ _ _) ?_
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [← disjoint_iff.mp hdis]
    exact le_inf (commutator_commutatorPreimage_le _ _ _ hnV)
      ((commutator_mono hF le_rfl).trans
        (commutator_commutatorPreimage_le _ _ _ hnA))
  · apply le_commutatorPreimage inf_le_left
    exact (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le

/-- The source factor U₂, which centralizes Uγ modulo V₁, centralizes Uγ
itself; its commutator with Vγ is consequently supported on A₁. -/
theorem second_factor_commutator_le_line
    (UH Uγ Vγ A₁ V₁ U₂ : Subgroup G)
    (hindex : (Source.DH UH Uγ A₁).relIndex UH = 2)
    (hnA : UH ≤ normalizer (A₁ : Set G))
    (hnV : UH ≤ normalizer (V₁ : Set G))
    (hmoved : ¬ ⁅UH, Uγ⁆ ≤ A₁ ⊔ V₁)
    (hdis : Disjoint V₁ A₁) (hU₂ : U₂ ≤ UH) (hfixed : ⁅U₂, Uγ⁆ ≤ V₁)
    (h13737 : ⁅UH ⊓ centralizer (Uγ : Set G), Vγ⁆ ≤ A₁) :
    ⁅U₂, Uγ⁆ = ⊥ ∧ ⁅U₂, Vγ⁆ ≤ A₁ := by
  have hF : U₂ ≤ fixedPreimage UH Uγ V₁ := le_commutatorPreimage hU₂ hfixed
  rw [fixedPreimage_eq_centralizer UH Uγ A₁ V₁ hindex hnA hnV hmoved hdis] at hF
  exact ⟨commutator_eq_bot_iff_le_centralizer.mpr (hF.trans inf_le_right),
    (commutator_mono hF le_rfl).trans h13737⟩

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion
end
