module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.Statements
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Conventions
public import Theory.Mathieu.M22.Properties.OuterCentralizers.DesignAction
public import Theory.GroupTheory.GeneralizedFitting.SolvableNormalKernel
public import BenderSuzuki.MatrixGroups.SuzukiZero

/-!
# Assembly of the two outer M₂₂ centralizer rows

Aschbacher–Smith 16.1.5(5), combined manuscript of 1 March 2004, printed p.1171,
gives E₈-by-L₃(2) and E₁₆-by-Sz(2) as the two outer centralizers. The slash
notation asserts a short exact sequence, without a splitting.

The assembly below lifts an arbitrary abstract outer involution to the faithful
degree-22 design action. The eight-fixed-point row excludes components using
the actual self-centralizing normal elementary kernel. The fixed-point-free
row is solvable because both its elementary kernel and the actual Suzuki matrix
quotient are solvable.

The three model inputs remain explicit: exhaustive fixed-point counts, the
E₈-by-PSL₃(2) extension with its kernel action, and the E₁₆-by-SuzukiMatrixGroup 0
extension. This conditional theorem does not assert those unproved model facts
or complete the source row.
-/

public section

namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu

open Subgroup Theory.GroupTheory Sporadic.Mathieu
open Sporadic.Mathieu.M22OuterCentralizers (fixedPoints)

private theorem no_components_of_elementary_extension
    {C Q : Type*} [Group C] [Group Q] [Finite C] {n : ℕ}
    (E : GroupExtension (Elementary n) C Q)
    (hself : Subgroup.centralizer (E.inl.range : Set C) ≤ E.inl.range) :
    ¬ ∃ K, IsComponent C K := by
  let : Group.IsSolvable E.inl.range :=
    Group.isSolvable_of_surjective E.inl.rangeRestrict_surjective
  rintro ⟨K, hK⟩
  exact not_isComponent_of_solvable_normal_selfCentralizing E.inl.range hself K hK

private theorem no_components_of_szTwo_extension
    {C : Type*} [Group C] [Finite C]
    (E : GroupExtension (Elementary 4) C SzTwo) :
    ¬ ∃ K, IsComponent C K := by
  let : Group.IsSolvable SzTwo := BenderSuzuki.MatrixGroups.suzukiZero_isSolvable
  let : Group.IsSolvable C := Group.isSolvable_of_ker_le_range
    E.inl E.rightHom E.range_inl_eq_ker_rightHom.ge
  rintro ⟨K, hK⟩
  let := hK.2
  let : IsSimpleGroup (K ⧸ Subgroup.center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (Subgroup.center K)).nontrivial
  exact Group.IsPerfect.not_isSolvable K inferInstance

/-- Conditional assembly from the actual geometric coverage and both exact
centralizer extensions. The model inputs must still be discharged. -/
theorem m22_outer_fixedSubgroup_alternatives_of_design_rows
    (hcoverage : ∀ s : m22DesignAut, orderOf s = 2 →
      (s : Equiv.Perm (Fin 22)) ∉ M22 →
      (fixedPoints s).card = 8 ∨ (fixedPoints s).card = 0)
    (height : ∀ s : m22DesignAut, orderOf s = 2 →
      (s : Equiv.Perm (Fin 22)) ∉ M22 → (fixedPoints s).card = 8 →
      ∃ E : GroupExtension (Elementary 3) (M22OuterCentralizers.centralizer s) L3Two,
        Subgroup.centralizer (E.inl.range : Set (M22OuterCentralizers.centralizer s)) ≤
          E.inl.range)
    (hzero : ∀ s : m22DesignAut, orderOf s = 2 →
      (s : Equiv.Perm (Fin 22)) ∉ M22 → (fixedPoints s).card = 0 →
      Nonempty (GroupExtension (Elementary 4) (M22OuterCentralizers.centralizer s) SzTwo))
    (r : MulAut M22) (hr : orderOf r = 2) (hi : ¬ ∃ g, r = MulAut.conj g) :
    (Nonempty (GroupExtension (Elementary 3) r.fixedSubgroup L3Two) ∨
      Nonempty (GroupExtension (Elementary 4) r.fixedSubgroup SzTwo)) ∧
      ¬ ∃ K, IsComponent r.fixedSubgroup K := by
  obtain ⟨s, hs, ho, rfl⟩ :=
    M22OuterCentralizers.exists_outer_design_involution r hr hi
  rcases hcoverage s hs ho with h8 | h0
  · obtain ⟨E, hself⟩ := height s hs ho h8
    exact ⟨Or.inl ⟨E⟩, no_components_of_elementary_extension E hself⟩
  · obtain ⟨E⟩ := hzero s hs ho h0
    exact ⟨Or.inr ⟨E⟩, no_components_of_szTwo_extension E⟩

end CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
