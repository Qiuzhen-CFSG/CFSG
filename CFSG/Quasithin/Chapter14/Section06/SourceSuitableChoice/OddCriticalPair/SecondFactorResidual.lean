module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.TerminalGeometry
public import Theory.GroupTheory.PResidual.IndexTwoRestriction

/-!
# The original second factor inside the full quotient centralizer

The group used in the terminal interface is P = C_H(u mod Z), rather than
the original factor H2. Commutation modulo Z places H2 inside that literal
kernel. If H2 has index two there, their embedded two-residuals agree.
Consequently the seed coordinates calculated with O^2(H2) give coordinates
and rank four for O^2(P), and this residual centralizes u itself.

The orthogonal action must still supply the commutation and index statements
and construct the coordinates. No action or rank assertion follows merely
from the names of the two groups.

Source: Aschbacher--Smith 14.6.17(3--5), printed pp.1035--1036.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
variable {G : Type*} [Group G] [Finite G]
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)

/-- Commutation on the original central quotient places the actual second
factor inside P, without replacing P by that factor. -/
theorem second_factor_le_suitable_kernel
    (u : G) (hu : u ∈ D.UH) (H2 : Subgroup G) (hH2 : H2 ≤ D.H)
    (hfix : ⁅zpowers u,H2⁆ ≤ D.V₁) : H2 ≤ h.kernel (zpowers u) := by
  have huH : zpowers u ≤ D.H := zpowers_le.mpr (h.UH_le_H hu)
  intro x hx
  apply (h.mem_kernel_iff huH).mpr
  exact ⟨hH2 hx,fun a ha => hfix (commutator_mem_commutator ha hx)⟩

/-- The original residual and that of the full quotient centralizer agree
when the orthogonal stabilizer calculation gives relative index two. -/
theorem second_factor_residual_eq_suitable_kernel
    (u : G) (hu : u ∈ D.UH) (H2 : Subgroup G) (hH2 : H2 ≤ D.H)
    (hfix : ⁅zpowers u,H2⁆ ≤ D.V₁)
    (hi : H2.relIndex (h.kernel (zpowers u)) = 2) :
    (pResidual 2 H2).map H2.subtype =
      (pResidual 2 (h.kernel (zpowers u))).map (h.kernel (zpowers u)).subtype :=
  embedded_twoResidual_eq_of_relIndex_two
    (second_factor_le_suitable_kernel h u hu H2 hH2 hfix) hi

/-- Apply the second-factor calculation to the literal terminal coordinates.
Both rank four and centralization concern R = O^2(P) inside the original G. -/
theorem second_factor_coordinates_for_suitable_kernel
    (u : G) (hu : u ∈ D.UH) (H2 : Subgroup G) (hH2 : H2 ≤ D.H)
    (hfix : ⁅zpowers u,H2⁆ ≤ D.V₁)
    (hi : H2.relIndex (h.kernel (zpowers u)) = 2)
    (c : SourceResidualSpanCoordinates D.V D.V₁ ((pResidual 2 H2).map H2.subtype)) :
    Nonempty (SourceResidualSpanCoordinates D.V D.V₁
        ((pResidual 2 (h.kernel (zpowers u))).map (h.kernel (zpowers u)).subtype)) ∧
      primeRank 2 (conjugateSpanBy D.V
        ((pResidual 2 (h.kernel (zpowers u))).map (h.kernel (zpowers u)).subtype)) = 4 ∧
      (pResidual 2 (h.kernel (zpowers u))).map (h.kernel (zpowers u)).subtype ≤
        centralizer ({u} : Set G) := by
  have he := second_factor_residual_eq_suitable_kernel h u hu H2 hH2 hfix hi
  have cP : SourceResidualSpanCoordinates D.V D.V₁
      ((pResidual 2 (h.kernel (zpowers u))).map (h.kernel (zpowers u)).subtype) := he ▸ c
  exact ⟨⟨cP⟩,cP.rank_four,suitable_parabolic_residual_centralizes h u hu _ le_rfl⟩

end CFSG.Quasithin.Chapter14.Section06
