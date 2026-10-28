module
public import CFSG.Quasithin.Chapter5.A5Source.Generation
public import CFSG.Quasithin.Chapter5.A5Source.PointCentralizer

/-!
# The original A5 Baumann normalizer bound

The original point-centralizer control produces elementary crossing cores.
The replacement-conjugator argument makes them generate Baum(T), and the
marked five-point action identifies its two dihedral factors. The odd
normalizer residual then preserves the original core, contradicting escape
from N_G(L). Thus N_G(Baum(T))≤N_G(L).

The source wrapper takes only the genuine earlier 4.3.2 uniqueness over L;
no generation, crossing, elementary-core or Baumann bound is assumed.
Uniqueness over LT alone does not discharge that earlier premise.
Source: Aschbacher–Smith 5.1.7(1), printed pp.633–634.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter5.A5Source
open Chapter13.Section05.A5Source ChapterB
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- The full original A5 Baumann argument from its point-centralizer input. -/
theorem baumann_normalizer_of_point_centralizers
    (d : Context T L V V₁ V₂ V₃)
    (hc : ∀ x ∈ baumann (T : Subgroup G) ⊓ centralizer (L : Set G), x ≠ 1 →
      centralizer ({x} : Set G) ≤ normalizer (L : Set G)) :
    normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  by_contra hout
  obtain ⟨g,hg,hQ,hcross,hgen⟩ := exists_baumann_generated_elementary_core d hout hc
  exact baumann_normalizer_of_generated_elementary_cores d hout hQ g hg hcross hgen

/-- Source 5.1.7(1), retaining only the genuine earlier 4.3.2 uniqueness input. -/
theorem baumann_normalizer_of_source_uniqueness
    (d : Context T L V V₁ V₂ V₃)
    (hu : Chapter4.UniqueMaximalOvergroup L (normalizer (L : Set G))) :
    normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  apply baumann_normalizer_of_point_centralizers d
  intro x hx hne
  exact point_centralizer_of_source_uniqueness hu hx.1.1 hx.2 hne

end CFSG.Quasithin.Chapter5.A5Source
