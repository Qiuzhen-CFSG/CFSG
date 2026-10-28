module
public import Theory.GroupTheory.PResidual.Restriction
public import Mathlib.GroupTheory.IndexNormal

/-!
# Residuals of subgroups of relative index two

A subgroup of index two is normal and contains the two-residual. Restricting
to it therefore preserves the embedded residual. The containment is proved
in the larger subgroup, rather than assuming normality in the ambient group.

Source application: the factor H2 and the full quotient centralizer
C_H(u mod Z) in Aschbacher--Smith 14.6.17, printed p.1036.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Index two in P suffices; no normality of A in G is asserted. -/
theorem embedded_twoResidual_eq_of_relIndex_two
    {A P : Subgroup G} (hAP : A ≤ P) (hi : A.relIndex P = 2) :
    (pResidual 2 A).map A.subtype = (pResidual 2 P).map P.subtype := by
  have hi' : (A.subgroupOf P).index = 2 := hi
  let : (A.subgroupOf P).Normal := (A.subgroupOf P).normal_of_index_eq_two hi'
  have hquot : IsPGroup 2 (P ⧸ A.subgroupOf P) :=
    IsPGroup.of_card (n := 1) (by simpa only [← index_eq_card, pow_one] using hi')
  apply embedded_pResidual_eq_of_le_of_residual_le 2 hAP
  rintro x ⟨y,hy,rfl⟩
  exact (show pResidual 2 P ≤ A.subgroupOf P from sInf_le ⟨inferInstance,hquot⟩) hy

end Subgroup
