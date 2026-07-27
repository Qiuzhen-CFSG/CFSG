/-
Authors: OpenAI
-/

module

public import Submission.FeitThompson.PFsection1.PFsection1_7_Core

/-!
# Suzuki VI.1.13(v)

Frobenius reciprocity for a class function and induction from a subgroup.
-/

noncomputable section

namespace BenderSuzuki
namespace External
namespace Suzuki
namespace VI

universe u

/-- Suzuki, *Group Theory II*, Chapter 6, (1.13)(v). -/
public theorem suzuki_ch6_proposition_1_13_v
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H]
    (theta : Section1.ClassFunction H) (chi : Section1.ClassFunction G)
    (hchi : Section1.IsClassFunction chi) :
    Section1.scalarProduct G chi (Section1.inducedCF H theta) =
      Section1.scalarProduct H (Section1.subgroupRestriction H chi) theta := by
  exact Section1.inducedClassFunction_frobenius_right H theta chi hchi

end VI
end Suzuki
end External
end BenderSuzuki
