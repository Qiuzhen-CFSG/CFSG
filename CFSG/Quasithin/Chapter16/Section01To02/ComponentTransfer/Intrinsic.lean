module

public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Intrinsic.Action
public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Intrinsic.Residual
public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Intrinsic.Index
public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Intrinsic.SplitCover

/-!
# Intrinsic component-transfer deductions

The actual involutory actions, component extraction from two-residuals,
central-cover splitting argument, and Sylow index comparison used to inspect
Aschbacher–Smith 16.1.7(3), printed pp.1172–1173.

The nine-case sieve is still pending the concrete 16.1.2/4/5 tables, their
model action identifications, and numerical centralizer data. No export here
asserts the nine-case conclusion or discharges a model-table premise.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.ComponentTransfer.Intrinsic

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G] {K L : Subgroup G} {t : G}

/-- The centralizer two-residual is the fixed-subgroup two-residual for the
actual induced automorphism used by 16.1.4. -/
noncomputable def centralizerTwoResidualEquivFixed (hn : t ∈ normalizer K) :
    pResidual 2 (centralizerIn K t) ≃* pResidual 2 (action hn).fixedSubgroup :=
  ((centralizerEquivFixed hn).subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_pResidual 2 (centralizerEquivFixed hn)))

/-- A quasisimple endpoint in the intrinsic two-residual table identifies L
itself. The table isomorphism and quasisimplicity remain explicit inputs. -/
noncomputable def componentEquivFixedResidualModel [Finite G]
    (hn : t ∈ normalizer K) (hL : IsComponentIn L (centralizerIn K t))
    {M : Type*} [Group M] [IsQuasisimple M]
    (e : pResidual 2 (action hn).fixedSubgroup ≃* M) : L ≃* M :=
  componentEquivModel hL ((centralizerTwoResidualEquivFixed hn).trans e)

end CFSG.Quasithin.Chapter16.ComponentTransfer.Intrinsic
