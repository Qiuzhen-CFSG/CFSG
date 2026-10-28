module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalUniqueness
public import Theory.GroupTheory.UniqueLocalPointKernel

/-!
# The original A₅ point-action normal core

The established A₅ hyperplane calculation identifies the seed centralizer
with the full module centralizer inside N(V). The two-perfect residual of
the actual normal point kernel therefore fixes V. The faithful local
component and uniqueness over LT kill that residual and give F.9.1(a).
Perfection, the faithful kernel and characteristic two of H are obtained
from the original Context; none is a separate premise here.

The global seed-normalizer containment remains a genuine earlier-source
input; the unique maximal overgroup and module normalizer are proved. The F.9 source consumer uses this
theorem on the same quotient action and the same original subgroups.
Source: Aschbacher–Smith 13.5.7, pp.917–918, and 13.3.18(1), p.894.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- The literal intrinsic normal core required by F.9.1(a). -/
theorem normalCore_point_kernel (d : Context T L V V₁ V₂ V₃)
    (H : Subgroup G) (hline : V₁ ≤ V₃)
    (hTH : (T : Subgroup G) ≤ H) (hHZ : H ≤ centralizer (V₁ : Set G))
    (hcontrol : H ⊓ normalizer (V₃ : Set G) ≤ normalizer (V : Set G))
    (hout : ¬ H ≤ normalizer (L : Set G)) :
    letI : (V₁.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
      (hHZ.trans (Subgroup.centralizer_le_normalizer _))
    (centralizerModulo (⊤ : Subgroup H) (V₃.subgroupOf H) (V₁.subgroupOf H)).normalCore ≤
      pCore 2 H := by
  let := d.perfect
  exact normalCore_seed_kernel_le_twoCore T L V H (normalizer (L : Set G)) V₃ V₁
    (T.isPGroup'.to_le (d.third_le.trans d.chosen.le_sylow))
    (centralizer_third d.flag V₃ d.third_le d.third_card d.third_invariant).le
    (d.third_le.trans (d.chosen.le_sylow.trans hTH)) hline hHZ hcontrol hTH d.normalizes_L
    d.chosen.normalizes d.module_normalizer d.centralizer_eq_core.le d.unique_maximal_overgroup hout (d.characteristic_H H hTH hHZ)

end CFSG.Quasithin.Chapter13.Section05.A5Source
