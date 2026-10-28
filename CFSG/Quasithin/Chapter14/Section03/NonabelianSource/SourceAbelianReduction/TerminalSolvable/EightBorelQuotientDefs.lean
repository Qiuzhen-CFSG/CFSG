module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.Defs

/-!
# The component map in the L₂(8) kernel comparison

The map is restriction of the original H → H/C_H(U/Z(U)), transported
from K.subgroupOf H back to K. Once its kernel is proved to equal O₂(K),
the first isomorphism theorem gives the intrinsic two-core quotient and
retains its equation on every original element. No kernel comparison is
asserted in this module.

Source: Aschbacher--Smith 14.3.15, printed p.994.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G}

/-- Restriction of the literal dotted projection to the original component. -/
noncomputable def componentDotMap (F : InvariantFlag T V 2)
    {K : Subgroup G} (hKH : K ≤ F.H) : K →* F.terminalDot K :=
  ((QuotientGroup.mk' F.terminalHatAction.ker).subgroupMap (K.subgroupOf F.H)).comp
    (subgroupOfEquivOfLe hKH).symm.toMonoidHom

theorem componentDotMap_surjective (F : InvariantFlag T V 2)
    {K : Subgroup G} (hKH : K ≤ F.H) : Function.Surjective (componentDotMap F hKH) :=
  ((QuotientGroup.mk' F.terminalHatAction.ker).subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe hKH).symm.surjective

theorem componentDotMap_apply (F : InvariantFlag T V 2)
    {K : Subgroup G} (hKH : K ≤ F.H) (k : K) :
    (componentDotMap F hKH k : F.TerminalHdot) =
      QuotientGroup.mk' F.terminalHatAction.ker (inclusion hKH k) := rfl

/-- The canonical equivalence obtained from the still-separate kernel equality. -/
noncomputable def componentCoreQuotientEquivDot (F : InvariantFlag T V 2)
    {K : Subgroup G} (hKH : K ≤ F.H)
    (hk : (componentDotMap F hKH).ker = pCore 2 K) :
    (K ⧸ pCore 2 K) ≃* F.terminalDot K :=
  (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (componentDotMap F hKH)
      (componentDotMap_surjective F hKH))

theorem componentCoreQuotientEquivDot_apply (F : InvariantFlag T V 2)
    {K : Subgroup G} (hKH : K ≤ F.H)
    (hk : (componentDotMap F hKH).ker = pCore 2 K) (k : K) :
    (componentCoreQuotientEquivDot F hKH hk (QuotientGroup.mk' (pCore 2 K) k) :
      F.TerminalHdot) = QuotientGroup.mk' F.terminalHatAction.ker (inclusion hKH k) := rfl

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
