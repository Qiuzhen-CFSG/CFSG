module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.Statements
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.LocalKernel
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.StructureTransport
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure.KernelWitnesses
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure.KernelBound
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure.Quotient

/-!
# Assembly of the central HS involution extension

The embedded quaternion and cyclic factors constructed in `KernelWitnesses`
generate a subgroup of order 64 in the actual pair kernel. The exhaustive bound
in `KernelBound` proves that this subgroup is the full kernel. Independently,
`Quotient` identifies the quotient with S₅ through the action on the five
independent four-sets of the fixed-pair graph. Normality is inside the actual
local group, and `localGroup_zero_eq_centralizer` identifies that entire group
with the centralizer of the specified carrier involution `e0`.

Thus the centralizer has a normal (Q₈ * Q₈) * C₄ with quotient S₅, with no
additional premise or splitting assertion. Its order 7680 follows from this
structure. The quaternion factors are actual embedded copies, retaining the
source specification despite the dihedral presentation in GLS3.

Source: Aschbacher–Smith 16.1.5(10), printed p.1172, and GLS3 Table 5.3m.
The other involution classes and the complete 16.1.5(10) assembly are separate.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner
open Subgroup
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore

attribute [local instance] core_normal

/-- Assemble the exact extension from the two remaining concrete model calculations. -/
theorem centralizer_coreExtension_of_card_and_quotient
    (hcard : Nat.card core ≤ 64)
    (hquot : Nonempty ((localGroup 0) ⧸ core ≃* S5)) :
    IsHSCoreExtension (centralizer ({e0} : Set Carrier)) := by
  apply coreExtension_transport (MulEquiv.subgroupCongr localGroup_zero_eq_centralizer)
  exact ⟨core, core_normal, CoreStructure.core_shape_of_card_le hcard, hquot⟩

/-- The full centralizer of the specified HS involution has the exact source
extension, with embedded quaternion/cyclic kernel and actual S₅ quotient. -/
theorem centralizer_coreExtension :
    IsHSCoreExtension (centralizer ({e0} : Set Carrier)) :=
  centralizer_coreExtension_of_card_and_quotient
    CoreStructure.core_card_le CoreStructure.core_quotient_equiv_s5

/-- The order of the full representative centralizer, derived from its extension. -/
theorem centralizer_card : Nat.card (centralizer ({e0} : Set Carrier)) = 7680 :=
  coreExtension_card centralizer_coreExtension

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner
