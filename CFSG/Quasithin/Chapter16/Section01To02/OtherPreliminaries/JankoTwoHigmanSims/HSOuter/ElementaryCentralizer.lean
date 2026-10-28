module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.Representatives
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.KernelExclusion
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer.Coverage
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer.Structure

/-!
# The elementary outer HS centralizer calculation

The centralizer of `elementaryPermutation` inside the exact degree-100 HS
carrier has the concrete normal subgroup `ElementaryCentralizer.Q`, identified
with E16 by `ElementaryCentralizer.kernelEquiv`. Exhaustive stabilizer-chain
coverage discharges the premise of the five-point conjugation calculation,
giving an actual quotient isomorphism with S5 and proving that Q contains its
centralizer. The same Q witnesses both the extension and the kernel-action
condition, so this centralizer has no components.

No centralizer order or splitting is assumed. Normality and self-centralization
are relative to this centralizer. Exhaustive fusion and the representative's
normalizer membership belong to the outer-centralizer assembly.

Source: Aschbacher–Smith 16.1.5(10), printed pp.1172–1173; GLS3 Table 5.3m,
class 2C, and the component exclusion used in 16.1.7(h).
-/

public section

namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter
open Subgroup Theory.GroupTheory

namespace ElementaryCentralizer

/-- The published elementary kernel is normal in the full actual centralizer. -/
instance kernelNormal : Q.Normal := kernel_normal candidate_eq_top

/-- The literal quotient of the full centralizer by the concrete kernel is S5. -/
noncomputable def quotientEquivS5 : C ⧸ Q ≃* S5 :=
  quotientEquiv candidate_eq_top

/-- The action calculation is unconditional after exhaustive coverage. -/
theorem centralizer_kernel_le : Subgroup.centralizer (Q : Set C) ≤ Q :=
  kernel_selfCentralizing candidate_eq_top

end ElementaryCentralizer

/-- The elementary outer representative has centralizer of shape E16-by-S5,
with actual kernel and quotient isomorphisms. -/
theorem elementaryCentralizer_isExtension :
    IsHSElementaryExtension (permutationCentralizer elementaryPermutation) :=
  ⟨ElementaryCentralizer.Q, ElementaryCentralizer.kernelNormal,
    ⟨ElementaryCentralizer.kernelEquiv⟩, ⟨ElementaryCentralizer.quotientEquivS5⟩⟩

/-- The same concrete E16 kernel supplies the action condition for components. -/
theorem elementaryCentralizer_hasSelfCentralizingNormalTwoSubgroup :
    HasSelfCentralizingNormalTwoSubgroup
      (permutationCentralizer elementaryPermutation) :=
  ⟨ElementaryCentralizer.Q, ElementaryCentralizer.kernelNormal,
    ElementaryCentralizer.kernel_isPGroup, ElementaryCentralizer.centralizer_kernel_le⟩

/-- This representative contributes no components to the alternatives in 16.1.7. -/
theorem elementaryCentralizer_not_isComponent
    (K : Subgroup (permutationCentralizer elementaryPermutation)) :
    ¬ IsComponent (permutationCentralizer elementaryPermutation) K :=
  elementaryCentralizer_hasSelfCentralizingNormalTwoSubgroup.not_isComponent K

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter
