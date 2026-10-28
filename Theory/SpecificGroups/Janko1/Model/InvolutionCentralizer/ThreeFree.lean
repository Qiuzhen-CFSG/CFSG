module
public import Theory.SpecificGroups.Janko1.Model.InvolutionCentralizer.Identification
public import Theory.SpecificGroups.Janko1.Model.InvolutionCentralizer.ProductStructure
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Two-group radicals of all J1 involution centralizers

The certified single involution class transports the actual C2 x A5
centralizer identification to every involution. Its solvable radical
is a two-group. The original rank-one application is in 12.6.26.
Source: GLS3 Table 5.3f; the native matrix certificates retain their
ATLAS attribution in Model.Basic and Certification.
-/

public section
open Subgroup Theory.GroupTheory
namespace Janko1.InvolutionCentralizer

/-- Every involution centralizer in the actual J1 carrier has a two-group radical. -/
theorem involution_radical_isTwoGroup (t : Model) (ht : orderOf t = 2) :
    IsPGroup 2 (solvableRadical (centralizer ({t} : Set Model))) := by
  obtain ⟨g,hg⟩ := involution_fusion_of_card card_model t ht
  let e := (CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj g) t).trans
    (MulEquiv.subgroupCongr (congrArg (fun x : Model => centralizer ({x} : Set Model)) hg))
  exact radical_isTwoGroup (e.trans productEquiv)

end Janko1.InvolutionCentralizer
