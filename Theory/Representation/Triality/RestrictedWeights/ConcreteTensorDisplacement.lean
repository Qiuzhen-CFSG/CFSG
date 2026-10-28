module

public import Theory.Representation.Triality.InnerDisplacement.TensorSource
public import Theory.Representation.Triality.RestrictedWeights.ConcreteBasicFamily

/-!
# The actual basic-family consumer of the triality tensor rank estimate

The constructed Spin highest-weight modules supply all dimension inputs.
For the two root representatives fixed by coefficient Frobenius, the remaining
basic operator ranks 2 and 6 imply the strict 5n bound on the literal tensor.
The finite realization, character period and those operator bounds remain
with their independent source producers.
Source: GLS3 §2.8; Guralnick--Malle, Classification of 2F-modules II, 8.6.
-/

public noncomputable section
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
open Triality.SimplyConnected Triality.RestrictedWeights.SteinbergTensors
open Representation.BinaryOffender.NaturalTensor
namespace Triality.RestrictedWeights.Concrete
universe u v
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable (hu : IsUniversalVersion (groupVariety k))

/-- All artificial lower degrees hold on the constructed basic modules. -/
theorem minimumDegree_le_basic_finrank (a : BasicWeight) :
    InnerDisplacement.minimumDegree a ≤ Module.finrank k ((basicFamily k hu).factor a).Space := by
  by_cases ha : a=zeroWeight
  · simp only [InnerDisplacement.minimumDegree,if_pos ha]
    exact ((basicFamily k hu).factor a).finrank_pos
  · obtain ⟨h8,h24⟩ := basic_finrank_lower_bounds k hu a ha
    by_cases hf : diagramAction a=a
    · simpa only [InnerDisplacement.minimumDegree,if_neg ha,if_pos hf] using h24 hf
    · simpa only [InnerDisplacement.minimumDegree,if_neg ha,if_neg hf] using h8

/-- The original basic-family tensor, with every dimension premise discharged. -/
theorem five_mul_lt_basic_tensor_displacement
    {G : Type v} [Group G] (ι : G →* Variety.Point (groupVariety k))
    (t : G) (ht : t^2=1)
    (hφ : (finiteGeometry k hu).frobenius.onPoints (ι t)=ι t)
    (w : ℕ→BasicWeight) (n s : ℕ) (hn : 0<n) (hs : 0<s) (hsn : s ∣ 3*n)
    (hwrap : ∀ i,w (i+n)=diagramAction (w i)) (hp : Function.Periodic w s)
    (hne : ∃ i,w i≠zeroWeight)
    (hrank : ∀ a,a≠zeroWeight →
      2≤operatorFixedCodim ((((basicFamily k hu).factor a).action.action (ι t)).val) ∧
      (diagramAction a=a →
        6≤operatorFixedCodim ((((basicFamily k hu).factor a).action.action (ι t)).val))) :
    5*n < s*operatorFixedCodim ((tensor (basicFamily k hu).factor
      (finiteGeometry k hu).frobenius.onPoints ι w n).ρ t) :=
  InnerDisplacement.five_mul_lt_fixed_tensor_displacement (basicFamily k hu).factor
    (finiteGeometry k hu).frobenius.onPoints ι t ht hφ w n s hn hs hsn hwrap hp hne
    (minimumDegree_le_basic_finrank k hu) hrank

end Triality.RestrictedWeights.Concrete
