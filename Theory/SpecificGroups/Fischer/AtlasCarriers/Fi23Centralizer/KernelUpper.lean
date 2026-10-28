module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelData
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.Transitions
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Data

/-!
# Assembly of the Fi23 three-point stabilizer bound

The three single-point inclusions are independent certificate obligations.
Their endpoints are the two explicit auxiliary groups in `KernelUpper.Data`
and the original seven-generator `KernelData.intermediate`. The theorem below
composes these inclusions for the literal ATLAS carrier and base `[1,13,27]`.
It remains conditional until all three inclusions have been certified.

This is the first part of the fixed-letter kernel argument for the involution
centralizer in GLS3 Table 5.3u, discussed in the Fischer paragraph of
`refs/KGroup/GLS3/Chapter5(sec3-).tex` near line 1042.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection

/-- The actual prefix containment follows from the three concrete step bounds.
The hypotheses are certificate obligations, not asserted stabilizer identities. -/
theorem prefix_stabilizer_le_intermediate_of_steps
    (hfirst : ∀ g : Carrier, inclusion g 1 = 1 → inclusion g ∈ KernelUpperData.first)
    (hsecond : ∀ p ∈ KernelUpperData.first, p 13 = 13 → p ∈ KernelUpperData.second)
    (hthird : ∀ p ∈ KernelUpperData.second, p 27 = 27 → p ∈ KernelData.intermediate)
    (g : Carrier) (hg : ∀ x ∈ KernelData.basePrefix, inclusion g x = x) :
    inclusion g ∈ KernelData.intermediate := by
  apply hthird (inclusion g)
  · apply hsecond (inclusion g)
    · exact hfirst g (hg 1 (by simp [KernelData.basePrefix]))
    · exact hg 13 (by simp [KernelData.basePrefix])
  · exact hg 27 (by simp [KernelData.basePrefix])

end Sporadic.Fischer.Fi23.CentralizerSection
