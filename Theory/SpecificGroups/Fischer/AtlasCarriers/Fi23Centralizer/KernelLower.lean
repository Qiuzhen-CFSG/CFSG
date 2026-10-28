module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Data
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Tail
public import Theory.GroupTheory.WordSubgroup.Stabilizer

/-!
# Assembly of the Fi23 seven-point stabilizer bound

The seven suffix points are split into two pairs followed by a triple.
The two explicit intermediate closures are defined in `KernelLower.Data`.
Their fixed-point and inverse-table certificates are proved there. For the
last triple, binary collection reduces six commuting involutions to 64
products, of which only the identity and product 10 fix all three points.

The first two stabilizer containments and the full-permutation commutation
and candidate comparisons remain explicit certificate obligations below.
Thus this module does not yet export the unconditional
`intermediate_suffix_stabilizer_bound` requested by the kernel assembly.
No assertion that `KernelData.intermediate` is an ambient stabilizer is used.

Source application: GLS3 Table 5.3u and the Fischer paragraph near line 1042
in `refs/KGroup/GLS3/Chapter5(sec3-).tex`; ATLAS F23G1-p31671B0.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection
open KernelLowerData

/-- The two early certificate families place the four-point stabilizer in
the explicit six-generator group. -/
theorem intermediate_four_point_bound_of_steps
    (hfirst : ∀ p ∈ KernelData.intermediate,
      p 40 = 40 → p 46 = 46 → p ∈ afterTwo)
    (hsecond : ∀ p ∈ afterTwo,
      p 63 = 63 → p 66 = 66 → p ∈ afterFour)
    (p : Equiv.Perm (Fin 31671)) (hp : p ∈ KernelData.intermediate)
    (h40 : p 40 = 40) (h46 : p 46 = 46) (h63 : p 63 = 63) (h66 : p 66 = 66) :
    p ∈ afterFour :=
  hsecond p (hfirst p hp h40 h46) h63 h66

/-- Consume the exact transition and numerical certificate contracts. The
source-theorem assembly must discharge all four of these premises. -/
theorem intermediate_suffix_stabilizer_bound_of_certificates
    (hfirst : ∀ p ∈ KernelData.intermediate,
      p 40 = 40 → p 46 = 46 → p ∈ afterTwo)
    (hsecond : ∀ p ∈ afterTwo,
      p 63 = 63 → p 66 = 66 → p ∈ afterFour)
    (hcomm : ∀ i j, afterFourGenerator i * afterFourGenerator j =
      afterFourGenerator j * afterFourGenerator i)
    (htarget : ∀ x, afterFourGenerator 1 (afterFourGenerator 3 x) =
      GeneratorLiftCertificate.candidateMap x) :
    ∀ p ∈ KernelData.intermediate,
      (∀ x ∈ KernelData.baseSuffix, p x = x) → p = 1 ∨ p = inclusion candidate := by
  intro p hp hfixed
  have h40 := hfixed 40 (by simp [KernelData.baseSuffix])
  have h46 := hfixed 46 (by simp [KernelData.baseSuffix])
  have h63 := hfixed 63 (by simp [KernelData.baseSuffix])
  have h66 := hfixed 66 (by simp [KernelData.baseSuffix])
  have h78 := hfixed 78 (by simp [KernelData.baseSuffix])
  have h86 := hfixed 86 (by simp [KernelData.baseSuffix])
  have h108 := hfixed 108 (by simp [KernelData.baseSuffix])
  exact afterFour_tail_bound_of_relations hcomm htarget p
    (intermediate_four_point_bound_of_steps hfirst hsecond p hp h40 h46 h63 h66)
    h78 h86 h108

end Sporadic.Fischer.Fi23.CentralizerSection
