module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelData
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.Evaluation
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.Transitions

/-!
# The ten-letter route to the Fi23 restriction kernel bound

The first three letters reduce to the explicit intermediate subgroup in
`KernelData`; the remaining seven reduce it to the identity and the candidate.
The assembly below is conditional: neither of these concrete stabilizer bounds
nor the assertion that these ten letters are fixed has yet been certified.
It does not establish the unconditional `pointwise_stabilizer_bound`.

The intermediate group is defined by seven explicit permutations, so these
obligations can be proved independently by kernel-checked Schreier transitions.
The general step soundness theorem is `wordSubgroup_stabilizer_le_next`.
No centralizer structure or identification of the fixed-point image is used.

Source: GLS volume 3, Table 5.3u, and the Fischer paragraph at line 1042 in
`refs/KGroup/GLS3/Chapter5(sec3-).tex`, which specifies `2Fi22`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection

/-- Assemble the two independently certifiable parts of the ten-letter chain.
This stronger conditional bound concerns every element of the actual carrier,
not only elements of the centralizer. -/
theorem fixed_letter_bound_of_stabilizer_chain
    (hprefix : ∀ x ∈ KernelData.basePrefix, inclusion candidate x = x)
    (hsuffix : ∀ x ∈ KernelData.baseSuffix, inclusion candidate x = x)
    (hupper : ∀ g : Carrier,
      (∀ x ∈ KernelData.basePrefix, inclusion g x = x) →
      inclusion g ∈ KernelData.intermediate)
    (hlower : ∀ p ∈ KernelData.intermediate,
      (∀ x ∈ KernelData.baseSuffix, p x = x) → p = 1 ∨ p = inclusion candidate)
    (g : Carrier)
    (hfixed : ∀ x : Fin 31671, inclusion candidate x = x → inclusion g x = x) :
    g = 1 ∨ g = candidate := by
  have hg := hupper g (fun x hx => hfixed x (hprefix x hx))
  rcases hlower (inclusion g) hg (fun x hx => hfixed x (hsuffix x hx)) with h | h
  · left
    apply inclusion_injective
    simpa only [map_one] using h
  · exact Or.inr (inclusion_injective h)

/-- The finite chain supplies the exact premise needed by the parent assembly.
The four concrete premises remain outstanding mathematical obligations. -/
theorem pointwise_stabilizer_bound_of_stabilizer_chain
    (hprefix : ∀ x ∈ KernelData.basePrefix, inclusion candidate x = x)
    (hsuffix : ∀ x ∈ KernelData.baseSuffix, inclusion candidate x = x)
    (hupper : ∀ g : Carrier,
      (∀ x ∈ KernelData.basePrefix, inclusion g x = x) →
      inclusion g ∈ KernelData.intermediate)
    (hlower : ∀ p ∈ KernelData.intermediate,
      (∀ x ∈ KernelData.baseSuffix, p x = x) → p = 1 ∨ p = inclusion candidate) :
    ∀ g : numerator,
      (∀ x : Fin 31671, inclusion candidate x = x → inclusion g.val x = x) →
      g.val = 1 ∨ g.val = candidate := by
  intro g hg
  exact fixed_letter_bound_of_stabilizer_chain hprefix hsuffix hupper hlower g.val hg

end Sporadic.Fischer.Fi23.CentralizerSection
