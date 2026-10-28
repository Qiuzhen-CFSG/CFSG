module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi24Prime
public import Theory.GroupTheory.InvolutionCentralizerSectionEmbedding

/-!
# The Fi₂₃ subgroup route to a Fi₂₄′ centralizer section

The explanatory paragraph for GLS3 Table 5.3v chooses an outer involution
z_C and an inner involution z_A in its Fi₂₃ centralizer. The centralizer
of z_A in that subgroup is 2Fi₂₂. Thus an embedding of Fi₂₃ into Fi₂₄′
transports its Fi₂₂ quotient section to the centralizer of an involution
in Fi₂₄′. In particular the outer z_C is not the required witness.

Here all three groups are the fixed ATLAS permutation carriers. The
embedding and the Fi₂₃ quotient section remain explicit inputs: this
module's conditional result does not yet construct either of them and
does not by itself establish the source centralizer assertion.

Source: `refs/KGroup/GLS3/Chapter5(sec3-).tex`, Table 5.3v and the
paragraph beginning "If K = Fi₂₄′" (line 1053). The application is
Aschbacher--Smith A.2.19, printed pp. 40–41 / PDF pp. 51–52.
-/

public section

namespace Sporadic.Fischer.Fi24Prime

/-- Transport the Fi₂₂ quotient section of Fi₂₃ along a genuine embedding
of the fixed permutation carriers. Both concrete inputs still need proofs. -/
theorem exists_fi22_centralizer_section_of_fi23_embedding
    (e : Fi23.Carrier →* Carrier) (he : Function.Injective e)
    (h23 : ∃ (t : Fi23.Carrier) (L : Subgroup Fi23.Carrier) (f : L →* Fi22.Carrier),
      orderOf t = 2 ∧ L ≤ Subgroup.centralizer ({t} : Set Fi23.Carrier) ∧
      Function.Surjective f ∧ IsPGroup 2 f.ker) :
    ∃ (t : Carrier) (L : Subgroup Carrier) (f : L →* Fi22.Carrier),
      orderOf t = 2 ∧ L ≤ Subgroup.centralizer ({t} : Set Carrier) ∧
      Function.Surjective f ∧ IsPGroup 2 f.ker := by
  obtain ⟨t, L, f, ht, hL, hf, hk⟩ := h23
  exact Theory.GroupTheory.exists_involutionCentralizer_section_of_injective
    e he t ht L hL f hf 2 hk

end Sporadic.Fischer.Fi24Prime
