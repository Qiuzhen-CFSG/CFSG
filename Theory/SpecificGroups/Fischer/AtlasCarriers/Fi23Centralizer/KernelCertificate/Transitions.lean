module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.FixedPointSetup
public import Theory.GroupTheory.WordSubgroup.Stabilizer

/-!
# Schreier transitions for the literal Fi23 carrier

The generic stabilizer-containment theorem applies to the two exact ATLAS
permutations defining Fi23. Its first application, at letter 1, begins the
three-letter prefix bound needed by the centralizer restriction kernel proof.
The explicit transition equations must still be certified. This module is
separate from the kernel assembly so certificate producers can import it.

Source application: GLS3 Table 5.3u and the Fischer paragraph at line 1042 in
`refs/KGroup/GLS3/Chapter5(sec3-).tex`; permutation data: ATLAS F23G1-p31671B0.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection

/-- Apply a checked Schreier transition table to the literal two ATLAS
generators. At `base = 1` this supplies the first step of the prefix containment
needed below; the later two steps use the same theorem for their generators.
The transition equations remain concrete certificate obligations. -/
theorem carrier_stabilizer_le_of_transitions {ι : Type*}
    (K : Subgroup (Equiv.Perm (Fin 31671)))
    (rep : ι → Equiv.Perm (Fin 31671)) (initial : ι) (base : Fin 31671)
    (hInitial : rep initial = 1)
    (hStep : ∀ s ∈ ({generatorA, generatorB} : Set (Equiv.Perm (Fin 31671))),
      ∀ r, ∃ t, ∃ k : K, s * rep r = rep t * k.val)
    (hInvStep : ∀ s ∈ ({generatorA, generatorB} : Set (Equiv.Perm (Fin 31671))),
      ∀ r, ∃ t, ∃ k : K, s⁻¹ * rep r = rep t * k.val)
    (hFix : ∀ k : K, k.val base = base)
    (hSeparate : ∀ r, rep r base = base → rep r = 1)
    (g : Carrier) (hbase : inclusion g base = base) : inclusion g ∈ K :=
  Theory.GroupTheory.closure_stabilizer_le_next {generatorA, generatorB} K
    rep initial base hInitial hStep hInvStep hFix hSeparate g.property hbase

end Sporadic.Fischer.Fi23.CentralizerSection
