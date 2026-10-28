module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Reduction

/-!
# The inverted set in the core-growth argument

In GLS, Volume 4, Chapter 2, Sections 3 and 16–17, the set `I` consists of
those elements of `O_{2'}(D)` inverted by the distinguished outside
involution `t`, where `D = M ∩ Mᵗ`. It is a set, not a subgroup. We regard
it inside `M` and define its actual conjugation maps on `Z ∩ M`.

Sharp transitivity of these maps and generation of `[O_{2'}(D),t]` are
separate proof obligations; neither is part of the definitions below.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII
variable {G : Type*} [Group G]

/-- The source inverted set `I_{O_{2'}(D)}(t)`, in the internal copy of `M`. -/
@[expose] public def coreGrowthInvertedSet (M : Subgroup G) (t : G) : Set M :=
  {x | (x : G) ∈ (pPrimeCore 2 (residualPairStabilizer M t)).map
      (residualPairStabilizer M t).subtype ∧
    t * (x : G) * t⁻¹ = (x : G)⁻¹}

public theorem one_mem_coreGrowthInvertedSet (M : Subgroup G) (t : G) :
    (1 : M) ∈ coreGrowthInvertedSet M t := by
  exact ⟨Subgroup.one_mem _, by simp⟩

/-- Conjugation by an element of `I`, with its actual distinguished target.
The source regularity assertion is bijectivity for each distinguished `z`. -/
@[expose] public def coreGrowthConjugate {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (t : G) (z : M) (hz : (z : G) ∈ Z) :
    coreGrowthInvertedSet M t → {w : M // (w : G) ∈ Z} := fun i =>
  ⟨MulAut.conj (i : M) z, h.invariant (i : G) z hz⟩

end BenderSuzuki.ZD
