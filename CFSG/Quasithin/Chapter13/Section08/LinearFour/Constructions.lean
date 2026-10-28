module

public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.PResidual.Defs

/-!
# The local subgroups for the L₄(2) branch

These are the constructions preceding Aschbacher–Smith 13.8.29, in
*The Classification of Quasithin Groups*, combined manuscript (1 March
2004), printed p.963. All subgroups live in the original ambient group.
In particular, `K2` is the image of the **two-residual** of `N_H(V₂)`;
`Q2` is the image of the **two-core** of `N_G(V₂)`. The generated groups
`U0` and `V0` use precisely that normalizer as conjugating group.

The elementary containment and normalization results below follow from
these definitions. They do not supply the model and representation
identifications of 13.8.29. The source uses right conjugation; a span
over all elements of a subgroup is unchanged by using left conjugation.
-/

namespace CFSG.Quasithin.Chapter13.Section08.LinearFour

open Subgroup

variable {G : Type*} [Group G]

/-- The source `G₂ = N_G(V₂)`. -/
@[expose] public def G2 (V2 : Subgroup G) : Subgroup G :=
  normalizer (V2 : Set G)

/-- The source `K₂ = O²(N_H(V₂))`, mapped into the original ambient group. -/
@[expose] public def K2 (H V2 : Subgroup G) : Subgroup G :=
  (pResidual 2 (↥(H ⊓ G2 V2))).map (H ⊓ G2 V2).subtype

/-- The source `Q₂ = O₂(G₂)`, mapped into the original ambient group. -/
@[expose] public def Q2 (V2 : Subgroup G) : Subgroup G :=
  (G2 V2).pCoreIn 2

/-- The source `U₀ = ⟨U_H^{G₂}⟩`. -/
@[expose] public def U0 (UH V2 : Subgroup G) : Subgroup G :=
  conjugateSpanBy UH (G2 V2)

/-- The source `V₀ = ⟨V_H^{G₂}⟩`. -/
@[expose] public def V0 (VH V2 : Subgroup G) : Subgroup G :=
  conjugateSpanBy VH (G2 V2)

public theorem K2_le_localNormalizer (H V2 : Subgroup G) :
    K2 H V2 ≤ H ⊓ G2 V2 := by
  exact map_subtype_le _

public theorem Q2_le_G2 (V2 : Subgroup G) : Q2 V2 ≤ G2 V2 :=
  pCoreIn_le 2 (G2 V2)

public theorem UH_le_U0 (UH V2 : Subgroup G) : UH ≤ U0 UH V2 :=
  le_conjugateSpanBy UH (G2 V2)

public theorem VH_le_V0 (VH V2 : Subgroup G) : VH ≤ V0 VH V2 :=
  le_conjugateSpanBy VH (G2 V2)

public theorem G2_normalizes_U0 (UH V2 : Subgroup G) :
    G2 V2 ≤ normalizer (U0 UH V2 : Set G) :=
  le_normalizer_conjugateSpanBy UH (G2 V2)

public theorem G2_normalizes_V0 (VH V2 : Subgroup G) :
    G2 V2 ≤ normalizer (V0 VH V2 : Set G) :=
  le_normalizer_conjugateSpanBy VH (G2 V2)

public theorem U0_le_V0 {UH VH V2 : Subgroup G} (hUV : UH ≤ VH) :
    U0 UH V2 ≤ V0 VH V2 := conjugateSpanBy_mono hUV le_rfl

end CFSG.Quasithin.Chapter13.Section08.LinearFour
