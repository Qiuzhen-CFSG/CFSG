module

public import Theory.SpecificGroups.Janko3.Model.Order.Level2Generators

/-!
# Word-defined candidates for the J₃ maximal two-locals

These are actual subgroups of the degree-6156 ATLAS model. Every generator
is defined as a product of words in the already certified subgroup-chain
generators. Membership uses only their containment in the model, not the
unfinished order certificate.

The names indicate their intended roles in GLS, volume 3, Table 5.3h,
printed p.269: the involution centralizer, the affine group on F₄², and the
normalizer of the Thompson subgroup of a Sylow two-subgroup. The source's
additive F₄² is elementary abelian of order 16. None of the candidate names
asserts an order, normalizer equality, local shape, or coverage theorem.
Those are separate obligations in the consuming converse proof.

The retained ATLAS data are under `Model/data`. The scripts and discovery
data under `TwoLocal/source` reproduce these words; GAP and Python output
is not used as a proof premise.
-/

namespace Sporadic.Janko3.TwoLocal
open Theory.GroupTheory OrderCertificate

/-- A word in each of three already certified levels, as an actual model element. -/
@[expose] public def chainElement (w0 w1 : List (Fin 4)) (w2 : List (Fin 6)) : Model :=
  ⟨evalWord L0Gen w0 * evalWord L1Gen w1 * evalWord L2Gen w2, by
    change _ ∈ modelSubgroup
    rw [← H0_eq_modelSubgroup]
    exact H0.mul_mem (H0.mul_mem ⟨w0, rfl⟩ (H1_le ⟨w1, rfl⟩))
      (H1_le (H2_le ⟨w2, rfl⟩))⟩

@[expose] public def sylowWord0 : Fin 5 → List (Fin 4)
  | 0 => [0]
  | 1 => [3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0]
  | 2 => [3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1]
  | 3 => [1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0]
  | 4 => [3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0]

@[expose] public def sylowWord1 : Fin 5 → List (Fin 4)
  | 0 => []
  | 1 => [0, 1, 0, 0, 1, 0, 1, 2, 1, 0, 1, 0]
  | 2 => [0, 1, 0, 0, 1, 2, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1]
  | 3 => [2, 1, 0, 0, 1, 2, 1, 0, 1, 2, 1, 0, 0]
  | 4 => [1, 2, 1, 0, 1, 0, 0, 1, 0, 1, 2, 1, 0, 0, 1]

@[expose] public def sylowWord2 : Fin 5 → List (Fin 6)
  | 0 => []
  | 1 => [1, 2, 0]
  | 2 => [2]
  | 3 => [1, 2, 0]
  | 4 => [2, 0]

/-- Explicit generators for the sylow candidate. -/
@[expose] public def sylowGenerator (i : Fin 5) : Model :=
  chainElement (sylowWord0 i) (sylowWord1 i) (sylowWord2 i)

@[expose] public def sylowCandidate : Subgroup Model :=
  Subgroup.closure (Set.range sylowGenerator)

public theorem sylowGenerator_mem (i : Fin 5) :
    sylowGenerator i ∈ sylowCandidate := Subgroup.subset_closure ⟨i, rfl⟩

@[expose] public def elementaryWord0 : Fin 4 → List (Fin 4)
  | 0 => [0]
  | 1 => [3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0]
  | 2 => [3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1]
  | 3 => [0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0]

@[expose] public def elementaryWord1 : Fin 4 → List (Fin 4)
  | 0 => []
  | 1 => [1, 2, 1, 0, 1, 0, 0, 1, 0, 1, 2, 1, 0, 0, 1]
  | 2 => [0, 1, 0, 0, 1, 2, 1, 0, 1, 2, 1]
  | 3 => [0, 0, 1, 2, 1, 0, 1, 2]

@[expose] public def elementaryWord2 : Fin 4 → List (Fin 6)
  | 0 => []
  | 1 => [2, 0]
  | 2 => [1]
  | 3 => [2]

/-- Explicit generators for the elementary candidate. -/
@[expose] public def elementaryGenerator (i : Fin 4) : Model :=
  chainElement (elementaryWord0 i) (elementaryWord1 i) (elementaryWord2 i)

@[expose] public def elementaryCandidate : Subgroup Model :=
  Subgroup.closure (Set.range elementaryGenerator)

public theorem elementaryGenerator_mem (i : Fin 4) :
    elementaryGenerator i ∈ elementaryCandidate := Subgroup.subset_closure ⟨i, rfl⟩

@[expose] public def thompsonWord0 : Fin 6 → List (Fin 4)
  | 0 => [3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0]
  | 1 => [3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1]
  | 2 => [3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0]
  | 3 => [0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0]
  | 4 => [3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0]
  | 5 => [0]

@[expose] public def thompsonWord1 : Fin 6 → List (Fin 4)
  | 0 => [1, 2, 1, 0, 1, 0, 0, 1, 0, 1, 2, 1, 0, 0, 1]
  | 1 => [1, 2, 1, 0, 1, 2, 1, 0, 0, 1, 0]
  | 2 => [0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0]
  | 3 => [0, 0, 1, 2, 1, 0, 1, 2]
  | 4 => [0, 1, 0, 0, 1, 0, 1, 2, 1, 0, 1, 0]
  | 5 => []

@[expose] public def thompsonWord2 : Fin 6 → List (Fin 6)
  | 0 => [2, 0]
  | 1 => [0, 2]
  | 2 => [2, 1, 0]
  | 3 => [2]
  | 4 => [1, 2, 0]
  | 5 => []

/-- Explicit generators for the thompson candidate. -/
@[expose] public def thompsonGenerator (i : Fin 6) : Model :=
  chainElement (thompsonWord0 i) (thompsonWord1 i) (thompsonWord2 i)

@[expose] public def thompsonCandidate : Subgroup Model :=
  Subgroup.closure (Set.range thompsonGenerator)

public theorem thompsonGenerator_mem (i : Fin 6) :
    thompsonGenerator i ∈ thompsonCandidate := Subgroup.subset_closure ⟨i, rfl⟩

@[expose] public def centralizerWord0 : Fin 5 → List (Fin 4)
  | 0 => [0]
  | 1 => [0]
  | 2 => [0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3]
  | 3 => [0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
  | 4 => [0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0]

@[expose] public def centralizerWord1 : Fin 5 → List (Fin 4)
  | 0 => []
  | 1 => []
  | 2 => [1, 2, 1, 2, 1, 0, 1, 0]
  | 3 => [1, 2, 1, 0, 1, 0, 0, 1, 2]
  | 4 => [0, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 2]

@[expose] public def centralizerWord2 : Fin 5 → List (Fin 6)
  | 0 => []
  | 1 => []
  | 2 => [0]
  | 3 => [2]
  | 4 => [0, 0]

/-- Explicit generators for the centralizer candidate. -/
@[expose] public def centralizerGenerator (i : Fin 5) : Model :=
  chainElement (centralizerWord0 i) (centralizerWord1 i) (centralizerWord2 i)

@[expose] public def centralizerCandidate : Subgroup Model :=
  Subgroup.closure (Set.range centralizerGenerator)

public theorem centralizerGenerator_mem (i : Fin 5) :
    centralizerGenerator i ∈ centralizerCandidate := Subgroup.subset_closure ⟨i, rfl⟩

@[expose] public def affineWord0 : Fin 7 → List (Fin 4)
  | 0 => [0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0]
  | 1 => [3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1]
  | 2 => [3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0]
  | 3 => [0]
  | 4 => []
  | 5 => [0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1]
  | 6 => [1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3]

@[expose] public def affineWord1 : Fin 7 → List (Fin 4)
  | 0 => [0, 0, 1, 2, 1, 0, 1, 2]
  | 1 => [0, 1, 0, 0, 1, 2, 1, 0, 1, 2, 1]
  | 2 => [1, 2, 1, 0, 1, 0, 0, 1, 0, 1, 2, 1, 0, 0, 1]
  | 3 => []
  | 4 => [1, 2, 1, 0, 1, 2, 1, 0, 0, 1, 2, 1, 0, 0, 1]
  | 5 => [0, 0, 1, 0, 0, 1, 2, 1, 0, 0, 1]
  | 6 => [1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 2, 1]

@[expose] public def affineWord2 : Fin 7 → List (Fin 6)
  | 0 => [2]
  | 1 => [1]
  | 2 => [2, 0]
  | 3 => []
  | 4 => []
  | 5 => [2]
  | 6 => [0, 2]

/-- Explicit generators for the affine candidate. -/
@[expose] public def affineGenerator (i : Fin 7) : Model :=
  chainElement (affineWord0 i) (affineWord1 i) (affineWord2 i)

@[expose] public def affineCandidate : Subgroup Model :=
  Subgroup.closure (Set.range affineGenerator)

public theorem affineGenerator_mem (i : Fin 7) :
    affineGenerator i ∈ affineCandidate := Subgroup.subset_closure ⟨i, rfl⟩

@[expose] public def thompsonNormalizerWord0 : Fin 8 → List (Fin 4)
  | 0 => [0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0]
  | 1 => [3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0]
  | 2 => [3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1]
  | 3 => [3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0]
  | 4 => [0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0]
  | 5 => [3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0]
  | 6 => [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1]
  | 7 => [0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3]

@[expose] public def thompsonNormalizerWord1 : Fin 8 → List (Fin 4)
  | 0 => [0, 0, 1, 2, 1, 0, 1, 2]
  | 1 => [0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0]
  | 2 => [1, 2, 1, 0, 1, 2, 1, 0, 0, 1, 0]
  | 3 => [1, 0, 1, 0, 1, 0, 0, 1, 2]
  | 4 => [1, 0, 1, 0, 1, 0, 0, 1, 2]
  | 5 => [1, 2, 1, 0, 1, 0, 0, 1, 0, 1, 2, 1, 0, 0, 1]
  | 6 => [1, 2, 1, 0, 1, 0, 1, 2, 1]
  | 7 => [0, 0, 1, 2, 1]

@[expose] public def thompsonNormalizerWord2 : Fin 8 → List (Fin 6)
  | 0 => [2]
  | 1 => [2, 1, 0]
  | 2 => [0, 2]
  | 3 => [4]
  | 4 => [4]
  | 5 => [2, 0]
  | 6 => [0]
  | 7 => [0, 2]

/-- Explicit generators for the thompsonNormalizer candidate. -/
@[expose] public def thompsonNormalizerGenerator (i : Fin 8) : Model :=
  chainElement (thompsonNormalizerWord0 i) (thompsonNormalizerWord1 i) (thompsonNormalizerWord2 i)

@[expose] public def thompsonNormalizerCandidate : Subgroup Model :=
  Subgroup.closure (Set.range thompsonNormalizerGenerator)

public theorem thompsonNormalizerGenerator_mem (i : Fin 8) :
    thompsonNormalizerGenerator i ∈ thompsonNormalizerCandidate := Subgroup.subset_closure ⟨i, rfl⟩

/-- The three word-defined local candidates in the source table's order. -/
@[expose] public def localFamily : Fin 3 → Subgroup Model
  | 0 => centralizerCandidate
  | 1 => affineCandidate
  | 2 => thompsonNormalizerCandidate

end Sporadic.Janko3.TwoLocal
