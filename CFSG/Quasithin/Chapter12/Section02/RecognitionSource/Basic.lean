module

public import CFSG.Quasithin.Chapter12.Section02.SourceHypotheses
public import CFSG.Quasithin.Chapter6.SourceDefs
public import Mathlib.GroupTheory.Complement

/-!
# The local boundary for the recognition in 12.2.13

Failure of the escape alternative concerns every nonidentity element of the
original chosen V. The later local analysis, 12.2.20--26, supplies a split
binary linear block with N_G(L)=L and V=O₂(L). Its natural-action marking
uses the original projection L → L/O₂(L), not just an abstract group tag.

`SplitLinearConfiguration` is an intermediate conclusion to be constructed,
not a replacement for Hypothesis 12.2.3. The global recognition of 12.2.27
is a separate obligation even when this local configuration is available.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
Theorem 12.2.13 and Lemmas 12.2.20--27, printed pp.799--807.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G]

/-- The contrary assumption in the original proof, for the unchanged V. -/
def NoEscape (L V : Subgroup G) : Prop :=
  ∀ v ∈ V, v ≠ 1 → centralizer ({v} : Set G) ≤ normalizer (L : Set G)

/-- The actual local output used in the final involution-centralizer recognition.
The split condition is inside L, over its literal two-core. -/
structure SplitLinearConfiguration (L V : Subgroup G) (d : ℕ) : Prop where
  rank : d = 3 ∨ d = 4
  block : ChapterC.IsLinearTwoBlock L d
  natural : Chapter6.Source.IsConjugationModel L V
    (Representation.specialLinearNatural (k := ZMod 2) d)
  self_normalizing : normalizer (L : Set G) = L
  core_eq : L.pCoreIn 2 = V
  split : ∃ S : Subgroup L, IsComplement' (pCore 2 L) S

/-- The global alternatives in 12.2.27, retaining the local dimension. -/
def RecognizedGroup (G : Type*) [Group G] (d : ℕ) : Prop :=
  ClassicalGroup.IsPSL G (d + 1) 2 ∨
    (d = 3 ∧ Nonempty (G ≃* alternatingGroup (Fin 9))) ∨
    (d = 4 ∧ Nonempty (G ≃* Sporadic.Mathieu.M24))

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
