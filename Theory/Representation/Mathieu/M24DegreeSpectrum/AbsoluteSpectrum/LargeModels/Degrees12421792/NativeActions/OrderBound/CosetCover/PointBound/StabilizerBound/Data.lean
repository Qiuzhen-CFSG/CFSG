module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.Stabilizer
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.PresentationBound.StabilizerBound.Data

/-!
# Exact words for comparing two abstract presentations

The eight proposed generators are literal words in the 24 generators of
`Stabilizer.Presented`. The comparison source is the independently bounded
29-relator `StabilizerChain.Level2`. Its relators must be proved in the original
abstract presentation; its permutation image supplies no such proof.

`Relations` and `Generation` are independent obligations. The optional
`recoveryWord` table gives candidate witnesses for the latter. They are data,
not equations. See `source/README.md` for discovery and word conventions.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Stabilizer.Comparison
open Subgroup.CosetWordCertificate
open Janko4.Cardinality.QuotientCount.UpperBound.PresentationBound.StabilizerChain

abbrev SourcePresented := Level2

def generatorWord : Fin 8 → Word (Fin 24) :=
  ![[(7, false), (9, true), (7, true), (4, false)],
    [(14, false), (1, false), (20, false), (18, false)],
    [(7, false), (9, true), (7, true), (4, false)],
    [(11, false), (4, false), (14, true), (18, true)],
    [(9, true), (7, true), (9, false), (12, false)],
    [(15, true), (14, true), (15, true), (7, false)],
    [(1, false), (11, true), (9, false), (4, true)],
    [(17, false), (18, false), (7, false), (17, true)]]

def generator (i : Fin 8) : Presented := eval PresentedGroup.of (generatorWord i)

def subgroup : Subgroup Presented := Subgroup.closure (Set.range generator)

/-- Literal relation-lifting obligation for the proposed map. -/
def Relations : Prop := ∀ r : Fin 29, eval generator (level2Relator r) = 1

/-- Generation of the abstract 437-relator group, with ordinary subgroup closure. -/
def Generation : Prop := subgroup = ⊤

/-- Optional candidate witnesses; no equality with an original generator is assumed. -/
def recoveryWord : Fin 24 → Word (Fin 8) :=
  ![[],
    [(6, true), (4, false), (1, false), (5, true), (0, true)],
    [(0, true), (4, false), (0, false), (1, false), (4, false), (7, false)],
    [(4, true), (5, true), (3, true), (7, false), (1, false), (3, true)],
    [(3, false), (1, true), (4, true), (0, false), (5, true)],
    [(5, false), (0, true), (4, false), (1, false), (3, true)],
    [],
    [(1, false), (4, false), (5, false), (3, true)],
    [(0, true), (7, true), (5, true), (0, false), (1, false), (3, true)],
    [(0, true), (7, false), (5, false), (0, true), (1, true)],
    [(1, false), (0, false), (5, true), (7, true), (0, false)],
    [(0, true), (3, false), (5, false), (3, true), (4, false), (1, true)],
    [(3, false), (1, true), (5, false), (1, true), (4, true), (1, false)],
    [(3, true), (0, false), (3, true), (0, false), (4, true)],
    [(1, false), (1, false), (4, true), (0, true), (6, true)],
    [(1, true), (6, true), (5, true), (1, true), (3, true), (4, true)],
    [],
    [(1, false), (7, false), (1, true), (0, false), (7, true), (1, true)],
    [(3, true), (7, true), (1, false), (5, true), (7, false)],
    [(0, true), (1, false), (7, true), (1, true), (0, false)],
    [(1, false), (0, false), (7, true), (0, false), (3, false), (3, false)],
    [(1, false), (6, true), (5, true), (0, true), (4, true), (4, true)],
    [(5, true), (7, false), (4, false), (1, false), (5, true)],
    [(0, true), (6, true), (1, true), (1, true), (5, false), (7, true)]]

/-- The exact source relations are available in the abstract target group. -/
theorem defining_relation (r : Fin 23 × Fin 19) :
    eval (PresentedGroup.of : Fin 24 → Presented) (relatorLetters r) = 1 := by
  have hm : FreeGroup.lift (PresentedGroup.of : Fin 24 → Presented) =
      PresentedGroup.mk (Set.range relator) := by
    apply FreeGroup.ext_hom
    intro i
    rfl
  change FreeGroup.lift (PresentedGroup.of : Fin 24 → Presented) (relator r) = 1
  rw [hm]
  exact PresentedGroup.one_of_mem ⟨r, rfl⟩

/-- Any proved recovery words suffice; the optional table is not privileged. -/
theorem generation_of_recovery (w : Fin 24 → Word (Fin 8))
    (h : ∀ a : Fin 24, PresentedGroup.of a = eval generator (w a)) : Generation := by
  apply top_unique
  rw [← PresentedGroup.closure_range_of (Set.range relator)]
  apply (Subgroup.closure_le subgroup).mpr
  rintro _ ⟨a, rfl⟩
  rw [h a]
  exact eval_mem_of_generators_mem subgroup generator
    (fun i => Subgroup.subset_closure (Set.mem_range_self i)) _

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Stabilizer.Comparison
