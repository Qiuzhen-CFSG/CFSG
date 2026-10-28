module

public import Theory.SpecificGroups.Lyons.GebhardtLocalParabolicRelators
public import Theory.GroupTheory.CosetWordCertificate

/-!
# Literal words for the local parabolic coset trace

These sixteen signed words are checked against the existing source relators
by `mk_rawRelatorWords`, a reflexivity proof in the free group. Free reduction
then shortens the inputs to the enumeration checker. Both checker evaluation
conventions interpret each resulting word as the identity in the actual local
subgroup, without a finite-group identification.

The numeric producer encoding is translated to `(generator, positive)` here.
The proof of equality with the source list, rather than the producer, certifies
this transcription. Source: Gebhardt, Experimental Mathematics 9 (2000),
333–338, Section 3B, as transcribed in `GebhardtPresentation`.
-/

namespace Lyons.Gebhardt.LocalParabolicCertificate
@[expose] public section
open Theory.GroupTheory.CosetEnumeration
/-- The original signed words, before free reduction. -/
def rawRelatorWords : List (Word (Fin 4)) := [
  [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)],
  [(1, true), (1, true), (1, true), (1, true), (1, true)],
  [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)],
  [(0, false), (0, false), (1, false), (0, true), (0, true), (1, true)],
  [(0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true)],
  [(2, true), (2, true), (2, true), (2, true), (2, true)],
  [(0, false), (0, false), (2, true), (0, true), (0, true), (2, false), (2, false), (2, false)],
  [(0, false), (1, false), (2, true), (1, true), (0, true), (1, true), (2, false), (1, false), (2, false), (1, false), (0, false), (0, false), (2, false), (0, true), (0, true), (1, true)],
  [(1, false), (1, false), (2, true), (1, true), (1, true), (1, false), (2, true), (1, true), (1, false), (2, true), (1, true), (1, true), (2, false), (1, false), (2, false), (2, false)],
  [(3, false), (0, true), (1, false), (0, true), (3, true), (0, false), (0, false), (0, false), (0, false), (0, false), (1, true), (0, false)],
  [(3, false), (1, true), (1, true), (0, false), (3, true), (0, true), (1, false), (1, false), (0, true), (0, true)],
  [(3, false), (2, false), (3, false), (1, true), (0, true), (2, false), (1, true), (0, true), (1, false), (1, false), (0, true), (3, true), (2, true), (3, true), (2, true), (0, false), (1, false), (2, false), (1, true), (2, false), (0, false), (1, true), (1, true), (0, false), (1, true), (0, true), (1, false), (0, true)],
  [(3, false), (2, false), (3, false), (0, true), (0, true), (2, false), (1, true), (0, true), (2, false), (1, true), (0, false), (1, false), (3, true), (2, true), (3, true), (1, false), (1, false), (2, false), (1, true), (2, false), (1, true), (0, true), (1, true), (0, true), (0, true)],
  [(3, false), (2, false), (1, false), (0, true), (2, false), (3, false), (1, true), (1, true), (0, true), (2, true), (1, true), (0, true), (3, true), (2, true), (0, false), (1, true), (2, true), (3, true), (0, false), (1, false), (2, true), (1, true), (0, true), (2, false), (1, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true)],
  [(3, false), (2, false), (1, false), (0, true), (2, false), (3, false), (0, true), (2, false), (2, false), (1, true), (3, true), (2, true), (0, false), (1, true), (2, true), (3, true), (1, true), (0, false), (2, false), (1, true), (0, false), (1, true), (2, true), (1, false), (1, false), (0, true), (0, true), (0, true), (0, true)],
  [(2, true), (0, false), (2, false), (0, true), (2, false), (0, false), (2, true), (0, true), (3, false), (2, false), (0, false), (2, false), (0, true), (2, true), (0, false), (2, true), (3, true), (2, true), (0, true), (2, false), (0, false), (2, false), (0, true), (2, true), (3, true)]
]

theorem mk_rawRelatorWords : rawRelatorWords.map FreeGroup.mk = freeRelators := by
  rfl

/-- Freely reduced inputs for the local enumeration. -/
def relatorWords : List (Word (Fin 4)) :=
  rawRelatorWords.map Subgroup.CosetWordCertificate.reduce

private theorem mk_reduce (w : Word (Fin 4)) :
    FreeGroup.mk (Subgroup.CosetWordCertificate.reduce w) = FreeGroup.mk w := by
  simpa only [Subgroup.CosetWordCertificate.eval, FreeGroup.lift_of_apply] using
    Subgroup.CosetWordCertificate.eval_reduce (FreeGroup.of : Fin 4 → FreeGroup (Fin 4)) w

theorem mk_relatorWords : relatorWords.map FreeGroup.mk = freeRelators := by
  rw [relatorWords, List.map_map]
  calc
    _ = rawRelatorWords.map FreeGroup.mk := by
      apply List.map_congr_left
      intro w _
      exact mk_reduce w
    _ = freeRelators := mk_rawRelatorWords

theorem mk_relatorWord_mem (w : Word (Fin 4)) (hw : w ∈ relatorWords) :
    FreeGroup.mk w ∈ freeRelators := by
  rw [← mk_relatorWords]
  exact List.mem_map.mpr ⟨w, hw, rfl⟩

theorem enumeration_relator_eq_one (w : Word (Fin 4)) (hw : w ∈ relatorWords) :
    eval generator w = 1 :=
  relationWord_eq_one_of_mem w (mk_relatorWord_mem w hw)

theorem wordCertificate_relator_eq_one (w : Word (Fin 4)) (hw : w ∈ relatorWords) :
    Subgroup.CosetWordCertificate.eval generator w = 1 :=
  freeRelator_eq_one _ (mk_relatorWord_mem w hw)

end
end Lyons.Gebhardt.LocalParabolicCertificate
