module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.RankOne
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.BlockContracts
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.CentralizingActors
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.RetainedBlock
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.Append

/-!
# Positive-rank dihedral equality induction

Rank one is proved directly. At larger rank, sharpness classifies the
rotation-fixed space by strict induction and leaves an ordinary block of
dimension two or four. In the five-factor branch the distinguished factor
is chosen different from the five-factor, which is forced into the
strictly smaller fixed-space action.

The retained-block construction supplies the actual cubic or orthogonal
action and pointwise fixation of its complement. The append construction
uses the smaller classification's actual count and preserves its canonical
inclusions and exceptional first factor. Together they prove the positive induction
step from the splitting, degree, orthogonal-pair and classified-centralizer
inputs. These earlier inputs remain explicit for the source-theorem
assembly owner. Source: Aschbacher--Smith G.9.2, printed pp.351--353.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality

open DihedralDegree PositiveStep

universe v

/-- Conditional assembly of the positive step from the retained-block and
inclusion-preserving append contracts. -/
theorem positiveEqualityStep_of_block_inputs
    (split : DihedralSplittingTheorem.{v}) (bounds : DihedralDegreeTheorem.{v})
    (block : BlockClassificationTheorem.{v}) (append : AppendClassifiedTheorem.{v}) :
    PositiveEqualityStep.{v} := by
  intro r hr ih
  by_cases hone : r = 1
  · subst r
    exact equalityAt_one split
  intro ι _ _ hc p hp ho W _ _ _ σ hf
  have ih' : ∀ s, s < Fintype.card ι → EqualityAt.{v} s := by
    intro s hs
    exact ih s (by omega)
  have finish (i : ι) (exceptional : Prop) (s : PreparedSplit σ i exceptional) :
      Nonempty (ClassifiedDecomposition σ ⊤ exceptional) :=
    append ι p W σ i exceptional s
      (split W (p i) (hp i) (ho i) (factorRep σ i) (factorRep_injective σ hf i)).1
      (block ι p hp ho W σ hf i exceptional s)
  constructor
  · intro hall hd
    obtain ⟨i⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card ι by omega)
    obtain ⟨s⟩ := preparedSplit_cubic (i := i) split bounds ih' hp ho hf hall (by omega)
    exact finish i False s
  · rintro ⟨j, hj⟩ hd
    obtain ⟨i, hi⟩ := Fintype.exists_ne_of_one_lt_card
      (show 1 < Fintype.card ι by omega) j
    obtain ⟨s⟩ := preparedSplit_five (i := i) split bounds ih' hp ho hf j hi.symm hj
      (by omega)
    exact finish i True s

/-- The strict positive-rank induction step, including rank one, from the
four earlier-theorem inputs. The retained-block and append contracts are
discharged by their constructions, with no same-rank classification input. -/
theorem positiveEqualityStep_of_inputs
    (split : DihedralSplittingTheorem.{v}) (bounds : DihedralDegreeTheorem.{v})
    (pair : OrthogonalPairTheorem.{v})
    (centralizer : ClassifiedInvolutionCentralizerTheorem.{0,v}) :
    PositiveEqualityStep.{v} :=
  positiveEqualityStep_of_block_inputs split bounds
    (blockClassification_of_inputs split bounds pair centralizer) appendClassifiedTheorem

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality
