module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.Inputs
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.Contracts
public import Theory.Representation.CyclicDefect.ClassPairing

/-!
# The source tensor coefficient is the regular projective pairing

The ordinary table identifies the unique eleven-singular class and supplies
actual centralizer orders. The general class-sum theorem therefore gives
exactly the coefficient in `RealStem.TensorPositive`. When projective edge
modules have been constructed, the second factor is their lifted character.
Integrality of this scalar product remains the projective reciprocity theorem.

Source: Feit, Chapter I, §17 and VII.2.15(ii).
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction

open Representation

variable {G : Type*} [Group G] [Finite G] {d : OrdinaryData G}

/-- The literal class-sum coefficient has the standard regular normalization. -/
public theorem tensorCoefficient_eq_regularPairing (s : RealStem G d) (i j k : Fin 10) :
    s.tensorCoefficient i j k = CyclicDefect.regularPairing 11
      (fun g => s.roots.value (s.rep i) g * s.roots.value (s.rep j) g)
      (fun g => d.chi (s.row k.castSucc) (ConjClasses.mk g) +
        d.chi (s.row k.succ) (ConjClasses.mk g)) := by
  classical
  have hr : Function.Bijective (fun c => ConjClasses.mk (d.representatives c)) := by
    simpa only [← d.classes_eq] using d.classes.bijective
  rw [CyclicDefect.regularPairing_eq_sum_div_centralizer d.representatives hr]
  · simp only [regular_representative_iff, d.centralizers, ← d.classes_eq]
    rw [← Finset.sum_filter]
    congr 1
  · intro g a
    dsimp only
    rw [s.roots.value_conj, s.roots.value_conj]
  · intro g a
    dsimp only
    rw [show ConjClasses.mk (a * g * a⁻¹) = ConjClasses.mk g from
      ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨a⁻¹, by simp [mul_assoc]⟩)]

/-- Actual projective edge realizations identify the second factor pointwise
on regular elements. No integrality claim is made without reciprocity. -/
public theorem tensorCoefficient_eq_projectivePairing (s : RealStem G d)
    (P : ProjectiveEdges s) (i j k : Fin 10) :
    s.tensorCoefficient i j k = CyclicDefect.regularPairing 11
      (fun g => s.roots.value (s.rep i) g * s.roots.value (s.rep j) g)
      (s.roots.value (P k).rep) := by
  classical
  rw [tensorCoefficient_eq_regularPairing]
  unfold CyclicDefect.regularPairing
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  split
  · rename_i hg
    rw [(P k).character_eq g hg]
  · rfl

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction
