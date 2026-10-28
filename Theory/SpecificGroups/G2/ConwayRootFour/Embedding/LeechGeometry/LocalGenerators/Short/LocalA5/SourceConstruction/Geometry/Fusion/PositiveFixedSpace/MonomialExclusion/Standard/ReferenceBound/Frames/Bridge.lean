module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Frames.Arithmetic

/-!
# Passing finite frame checks to the published candidate contract

The matching check identifies both literal monomial parameters, including the
possible global sign. The action, fixed-vector and coordinate-retraction checks
then construct an `EightFrame` for the original candidate matrix.
Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284.
-/

open Atlas.Codes
open scoped Matrix
@[expose] public section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound
namespace FrameCheck

def referenceRowVector : Vector ℕ 24 :=
  ⟨#[1,13,5,6,68,122,21,227,1028,1803,261,2828,5714,51673,22860,30449,66876,855141,328954,396196,4473943,8036470,1400043,14914235], rfl⟩

set_option Elab.async false in
theorem referenceRowVector_eq : rowMatrix referenceRowVector = referenceTable := by
  decide +kernel

def matchCheck (r : Fin 512) (s : ℕ) (p : Vector (Fin 24) 24) (neg : Bool) : Bool :=
  all24 fun k => decide (candidateSign r k =
      if neg then 1 - maskBit s k else maskBit s k) &&
    decide (candidatePull r k = p.get k)

theorem candidate_eq_of_checks (r : Fin 512) (s : ℕ) (p : Vector (Fin 24) 24)
    (rows : Vector ℕ 24) (neg : Bool)
    (ha : actionCheck s p rows = true) (hm : matchCheck r s p neg = true) :
    candidateMatrix r = rowMatrix rows := by
  have hs : candidateSign r =
      (fun k => if neg then 1 - maskBit s k else maskBit s k) := by
    funext k
    have hk := (all24_iff _).mp hm k
    simp only [Bool.and_eq_true] at hk
    exact of_decide_eq_true hk.1
  have hp : candidatePull r = p.get := by
    funext k
    have hk := (all24_iff _).mp hm k
    simp only [Bool.and_eq_true] at hk
    exact of_decide_eq_true hk.2
  unfold candidateMatrix
  rw [hs, hp]
  cases neg
  · exact (action_of_check s p rows ha).1
  · exact (action_of_check s p rows ha).2

theorem frame_of_checks (r : Fin 512) (rows : Vector ℕ 24)
    (cols : Vector ℕ 8) (pivots : Vector (Fin 24) 8)
    (hm : candidateMatrix r = rowMatrix rows)
    (ha : fixedCheck referenceRowVector cols = true)
    (hb : fixedCheck rows cols = true)
    (hi : independentCheck pivots cols = true) :
    Nonempty (EightFrame referenceMatrix (candidateMatrix r)) := by
  refine ⟨⟨colMatrix cols, coordinateRetract pivots, ?_, ?_, independent_of_check _ _ hi⟩⟩
  · rw [referenceMatrix_table, ← referenceRowVector_eq]
    exact fixed_of_check _ _ ha
  · rw [hm]
    exact fixed_of_check _ _ hb

end FrameCheck
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound
