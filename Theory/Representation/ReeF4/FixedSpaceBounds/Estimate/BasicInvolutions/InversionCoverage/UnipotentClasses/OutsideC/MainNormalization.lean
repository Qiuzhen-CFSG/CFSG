module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC.ReductionContracts
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC.MainNormalization.SplitConjugation

/-!
# Removing the two main coordinates in the outside-C branch

Conjugation by x₁(s)y₁(u) preserves X₈ and the absent first B₂ block.
The main X₇ and X₃ parameters become s*a+b and s^(2θ)*b+u*a+c.
When a is nonzero, solve these two equations in that order. The conjugator
lies in the actual fixed Ree group; positive-coordinate existence and split
uniqueness recover every other parameter without extra twist assumptions.
This proves the `MainNormalization` input of the outside-C conjugacy consumer,
for all m, without a square or involution hypothesis.

Source: GLS3 Table 2.4 and 2.4.5(d), refs/KGroup/GLS3/chapter2.tex;
the coordinate reduction used for Guralnick--Malle Lemma 8.8, internal p.57.
-/

@[expose] public section
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC
open Parabolics Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations.LongCommutators
open NormalizedRootCentralizers.CenterExponent
open NormalizedRootCentralizers.CenterExponent.OuterElimination
open ElementaryTwoBound (centralElement centralElement_coe)
open ElementaryTwoBound.RootCalculations
open Theory.AlgebraicGroup.StandardRootSystem

/-- The actual ambient conjugator for the two main parameters. -/
def firstBlockActor (m : ℕ) (s u : CoefficientField m) : Model m :=
  mainElement m 0 s * centralElement m 0 u

private theorem fieldEnd_half (m : ℕ) (i : Fin 8) :
    rootFieldEnd m (longRoot i) = halfFrobenius m := by
  ext t
  rw [MatrixRelations.rootFieldEnd_longRoot]
  rfl

private theorem word_zero (m : ℕ) (t : CoefficientField m) :
    rootWord m 0 t = X m 0 t * X m 1 (halfFrobenius m t) *
      X m 2 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  rfl

private theorem central_zero (m : ℕ) (t : CoefficientField m) :
    centralWord m 0 t = X m 3 t * X m 2 (halfFrobenius m t) := by
  simp only [centralWord, fieldEnd_half]
  rfl

attribute [local irreducible] X

private theorem firstBlockActor_split (m : ℕ) (s u : CoefficientField m) :
    toSplitGroup m (firstBlockActor m s u) =
      X m 0 s * X m 1 (halfFrobenius m s) *
        X m 2 (s * halfFrobenius m s + halfFrobenius m u) * X m 3 u := by
  have hc := xc m 3 2 (by norm_num [V, dot, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]) u (halfFrobenius m u)
  simp only [firstBlockActor, map_mul, mainElement_coe, centralElement_coe,
    word_zero, central_zero, mul_assoc]
  rw [hc.eq, ← mul_assoc (X m 2 (s * halfFrobenius m s)), xa]

private theorem wordElement_mem_unipotent (m : ℕ) (p : PositiveParameters m) :
    wordElement m p ∈ unipotent m := by
  apply (unipotent m).mul_mem
  · apply (unipotent m).list_prod_mem
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact mainElement_mem_unipotent m _ _
  · apply (unipotent m).list_prod_mem
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact (unipotent m).mul_mem (mainElement_mem_unipotent m _ _)
      (ElementaryTwoBound.Y_le_unipotent m _ (centralElement_mem_Y m _ _))

/-- The required coordinates of the literal first-block conjugation.
No square-one hypothesis is used. -/
theorem firstBlockActor_coordinates (m : ℕ) (p : PositiveParameters m)
    (hmain : p.main 0 = 0) (hcentral : p.central 0 = 0)
    (s u : CoefficientField m) :
    ∃ q : PositiveParameters m,
      firstBlockActor m s u * wordElement m p * (firstBlockActor m s u)⁻¹ =
        wordElement m q ∧
      q.pair 0 = p.pair 0 ∧ q.main 0 = 0 ∧ q.central 0 = 0 ∧
      q.main 2 = s * p.pair 0 + p.main 2 ∧
      q.main 3 = titsEnd m s * p.main 2 + u * p.pair 0 + p.main 3 := by
  let g := firstBlockActor m s u
  let z := g * wordElement m p * g⁻¹
  have hg : g ∈ unipotent m :=
    (unipotent m).mul_mem (mainElement_mem_unipotent m 0 s)
      (ElementaryTwoBound.Y_le_unipotent m 0 (centralElement_mem_Y m 0 u))
  have hz : z ∈ unipotent m := (unipotent m).mul_mem
    ((unipotent m).mul_mem hg (wordElement_mem_unipotent m p)) ((unipotent m).inv_mem hg)
  obtain ⟨q, hq⟩ := exists_positiveWord m z hz
  have hp0 : parameters m p 0 = 0 := hmain
  have hp1 : parameters m p 1 = 0 := by simp [parameters, hmain]
  have hp2 : parameters m p 2 = 0 := by simp [parameters, hmain, hcentral]
  have hp3 : parameters m p 3 = 0 := hcentral
  obtain ⟨w, hw, hw0, _, _, hw3, hw22, hw18, hw6⟩ :=
    MainNormalizationCalculation.split_firstBlock_conjugate m (parameters m p)
      s (halfFrobenius m s) (s * halfFrobenius m s + halfFrobenius m u) u
      hp0 hp1 hp2 hp3
  have he : parameters m q = w := by
    apply splitWord_injective m
    calc
      splitWord m (parameters m q) = toSplitGroup m z :=
        (positiveWord_split m q).symm.trans hq.symm
      _ = splitWord m w := by
        simpa only [z, g, map_mul, map_inv, firstBlockActor_split,
          wordElement_coe, positiveWord_split] using hw
  refine ⟨q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply toSplitGroup_injective m
    exact hq.trans (wordElement_coe m q).symm
  · exact (congrFun he 22).trans hw22
  · exact (congrFun he 0).trans hw0
  · exact (congrFun he 3).trans hw3
  · exact (congrFun he 18).trans hw18
  · have h : q.main 3 = halfFrobenius m s ^ 2 * p.main 2 +
        u * p.pair 0 + p.main 3 := (congrFun he 6).trans hw6
    simpa only [halfFrobenius_sq] using h

/-- Uniform normalization of X₇ and X₃ with nonzero X₈.
This discharges the exact `MainNormalization` premise of
`outsideCConjugacy_of_coordinate_calculations`. -/
theorem mainNormalization (m : ℕ) : MainNormalization m := by
  intro p hp hmain hcentral
  let s := p.main 2 / p.pair 0
  let u := (p.main 3 + titsEnd m s * p.main 2) / p.pair 0
  obtain ⟨q, hconj, hpair, hqmain, hqcentral, hq2, hq3⟩ :=
    firstBlockActor_coordinates m p hmain hcentral s u
  refine ⟨q, isConj_iff.mpr ⟨firstBlockActor m s u, hconj⟩,
    hpair, hqmain, hqcentral, ?_, ?_⟩
  · have hs : s * p.pair 0 = p.main 2 := div_mul_cancel₀ _ hp
    rw [hq2, hs, CharTwo.add_self_eq_zero]
  · rw [hq3, show u * p.pair 0 = p.main 3 + titsEnd m s * p.main 2 from
      div_mul_cancel₀ _ hp]
    rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero, CharTwo.add_self_eq_zero]

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC
