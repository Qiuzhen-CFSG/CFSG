module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.Branches
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC.Collection
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.BinaryRootNormalization.WeylTransport

/-!
# The five-parameter outside-C slice consists of short-root involutions

For a nonzero a, every x₈(a) x₆(b) x₄(c) y₅(d) y₇(e) is conjugate to x₈(a)
by an explicit positive element x₂(s) x₃(t) y₃(u) x₅(v). We solve the four
coordinate equations in triangular order. The checked split-root calculation
and uniqueness of positive fixed coordinates identify the resulting element;
the fixed Weyl word then carries x₈(a) to the literal short-root curve x₄(a).
No involution-class or square hypothesis enters this calculation.

Source: GLS3 Table 2.4 and 2.4.5(d), refs/KGroup/GLS3/chapter2.tex;
the involution-class input to Guralnick--Malle Lemma 8.8, internal p.57.
-/

@[expose] public section
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC
open Parabolics EvenInvolutionGeometry ElementaryTwoBound ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent
open NormalizedRootCentralizers.CenterExponent.OuterElimination
open Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations.LongCommutators

/-- Coordinates of the five-parameter slice x₈(a) x₆(b) x₄(c) y₅(d) y₇(e). -/
def sliceParameters (m : ℕ) (a b c d e : CoefficientField m) : PositiveParameters m :=
  ⟨![a, 0, b, c], 0, ![0, d, e, 0]⟩

/-- The slice uses the literal source curves in the published positive order. -/
theorem wordElement_slice_eq_product (m : ℕ) (a b c d e : CoefficientField m) :
    wordElement m (sliceParameters m a b c d e) =
      mainElement m 7 a * mainElement m 5 b * mainElement m 3 c *
        centralElement m 4 d * centralElement m 6 e := by
  simp [wordElement, sliceParameters, positive_pair_indices, positive_quartet_indices,
    pairCount, quartetCount, List.ofFn_succ, mul_assoc]

/-- The unipotent actor used to reach that slice. -/
def sliceActor (m : ℕ) (s t u v : CoefficientField m) : Model m :=
  mainElement m 1 s * mainElement m 2 t * centralElement m 2 u * mainElement m 4 v

private theorem fieldEnd_half (m : ℕ) (i : Fin 8) :
    rootFieldEnd m (longRoot i) = halfFrobenius m := by
  ext t
  rw [MatrixRelations.rootFieldEnd_longRoot]
  rfl

private theorem word_two (m : ℕ) (a : CoefficientField m) :
    rootWord m 2 a = X m 6 a * X m 7 (halfFrobenius m a) *
      X m 8 (a * halfFrobenius m a) := by
  simp only [rootWord, fieldEnd_half]
  rfl

private theorem word_four (m : ℕ) (a : CoefficientField m) :
    rootWord m 4 a = X m 12 a * X m 13 (halfFrobenius m a) *
      X m 14 (a * halfFrobenius m a) := by
  simp only [rootWord, fieldEnd_half]
  rfl

private theorem word_seven (m : ℕ) (a : CoefficientField m) :
    rootWord m 7 a = X m 22 a * X m 23 (halfFrobenius m a) := by
  simp only [rootWord, fieldEnd_half]
  exact mul_one _

private theorem central_two (m : ℕ) (a : CoefficientField m) :
    centralWord m 2 a = X m 9 a * X m 8 (halfFrobenius m a) := by
  simp only [centralWord, fieldEnd_half]
  rfl

attribute [local irreducible] MatrixRelations.LongCommutators.X

private theorem collected_actor (m : ℕ) (a s t u v : CoefficientField m) :
    toSplitGroup m (sliceActor m s t u v * mainElement m 7 a *
      (sliceActor m s t u v)⁻¹) =
    splitWord m ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      a * titsEnd m s, s * halfFrobenius m a, 0, 0,
      halfFrobenius m u * halfFrobenius m a +
        halfFrobenius m s * halfFrobenius m t * a +
        halfFrobenius m s * halfFrobenius m v * halfFrobenius m a +
        t * halfFrobenius m t * halfFrobenius m a,
      u * a + s * t * titsEnd m a + s * v * a + t * a * titsEnd m t,
      s * titsEnd m a + a * titsEnd m t,
      halfFrobenius m s * a + t * halfFrobenius m a, 0, 0,
      halfFrobenius m t * a + halfFrobenius m v * halfFrobenius m a,
      t * titsEnd m a + v * a, a, halfFrobenius m a] := by
  simp only [map_mul, map_inv, sliceActor, mainElement_coe, centralElement_coe,
    word_1, word_two, word_four, word_seven, central_two, mul_inv_rev, xi]
  simpa only [Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk,
    halfFrobenius_sq, mul_assoc, mul_one] using
    Collection.conjugator_split m
      ![s, halfFrobenius m s, t, halfFrobenius m t,
        u, halfFrobenius m u, v, halfFrobenius m v, a, halfFrobenius m a,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The complete parameter formula for conjugation by the displayed actor. -/
theorem sliceActor_conjugate (m : ℕ) (a s t u v : CoefficientField m) :
    sliceActor m s t u v * mainElement m 7 a * (sliceActor m s t u v)⁻¹ =
      wordElement m (sliceParameters m a
        (s * titsEnd m a + titsEnd m t * a) (titsEnd m s * a)
        (s * t * titsEnd m a + s * v * a + t * titsEnd m t * a + u * a)
        (t * titsEnd m a + v * a)) := by
  let z := sliceActor m s t u v * mainElement m 7 a * (sliceActor m s t u v)⁻¹
  have hg : sliceActor m s t u v ∈ unipotent m := by
    exact (unipotent m).mul_mem ((unipotent m).mul_mem
      ((unipotent m).mul_mem (mainElement_mem_unipotent m 1 s)
        (mainElement_mem_unipotent m 2 t))
      (Y_le_unipotent m 2 (centralElement_mem_Y m 2 u)))
      (mainElement_mem_unipotent m 4 v)
  have hz : z ∈ unipotent m := (unipotent m).mul_mem
    ((unipotent m).mul_mem hg (mainElement_mem_unipotent m 7 a))
    ((unipotent m).inv_mem hg)
  obtain ⟨p, hp⟩ := exists_positiveWord m z hz
  have he := splitWord_injective m
    ((positiveWord_split m p).symm.trans (hp.symm.trans (collected_actor m a s t u v)))
  have hpair : p.pair = ![a, 0, s * titsEnd m a + titsEnd m t * a,
      titsEnd m s * a] := by
    funext j
    fin_cases j
    · exact congrFun he 22
    · exact congrFun he 4
    · have h : p.pair 2 = s * titsEnd m a + a * titsEnd m t := congrFun he 16
      change p.pair 2 = s * titsEnd m a + titsEnd m t * a
      simpa only [mul_comm] using h
    · have h : p.pair 3 = a * titsEnd m s := congrFun he 10
      change p.pair 3 = titsEnd m s * a
      simpa only [mul_comm] using h
  have hmain : p.main = 0 := by
    funext j
    fin_cases j
    · exact congrFun he 0
    · exact congrFun he 12
    · exact congrFun he 18
    · exact congrFun he 6
  have hcentral : p.central = ![0,
      s * t * titsEnd m a + s * v * a + t * titsEnd m t * a + u * a,
      t * titsEnd m a + v * a, 0] := by
    funext j
    fin_cases j
    · exact congrFun he 3
    · have h : p.central 1 = u * a + s * t * titsEnd m a + s * v * a +
          t * a * titsEnd m t := congrFun he 15
      change p.central 1 =
        s * t * titsEnd m a + s * v * a + t * titsEnd m t * a + u * a
      rw [h]
      ring
    · exact congrFun he 21
    · exact congrFun he 9
  have hparams : p = sliceParameters m a
      (s * titsEnd m a + titsEnd m t * a) (titsEnd m s * a)
      (s * t * titsEnd m a + s * v * a + t * titsEnd m t * a + u * a)
      (t * titsEnd m a + v * a) := by
    cases p
    simp_all only [sliceParameters]
  apply toSplitGroup_injective m
  rw [wordElement_coe, ← hparams]
  exact hp

/-- All four tail parameters are reached by actual positive conjugation. -/
theorem exists_sliceActor (m : ℕ) (a b c d e : CoefficientField m) (ha : a ≠ 0) :
    ∃ g : Model m, g * mainElement m 7 a * g⁻¹ =
      wordElement m (sliceParameters m a b c d e) := by
  let s := halfFrobenius m (c / a)
  let t := halfFrobenius m ((b + s * titsEnd m a) / a)
  let v := (e + t * titsEnd m a) / a
  let u := (d + s * e + t * titsEnd m t * a) / a
  refine ⟨sliceActor m s t u v, ?_⟩
  have hs : titsEnd m s * a = c := by
    simp only [s, titsEnd_halfFrobenius, div_mul_cancel₀ _ ha]
  have ht : s * titsEnd m a + titsEnd m t * a = b := by
    simp only [t, titsEnd_halfFrobenius, div_mul_cancel₀ _ ha]
    rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
  have hv : t * titsEnd m a + v * a = e := by
    simp only [v, div_mul_cancel₀ _ ha]
    rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
  have hu : s * t * titsEnd m a + s * v * a + t * titsEnd m t * a + u * a = d := by
    simp only [u, div_mul_cancel₀ _ ha]
    have hse : s * t * titsEnd m a + s * v * a = s * e := by
      rw [← hv]
      ring
    rw [hse]
    abel_nf
    simp [CharTwo.two_eq_zero]
  rw [sliceActor_conjugate, hs, ht, hv, hu]

/-- The fixed Weyl actor identifies the eighth curve with the specified short curve. -/
theorem eighth_isConj_short (m : ℕ) (a : CoefficientField m) :
    IsConj (mainElement m 7 a) (shortRootElement m a) := by
  apply isConj_iff.mpr
  refine ⟨Normalization.shortWeyl m, ?_⟩
  apply toSplitGroup_injective m
  simp only [map_mul, map_inv, mainElement_coe, shortRootElement_coe, rootWord_end]
  exact Normalization.shortWeyl_conjugate m a

/-- The entire five-parameter slice is in the actual short-root involution class. -/
theorem slice_isShortRootInvolution (m : ℕ) (a b c d e : CoefficientField m)
    (ha : a ≠ 0) :
    IsShortRootInvolution (wordElement m (sliceParameters m a b c d e)) := by
  refine ⟨a, ha, (eighth_isConj_short m a).symm.trans ?_⟩
  exact isConj_iff.mpr (exists_sliceActor m a b c d e ha)

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC
