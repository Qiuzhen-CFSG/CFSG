module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularCoefficients
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularAdjacent

/-!
# The perpendicular Suzuki angular commutations

The split-root commutation of the first and fifth main curves extends to
whole root groups by closure. The linear reflection transports it to the
third and seventh angular roots, retaining both Suzuki parameters at q=2.

Source: GLS3 Table 2.4 and 2.4.5(d); Fong--Seitz II, (10.2)(iv).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.AlgebraicGroup StandardRootSystem
namespace ReeF4.RootPresentationRecognition.AngularSuzukiCommute
open ReeF4 CentralCovers.TwoPrimary ElementaryTwoBound ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics MatrixRelations MatrixRelations.LongCommutators Parabolics.RadicalCoordinates.FixedCoordinates
open SignedGeometry
private theorem fieldEnd_half (m : ℕ) (i : Fin 8) :
    rootFieldEnd m (longRoot i) = halfFrobenius m := by
  simp only [rootFieldEnd, if_pos (longRoot_isLong i), halfFrobenius]

private theorem word_0 (m : ℕ) (t : CoefficientField m) :
    rootWord m 0 t = MatrixRelations.LongCommutators.X m 0 t * MatrixRelations.LongCommutators.X m 1 (halfFrobenius m t) * MatrixRelations.LongCommutators.X m 2 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  rfl

private theorem word_4 (m : ℕ) (t : CoefficientField m) :
    rootWord m 4 t = MatrixRelations.LongCommutators.X m 12 t * MatrixRelations.LongCommutators.X m 13 (halfFrobenius m t) * MatrixRelations.LongCommutators.X m 14 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  rfl

private theorem commute_0_4 (m : ℕ) (t u : CoefficientField m) :
    Commute (rootWord m 0 t) (rootWord m 4 u) := by
  rw [word_0, word_4]
  exact (((((xc m 0 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (u)).mul_right (xc m 0 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (halfFrobenius m u))).mul_right (xc m 0 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (u * halfFrobenius m u))).mul_left (((xc m 1 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (u)).mul_right (xc m 1 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (halfFrobenius m u))).mul_right (xc m 1 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (u * halfFrobenius m u)))).mul_left (((xc m 2 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t * halfFrobenius m t) (u)).mul_right (xc m 2 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t * halfFrobenius m t) (halfFrobenius m u))).mul_right (xc m 2 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t * halfFrobenius m t) (u * halfFrobenius m u))))


/-- Whole perpendicular Suzuki roots commute in the native model. -/
theorem native_perpendicular_commute (m : ℕ) (x : ElementaryTwoBound.X m 0) (y : ElementaryTwoBound.X m 4) :
    Commute (x : Model m) (y : Model m) := by
  have hc (t u : CoefficientField m) :
      Commute (mainElement m 0 t) (mainElement m 4 u) :=
    Subtype.ext (commute_0_4 m t u).eq
  have hle (t : CoefficientField m) : ElementaryTwoBound.X m 4 ≤ centralizer {mainElement m 0 t} := by
    apply (closure_le _).mpr
    rintro _ ⟨u,rfl⟩
    exact mem_centralizer_singleton_iff.mpr (hc t u).symm
  have hle' : ElementaryTwoBound.X m 0 ≤ centralizer {(y : Model m)} := by
    apply (closure_le _).mpr
    rintro _ ⟨t,rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp (hle t y.property)).symm
  exact mem_centralizer_singleton_iff.mp (hle' x.property)

variable (m : ℕ)
local notation "S" i:max a:max b:max => (PositiveTables.quartet m i a b : Model m)
private theorem quartet_reflect (s : Bool) (i : Fin 4)
    (h : (step true s (true,i)).1 = true) (a b : CoefficientField m) :
    MulAut.conj (reflection m (NormalizerPresentation.side s)) (S i a b) = S (next true s i) a b := by
  have hh := SignedCharts.reflection_quartet m s (true,i) a b
  rw [show step true s (true,i) = (true,next true s i) from Prod.ext h rfl] at hh
  exact hh

/-- The two perpendicular Suzuki pairs, with all four field labels. -/
theorem suzuki_commute_family (a b u v : CoefficientField m) :
    Commute (S 0 a b) (S 1 u v) ∧ Commute (S 3 a b) (S 2 u v) := by
  have hc (a b u v : CoefficientField m) : Commute (S 0 a b) (S 1 u v) := by
    rw [PositiveTables.quartet_blockPoint,PositiveTables.quartet_blockPoint]
    simp only [rootIndex,positive_quartet_indices,Fin.isValue]
    exact native_perpendicular_commute m
      ⟨_, (mem_X_even m 0 (by decide) _).mpr ⟨a,b,rfl⟩⟩
      ⟨_, (mem_X_even m 4 (by decide) _).mpr ⟨u,v,rfl⟩⟩
  refine ⟨hc a b u v, ?_⟩
  have hh := congrArg (MulAut.conj (reflection m (NormalizerPresentation.side false))) (hc u v a b).eq
  change _ * _ = _ * _
  simpa only [map_mul,quartet_reflect m false 0 (by decide),
    quartet_reflect m false 1 (by decide),next,Matrix.cons_val,Fin.isValue,
    Matrix.head_cons] using hh.symm

end ReeF4.RootPresentationRecognition.AngularSuzukiCommute
