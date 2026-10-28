module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularCoefficients
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularAdjacent

/-!
# Five commuting linear angular pairs

The middle linear roots commute by the split-root calculation; a second
split-root calculation gives perpendicular linear commutation. The supplied
reflections transport these two identities to all five commuting linear pairs.
The excluded extreme pair is left to the full Section 10 calculation.

Source: Fong--Seitz II, Section 10, (10.2)(iv), (10.3), and Weyl transport;
GLS3 Table 2.4 and 2.4.5(d).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup ReeF4
namespace ReeF4.RootPresentationRecognition.AngularLinearCommute
open CentralCovers.TwoPrimary ElementaryTwoBound ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics MatrixRelations
open Parabolics.RadicalCoordinates.FixedCoordinates
open SignedGeometry
variable (m : ℕ)
local notation "L" i:max a:max => (PositiveTables.pair m i a : Model m)
private theorem pair_eq (i : Fin 4) (a : CoefficientField m) :
    L i a = mainElement m (![7,1,5,3] i) a := by
  rw [PositiveTables.pair_main]
  simp only [rootIndex, Sum.elim_inl, positive_pair_indices]

private theorem pair_reflect (s : Bool) (i : Fin 4)
    (h : (step false s (true,i)).1 = true) (a : CoefficientField m) :
    MulAut.conj (reflection m (NormalizerPresentation.side s)) (L i a) = L (next false s i) a := by
  have hh := SignedCharts.reflection_pair m s (true,i) a
  rw [show step false s (true,i) = (true,next false s i) from Prod.ext h rfl] at hh
  exact hh

private theorem linear3_linear2 (x y : CoefficientField m) : Commute (L 3 x) (L 2 y) := by
  rw [pair_eq,pair_eq]
  apply Subtype.ext
  change Commute (rootWord m 3 x) (rootWord m 5 y)
  open MatrixRelations.LongCommutators in
  have w3 : rootWord m 3 x = X m 10 x * X m 11 (halfFrobenius m x) := by
    simp only [rootWord,rootFieldEnd,if_pos (longRoot_isLong _),halfFrobenius]
    change _ * 1 = _
    exact mul_one _
  open MatrixRelations.LongCommutators in
  have w5 : rootWord m 5 y = X m 16 y * X m 17 (halfFrobenius m y) := by
    simp only [rootWord,rootFieldEnd,if_pos (longRoot_isLong _),halfFrobenius]
    change _ * 1 = _
    exact mul_one _
  rw [w3,w5]
  open MatrixRelations.LongCommutators Theory.AlgebraicGroup.StandardRootSystem in
  exact (((xc m 10 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) x y).mul_right
    (xc m 10 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) x (halfFrobenius m y))).mul_left
    ((xc m 11 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m x) y).mul_right
      (xc m 11 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m x) (halfFrobenius m y))))

private theorem linear3_linear0 (x y : CoefficientField m) : Commute (L 3 x) (L 0 y) := by
  rw [pair_eq,pair_eq]
  apply Subtype.ext
  change Commute (rootWord m 3 x) (rootWord m 7 y)
  open MatrixRelations.LongCommutators in
  have w3 : rootWord m 3 x = X m 10 x * X m 11 (halfFrobenius m x) := by
    simp only [rootWord,rootFieldEnd,if_pos (longRoot_isLong _),halfFrobenius]
    change _ * 1 = _
    exact mul_one _
  open MatrixRelations.LongCommutators in
  have w7 : rootWord m 7 y = X m 22 y * X m 23 (halfFrobenius m y) := by
    simp only [rootWord,rootFieldEnd,if_pos (longRoot_isLong _),halfFrobenius]
    change _ * 1 = _
    exact mul_one _
  rw [w3,w7]
  open MatrixRelations.LongCommutators Theory.AlgebraicGroup.StandardRootSystem in
  exact (((xc m 10 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) x y).mul_right
    (xc m 10 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) x (halfFrobenius m y))).mul_left
    ((xc m 11 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m x) y).mul_right
      (xc m 11 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m x) (halfFrobenius m y))))

private theorem reflect_commute (s : Bool) (i j : Fin 4)
    (hi : (step false s (true,i)).1 = true)
    (hj : (step false s (true,j)).1 = true)
    (a b : CoefficientField m) (h : Commute (L i a) (L j b)) :
    Commute (L (next false s i) a) (L (next false s j) b) := by
  have hh := h.map (MulAut.conj (reflection m (NormalizerPresentation.side s))).toMonoidHom
  simpa only [MulEquiv.coe_toMonoidHom,pair_reflect m s i hi,pair_reflect m s j hj] using hh

/-- The five linear pairs whose native angular table is a singleton. -/
theorem linear_commute_family (a b : CoefficientField m) :
    Commute (L 1 a) (L 3 b) ∧
    Commute (L 1 a) (L 2 b) ∧
    Commute (L 3 a) (L 2 b) ∧
    Commute (L 3 a) (L 0 b) ∧
    Commute (L 2 a) (L 0 b) := by
  have h13 (x y : CoefficientField m) : Commute (L 1 x) (L 3 y) := by
    simpa only [next,Matrix.cons_val,Fin.isValue,Matrix.head_cons] using
      reflect_commute m false 2 3 (by decide) (by decide) x y (linear3_linear2 m y x).symm
  have h12 : Commute (L 1 a) (L 2 b) := by
    simpa only [next,Matrix.cons_val,Fin.isValue,Matrix.head_cons] using
      reflect_commute m true 0 3 (by decide) (by decide) a b (linear3_linear0 m b a).symm
  have h20 : Commute (L 2 a) (L 0 b) := by
    simpa only [next,Matrix.cons_val,Fin.isValue,Matrix.head_cons] using
      reflect_commute m true 3 1 (by decide) (by decide) a b (h13 b a).symm
  exact ⟨h13 a b,h12,linear3_linear2 m a b,linear3_linear0 m a b,h20⟩
end ReeF4.RootPresentationRecognition.AngularLinearCommute
