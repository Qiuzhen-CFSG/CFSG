module

public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination.SplitWords

/-!
# The long Ree root curve centralizes the positive subgroup

The two split roots of `y₅(t)` have nonnegative inner product with every
positive root. The characteristic-two Chevalley commutation formulas therefore
make both factors commute with each factor of the unique positive word.
Transport through the actual fixed-group embedding gives centrality in U.

Source: GLS3 Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`;
Aschbacher–Smith 16.1.6 and 16.5.13, printed pp.1172 and 1201–1202
of `refs/quasithin.pdf`.
-/

public section
noncomputable section
namespace ReeF4.EvenInvolutionGeometry
open Theory.AlgebraicGroup StandardRootSystem
open Parabolics
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics.RadicalCoordinates.FixedCoordinates
open MatrixRelations.LongCommutators
open NormalizedRootCentralizers.CenterExponent
open NormalizedRootCentralizers.CenterExponent.OuterElimination
attribute [local irreducible] X

private theorem top_geometry (i : Fin 24) (hi : i = 14 ∨ i = 15) (j : Fin 24) :
    0 ≤ dot (V i) (V j) := by
  rcases hi with rfl | rfl <;> fin_cases j <;>
    norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem top_commutes_splitWord (m : ℕ) (i : Fin 24) (hi : i = 14 ∨ i = 15)
    (t : CoefficientField m) (v : Fin 24 → CoefficientField m) :
    Commute (X m i t) (splitWord m v) := by
  have h (j : Fin 24) : Commute (X m i t) (X m j (v j)) :=
    xc m i j (top_geometry i hi j) t (v j)
  exact (h 22).mul_right ((h 23).mul_right ((h 4).mul_right ((h 5).mul_right ((h 16).mul_right ((h 17).mul_right ((h 10).mul_right ((h 11).mul_right ((h 0).mul_right ((h 1).mul_right ((h 2).mul_right ((h 3).mul_right ((h 12).mul_right ((h 13).mul_right ((h 14).mul_right ((h 15).mul_right ((h 18).mul_right ((h 19).mul_right ((h 20).mul_right ((h 21).mul_right ((h 6).mul_right ((h 7).mul_right ((h 8).mul_right ((h 9).mul_right (Commute.one_right _))))))))))))))))))))))))

private theorem central_four (m : ℕ) (t : CoefficientField m) :
    centralWord m 4 t = X m 15 t * X m 14 (halfFrobenius m t) := by
  simp only [centralWord, rootFieldEnd, if_pos (MatrixRelations.longRoot_isLong 4),
    halfFrobenius]
  unfold X
  rfl

/-- Every element of the actual long-root curve centralizes the standard U.
The calculation also includes the binary endpoint. -/
theorem longRootElement_commute_unipotent (m : ℕ) (t : CoefficientField m)
    (x : Model m) (hx : x ∈ unipotent m) : Commute (longRootElement m t) x := by
  obtain ⟨p, hp⟩ := exists_positiveWord m x hx
  apply toSplitGroup_injective m
  simp only [map_mul, longRootElement_coe, hp, positiveWord_split, central_four]
  exact ((top_commutes_splitWord m 15 (Or.inr rfl) t _).mul_left
    (top_commutes_splitWord m 14 (Or.inl rfl) (halfFrobenius m t) _)).eq

end ReeF4.EvenInvolutionGeometry
