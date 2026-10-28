module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.Container
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.Symmetry
public import Theory.Representation.SL5ExteriorSquare.SelfDual
public import Theory.Representation.SL5ExteriorSquare.SixDimensionalExclusion

/-!
# The intrinsic form on native F and orthogonal occurrence

Transport the intrinsic form through the actual exterior marking. The full
SL5 quotient makes it invariant under the whole exterior action. Irreducibility
would make a nonzero form an isomorphism with the dual, contradicting the
proved unequal characters. Thus the intrinsic form is zero.

Consequently each outside-E involution of Q belongs to a native F-occurrence
contained in its actual Q-intersection with the full-centralizer solvable
residual. This supplies orthogonality and occurrence as a lower bound; equality
with that residual intersection requires the remaining reverse containment.

Source: KW (1988), Proposition 2.2.2, pp.490--491, using its intrinsic relation
from Corollary 1.1.4. All residual maps are the literal subgroup embeddings.
-/
@[expose] public noncomputable section
namespace Janko4.LocalStructure.LinearFive.Geometry
open NativeNormalizer LargeCenterRadicals.OuterHalf
open Representation Representation.SL5TenDimensional Representation.SL5ExteriorSquare
open scoped IsMulCommutative
attribute [local instance] F_elementary
attribute [local irreducible] modelGroup matrixA matrixB F exteriorLinearMarking

private theorem exterior_invariant_zero (B : LinearMap.BilinForm (ZMod 2) V)
    (hinv : ∀ g x y, B (exteriorAction 2 g x) (exteriorAction 2 g y) = B x y) : B = 0 := by
  let ρ := exteriorAction 2
  let : ρ.IsIrreducible := exteriorSquare_isIrreducible
  let f : ρ.IntertwiningMap ρ.dual := {
    toLinearMap := B
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      obtain ⟨z,rfl⟩ := (ρ.apply_bijective g).surjective y
      change B (ρ g x) (ρ g z) = B x (ρ g⁻¹ (ρ g z))
      rw [hinv]
      congr 1
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl }
  rcases Representation.IsIrreducible.injective_or_eq_zero f with hf | hf
  · have hsurj : Function.Surjective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := f.toLinearMap) (by simp)).mp hf
    exact (not_selfDual_of_square_coordinates ρ (MulEquiv.refl Group)
      (LinearEquiv.refl (ZMod 2) V) (by intros; rfl) ⟨f.ofBijective ⟨hf,hsurj⟩⟩).elim
  · exact congrArg IntertwiningMap.toLinearMap hf

/-- The native exterior marking and full SL5 action force the intrinsic form on F to vanish. -/
theorem F_intrinsicForm_zero : intrinsicElementaryForm F = 0 := by
  let c := exteriorLinearMarking
  let B := LinearMap.BilinForm.congr c (intrinsicElementaryForm F)
  have hi : ∀ g x y, B (exteriorAction 2 g x) (exteriorAction 2 g y) = B x y := by
    intro g x y
    obtain ⟨n,rfl⟩ := normalizerProjection_surjective g
    obtain ⟨x,rfl⟩ := c.surjective x
    obtain ⟨y,rfl⟩ := c.surjective y
    change B (exteriorAction 2 (normalizerProjection n)
      (exteriorLinearMarking (Additive.ofMul x.toMul)))
      (exteriorAction 2 (normalizerProjection n)
      (exteriorLinearMarking (Additive.ofMul y.toMul))) = B (c x) (c y)
    rw [← normalizerProjection_linear n x.toMul, ← normalizerProjection_linear n y.toMul]
    simp only [B, LinearMap.BilinForm.congr_apply, c, LinearEquiv.symm_apply_apply]
    exact intrinsicElementaryForm_normalizer F n x y
  have hz := exterior_invariant_zero B hi
  exact (LinearMap.BilinForm.congr c).injective (hz.trans (map_zero _).symm)

/-- Orthogonality here means membership in the actual full centralizer residual. -/
theorem F_innerRelated (x y : Model) (hx : x ∈ F) (hy : y ∈ F) (hx1 : x ≠ 1) :
    InnerRelated x y := by
  apply (outerValue_eq_zero_iff x y hx1).mp
  have h := congrArg (fun B : LinearMap.BilinForm (ZMod 2) (Additive F) =>
    B (Additive.ofMul ⟨x,hx⟩) (Additive.ofMul ⟨y,hy⟩)) F_intrinsicForm_zero
  exact h

theorem secondF_innerRelated (x y : Model) (hx : x ∈ secondF) (hy : y ∈ secondF)
    (hx1 : x ≠ 1) : InnerRelated x y := by
  obtain ⟨u,hu,rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨v,hv,rfl⟩ := Subgroup.mem_map.mp hy
  apply (innerRelated_equiv (MulAut.conj seed) u v).mpr
  apply F_innerRelated u v hu hv
  intro he
  exact hx1 (by rw [he,map_one])

/-- The literal candidate in KW 2.2.2: Q intersected with the embedded
solvable residual of the full ambient involution centralizer. -/
def F_x (x : Model) : Subgroup Model :=
  Q ⊓ (Subgroup.solvableResidual (Subgroup.centralizer ({x} : Set Model))).map
    (Subgroup.centralizer ({x} : Set Model)).subtype

/-- The native subgroup is contained in the actual orthogonal subgroup at each of its involutions. -/
theorem F_le_F_x (x : Model) (hx : x ∈ F) (hx1 : x ≠ 1) : F ≤ F_x x := by
  intro y hy
  exact ⟨F_le_Q hy,F_innerRelated x y hx hy hx1⟩

theorem secondF_le_F_x (x : Model) (hx : x ∈ secondF) (hx1 : x ≠ 1) : secondF ≤ F_x x := by
  intro y hy
  exact ⟨secondF_le_Q hy,secondF_innerRelated x y hx hy hx1⟩

/-- Every source involution outside E lies in one of the two native F-groups,
and that whole group lies in its literal orthogonal subgroup. The reverse
containment in F_x, which would prove equality, is not asserted here. -/
theorem outside_involution_orthogonal_occurrence (x : Model) (hxQ : x ∈ Q)
    (hxE : x ∉ E) (hx2 : orderOf x = 2) :
    (x ∈ F ∧ F ≤ F_x x) ∨ (x ∈ secondF ∧ secondF ≤ F_x x) := by
  have hx1 : x ≠ 1 := by intro he; rw [he,orderOf_one] at hx2; omega
  have hs : x*x=1 := by simpa only [hx2,pow_two] using pow_orderOf_eq_one x
  rcases Q_square_one_occurrences x hxQ hs with h | h | h
  · exact (hxE h).elim
  · exact Or.inl ⟨h,F_le_F_x x h hx1⟩
  · exact Or.inr ⟨h,secondF_le_F_x x h hx1⟩

end Janko4.LocalStructure.LinearFive.Geometry
