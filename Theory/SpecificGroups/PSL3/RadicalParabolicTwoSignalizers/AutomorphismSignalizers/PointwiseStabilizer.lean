module

public import Theory.SpecificGroups.PSL3.RadicalParabolicTwoSignalizers.Centralizers
public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Pointwise stabilizers of PSL₃(5) parabolic radicals

Standard automorphism coverage, with simplicity and nonsolvability supplied by
ATLAS, reduces every automorphism to an inner factor and inverse transpose.
Field automorphisms of ZMod 5 are trivial. Scalar multiplication removes the
linear determinant, since every unit has fourth power one.

An inner-times-graph automorphism fixing a radical pointwise would give
u x uᵀ = x for its two coordinate roots. On the line side these equations kill
the last row of x; on the point side they kill its lower 2-by-2 block. Both
contradict determinant one. Thus every pointwise stabilizer is inner.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, proof 1.3.8, printed p.513;
the imported automorphism coverage proves the A₂ case of GLS3, Theorem 2.5.12.
The imported ATLAS simplicity and perfection results retain their source
attribution and license in `Theory.AtlasPort.ExceptionalIsomorphisms`.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix.PSL3.OuterSolvable Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.RadicalParabolicTwoSignalizers
local notation "𝔽" => ZMod 5

private theorem linearConj_scalar (u : 𝔽ˣ) :
    linearConj 𝔽 (GeneralLinearGroup.scalar (Fin 3) u) = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := projection_surjective 𝔽 y
  change QuotientGroup.mk (linearConjSL 𝔽 _ x) = QuotientGroup.mk x
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL, GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]

private theorem innerDiagonal_eq_inner :
    innerDiagonal 𝔽 = MulAut.innerSubgroup Model := by
  apply le_antisymm _ (inner_le_innerDiagonal 𝔽)
  rintro _ ⟨g, rfl⟩
  let d := GeneralLinearGroup.det g
  have hd : d ^ 4 = 1 := (by decide : ∀ u : (ZMod 5)ˣ, u ^ 4 = 1) d
  let x : (GeneralLinearGroup.det : GL (Fin 3) 𝔽 →* 𝔽ˣ).ker :=
    ⟨GeneralLinearGroup.scalar (Fin 3) d * g, by
      change GeneralLinearGroup.det _ = 1
      rw [map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin]
      change d ^ 3 * d = 1
      rw [← pow_succ]
      exact hd⟩
  refine ⟨QuotientGroup.mk ((slEquivDetKernel 𝔽).symm x), ?_⟩
  rw [← linearConj_toGL, slEquivDetKernel_symm_toGL]
  change linearConj 𝔽 (GeneralLinearGroup.scalar (Fin 3) d * g) = _
  rw [map_mul, linearConj_scalar, one_mul]

private theorem one_or_graph {α : MulAut Model} (hα : α ∈ zpowers (graph 𝔽)) :
    α = 1 ∨ α = graph 𝔽 := by
  have hsq : graph 𝔽 * graph 𝔽 = 1 := by simpa only [pow_two] using graph_sq 𝔽
  have hinv : (graph 𝔽)⁻¹ = graph 𝔽 := inv_eq_of_mul_eq_one_left hsq
  let H : Subgroup (MulAut Model) :=
    { carrier := {α | α = 1 ∨ α = graph 𝔽}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (rfl | rfl) (rfl | rfl) <;> simp [hsq]
      inv_mem' := by
        rintro a (rfl | rfl) <;> simp [hinv] }
  exact (zpowers_le.mpr (show graph 𝔽 ∈ H from Or.inr rfl)) hα

/-- Every automorphism of PSL₃(5) is inner or inner times inverse transpose. -/
theorem automorphism_normal_form (α : MulAut Model) :
    ∃ g : Model, α = MulAut.conj g ∨ α = MulAut.conj g * graph 𝔽 := by
  let : IsSimpleGroup Model := Atlas.psl_simple_high_rank 3 (by decide)
  let : Group.IsPerfect Model := Atlas.psl_perfect 3 (by decide)
  have hc := standard_eq_top_of_odd_prime_card 𝔽
    (Group.IsPerfect.not_isSolvable Model) (by decide : Nat.Prime 5)
    (by decide : Odd 5) (Nat.card_zmod 5)
  have hf : (fieldAction 𝔽).range = ⊥ := by
    apply eq_bot_iff.mpr
    rintro _ ⟨σ, rfl⟩
    rw [Subsingleton.elim σ 1, map_one]
    exact one_mem _
  rw [standard, innerDiagonal_eq_inner, hf, sup_bot_eq] at hc
  have hα : α ∈ MulAut.innerSubgroup Model ⊔ zpowers (graph 𝔽) := hc ▸ mem_top α
  obtain ⟨_, ⟨g,rfl⟩, β, hβ, rfl⟩ := mem_sup_of_normal_left.mp hα
  refine ⟨g, ?_⟩
  rcases one_or_graph hβ with rfl | rfl
  · exact Or.inl (mul_one _)
  · exact Or.inr rfl

private theorem no_graph_fixes_rootPlane (point : Bool) (g : Model)
    (h : ∀ u ∈ rootPlane 𝔽 point, (MulAut.conj g * graph 𝔽) u = u) : False := by
  obtain ⟨x,rfl⟩ := projection_surjective 𝔽 g
  have heq (u : SL(3,𝔽)) (hu : u ∈ rootPlaneSL 𝔽 point) :
      u * x * SpecialLinearGroup.transpose u = x := by
    have he := h (projection 𝔽 u) (mem_map_of_mem (projection 𝔽) hu)
    have he' : x * (SpecialLinearGroup.transpose u)⁻¹ * x⁻¹ = u := by
      apply projection_injective
      exact he
    calc
      u * x * SpecialLinearGroup.transpose u =
          (x * (SpecialLinearGroup.transpose u)⁻¹ * x⁻¹) * x *
            SpecialLinearGroup.transpose u := by rw [he']
      _ = x := by group
  have hdet := x.property
  rw [Matrix.det_fin_three] at hdet
  cases point
  · have entries (b c : 𝔽) (i j : Fin 3) :
        ((matrix 𝔽 ⟨0,b,c⟩ * x.val) * (matrix 𝔽 ⟨0,b,c⟩).transpose) i j = x.val i j :=
      congrArg (fun y : SL(3,𝔽) => y.val i j)
        (heq _ ((mem_rootPlaneSL_line 𝔽 _).mpr ⟨b,c,rfl⟩))
    have h20 := entries 1 0 1 0
    have h21 := entries 0 1 0 1
    have h22 := entries 1 0 1 2
    simp [matrix, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at h20 h21 h22
    simp [h20,h21,h22] at hdet
  · have entries (a c : 𝔽) (i j : Fin 3) :
        ((matrix 𝔽 ⟨a,0,c⟩ * x.val) * (matrix 𝔽 ⟨a,0,c⟩).transpose) i j = x.val i j :=
      congrArg (fun y : SL(3,𝔽) => y.val i j)
        (heq _ ((mem_rootPlaneSL_point 𝔽 _).mpr ⟨a,c,rfl⟩))
    have h11 := entries 1 0 0 1
    have h12 := entries 1 0 0 2
    have h21 := entries 0 1 0 1
    have h22 := entries 0 1 0 2
    simp [matrix, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at h11 h12 h21 h22
    simp [h11,h12,h21,h22] at hdet

/-- Pointwise stabilizers of either radical contain only inner automorphisms. -/
theorem fixes_rootPlane_is_inner (point : Bool) (α : MulAut Model)
    (h : ∀ u ∈ rootPlane 𝔽 point, α u = u) :
    α ∈ MulAut.innerSubgroup Model := by
  obtain ⟨g, rfl | rfl⟩ := automorphism_normal_form α
  · exact ⟨g,rfl⟩
  · exact (no_graph_fixes_rootPlane point g h).elim

end Matrix.PSL3.RadicalParabolicTwoSignalizers
