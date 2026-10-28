module

public import Theory.Representation.BinaryParabolicExteriorSquare.Simplicity
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.Assembly
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.RadicalGeometry.FixedSpaces

/-!
# The hyperplane exterior-square calculation in C.4.8

For the actual perfect hyperplane parabolic M₀ of SL₅(F₂), its two-core is
the last-column shear subgroup. Its fixed space in Λ²(F₂⁵) is V₆ = Λ²(F₂⁴).
The upper-block projection is onto SL₄(F₂), and elementary transvections
show that [V₆,M₀] = V₆. The six-space is simple and its Pfaffian isometry
intertwines the literal upper-block action with Ω⁺₆(2).

The marking theorems apply these calculations to any equivariantly identified
exterior representation. They retain the original action operators, calculate
the actual fixed-space commutator and its dimension, and prove that each
nonzero invariant submodule of that commutator is the whole six-space.

The core used here is O₂(M₀), not a stipulated radical: the equality with
the §12.5 source radical follows from the proved perfection of this endpoint.
Source: Aschbacher--Smith, C.4.8, final paragraph, printed p.154;
B.4.2(10),(11), printed p.86; K.3.2.3 and Lemma 12.5.2(4).
The imported orthogonal comparison uses the attributed ATLAS exterior model.
-/

@[expose] public section
open Atlas.Order20160A8.Bivectors
open scoped MatrixGroups
namespace Representation.BinaryParabolicExteriorSquare
noncomputable section

open SL5ExteriorSquare SL5TenDimensional

/-- The upper block is onto the literal SL₄(2) matrix group. -/
theorem exists_upperBlock (a : SL(4, Bit)) :
    ∃ g : parabolic 4, upperBlock g.val = a.val := by
  obtain ⟨q, hq⟩ := parabolicFourResidualQuotientEquiv.surjective a
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ q
  rw [parabolicFourResidualQuotientEquiv_mk] at hq
  exact ⟨Subgroup.inclusion (parabolicResidual_le 4) g, congrArg Subtype.val hq⟩

/-- Simplicity on the actual six-dimensional exterior submodule. -/
theorem sixSpace_simple (P : Submodule Bit V₆)
    (hP : ∀ g : parabolic 4, ∀ x ∈ P, v6Action g x ∈ P)
    (hne : P ≠ ⊥) : P = ⊤ := by
  have he : P.map v6Coordinates.toLinearMap = ⊤ := by
    apply six_simple
    · intro a x hx
      obtain ⟨v, hv, rfl⟩ := hx
      obtain ⟨g, hg⟩ := exists_upperBlock a
      refine ⟨v6Action g v, hP g v hv, ?_⟩
      exact (v6Coordinates_action g v).trans (congrArg (fun A => exteriorMap A _) hg)
    · intro hz
      apply hne
      apply (Submodule.eq_bot_iff P).mpr
      intro x hx
      have hx' : v6Coordinates x ∈ P.map v6Coordinates.toLinearMap := ⟨x, hx, rfl⟩
      rw [hz, Submodule.mem_bot] at hx'
      exact v6Coordinates.map_eq_zero_iff.mp hx'
  apply top_unique
  intro x _
  have hx : v6Coordinates x ∈ P.map v6Coordinates.toLinearMap := by rw [he]; trivial
  obtain ⟨y, hy, heq⟩ := hx
  exact (v6Coordinates.injective heq) ▸ hy

/-- The actual two-core of the perfect hyperplane component. -/
theorem hyperplane_component_core :
    (pCore 2 (parabolicResidual 4)).map (parabolicResidual 4).subtype = shearSubgroup := by
  rw [parabolicResidual_four, parabolic_twoCore_eq_unipotent,
    parabolicUnipotent_four_eq_shearSubgroup]

/-- The fixed space required by C.4.8 is literally Λ²Γ₄. -/
theorem hyperplane_component_fixed :
    BinaryOffender.fixedSpace (exteriorAction 2)
      ((pCore 2 (parabolicResidual 4)).map (parabolicResidual 4).subtype) = V₆ := by
  rw [hyperplane_component_core, fixedSpace_shearSubgroup]

/-- The perfect hyperplane component generates all of its six-space by commutators. -/
theorem hyperplane_component_commutator :
    BinaryOffender.subspaceCommutator (exteriorAction 2) V₆ (parabolicResidual 4) = V₆ := by
  rw [parabolicResidual_four]
  let C := BinaryOffender.subspaceCommutator (exteriorAction 2) V₆ (parabolic 4)
  have hle : C ≤ V₆ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, v, hv, rfl⟩
    exact V₆.sub_mem (v6Action (⟨g,hg⟩ : parabolic 4) ⟨v,hv⟩).property hv
  have hinv (g : parabolic 4) : C ≤ C.comap (exteriorAction 2 g.val) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, v, hv, rfl⟩
    have hga : exteriorAction 2 (g.val * a) v - v ∈ C :=
      Submodule.subset_span ⟨g.val * a, (parabolic 4).mul_mem g.property ha, v, hv, rfl⟩
    have hg : exteriorAction 2 g.val v - v ∈ C :=
      Submodule.subset_span ⟨g.val, g.property, v, hv, rfl⟩
    change exteriorAction 2 g.val (exteriorAction 2 a v - v) ∈ C
    have he : exteriorAction 2 g.val (exteriorAction 2 a v - v) =
        (exteriorAction 2 (g.val * a) v - v) - (exteriorAction 2 g.val v - v) := by
      rw [map_sub, map_mul, Module.End.mul_apply]
      abel
    rw [he]
    exact C.sub_mem hga hg
  let P := C.comap V₆.subtype
  have hp : P = ⊤ := by
    apply sixSpace_simple
    · intro g x hx
      exact hinv g hx
    · obtain ⟨g, hg⟩ := exists_upperBlock
        (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 4)) (j := 2) (by decide) 1)
      let v : V₆ := v6Coordinates.symm (Pi.single 3 1)
      apply (Submodule.ne_bot_iff P).mpr
      refine ⟨v6Action g v - v, ?_, ?_⟩
      · exact Submodule.subset_span ⟨g.val, g.property, v.val, v.property, rfl⟩
      · intro hz
        have hc := congrArg v6Coordinates hz
        rw [map_sub, v6Coordinates_action, hg, map_zero] at hc
        have hv : v6Coordinates v = Pi.single 3 1 := v6Coordinates.apply_symm_apply _
        rw [hv] at hc
        exact six_transvection_nontrivial (sub_eq_zero.mp hc)
  apply le_antisymm hle
  intro v hv
  have hpv : (⟨v,hv⟩ : V₆) ∈ P := by rw [hp]; trivial
  exact hpv

/-- The literal fixed-space commutator in the exterior SL₅ hyperplane case. -/
theorem hyperplane_fixed_commutator :
    BinaryOffender.subspaceCommutator (exteriorAction 2)
      (BinaryOffender.fixedSpace (exteriorAction 2)
        ((pCore 2 (parabolicResidual 4)).map (parabolicResidual 4).subtype))
      (parabolicResidual 4) = V₆ := by
  rw [hyperplane_component_fixed, hyperplane_component_commutator]

/-- The C.4.8 fixed-space commutator, using the two-core of M itself. -/
def fixedCommutator {G U : Type*} [_root_.Group G] [AddCommGroup U] [Module Bit U]
    (ρ : Representation Bit G U) (M : Subgroup G) : Submodule Bit U :=
  BinaryOffender.subspaceCommutator ρ
    (BinaryOffender.fixedSpace ρ ((pCore 2 M).map M.subtype)) M

/-- A marking of an exterior representation transports the computed W, with no
fixed-space or commutator conclusion imposed on the marking. -/
theorem hyperplane_marked_fixedCommutator {U : Type*} [AddCommGroup U] [Module Bit U]
    (ρ : Representation Bit SL5TenDimensional.Group U) (e : U ≃ₗ[Bit] V)
    (he : ∀ g u, e (ρ g u) = exteriorAction 2 g (e u)) :
    (fixedCommutator ρ (parabolicResidual 4)).map e.toLinearMap = V₆ := by
  have hf (A : Subgroup SL5TenDimensional.Group) :
      (BinaryOffender.fixedSpace ρ A).map e.toLinearMap =
        BinaryOffender.fixedSpace (exteriorAction 2) A := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩ g
      change exteriorAction 2 g.val (e u) = e u
      rw [← he]
      exact congrArg e (hu g)
    · intro hv
      refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
      intro g
      apply e.injective
      change e (ρ g.val (e.symm v)) = e (e.symm v)
      rw [he, e.apply_symm_apply]
      exact hv g
  have hc (A : Subgroup SL5TenDimensional.Group) (D : Submodule Bit U) :
      (BinaryOffender.subspaceCommutator ρ D A).map e.toLinearMap =
        BinaryOffender.subspaceCommutator (exteriorAction 2) (D.map e.toLinearMap) A := by
    simp only [BinaryOffender.subspaceCommutator, Submodule.map_span]
    congr 1
    ext v
    constructor
    · rintro ⟨_, ⟨g, hg, u, hu, rfl⟩, rfl⟩
      exact ⟨g, hg, e u, ⟨u, hu, rfl⟩, by simp [he]⟩
    · rintro ⟨g, hg, _, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨ρ g u - u, ⟨g, hg, u, hu, rfl⟩, by simp [he]⟩
  rw [fixedCommutator, hc, hf, hyperplane_fixed_commutator]

/-- The marked source W is linearly identified with the actual orthogonal six-space. -/
def hyperplane_marked_equiv {U : Type*} [AddCommGroup U] [Module Bit U]
    (ρ : Representation Bit SL5TenDimensional.Group U) (e : U ≃ₗ[Bit] V)
    (he : ∀ g u, e (ρ g u) = exteriorAction 2 g (e u)) :
    fixedCommutator ρ (parabolicResidual 4) ≃ₗ[Bit] V₆ :=
  e.ofSubmodules _ _ (hyperplane_marked_fixedCommutator ρ e he)

/-- The transported operator on the actual fixed-space commutator. Its value
is checked against the original representation below. -/
def hyperplane_marked_action {U : Type*} [AddCommGroup U] [Module Bit U]
    (ρ : Representation Bit SL5TenDimensional.Group U) (e : U ≃ₗ[Bit] V)
    (he : ∀ g u, e (ρ g u) = exteriorAction 2 g (e u)) (g : parabolic 4) :
    fixedCommutator ρ (parabolicResidual 4) →ₗ[Bit]
      fixedCommutator ρ (parabolicResidual 4) :=
  (hyperplane_marked_equiv ρ e he).symm.toLinearMap.comp
    ((v6Action g).comp (hyperplane_marked_equiv ρ e he).toLinearMap)

/-- The marked operator is exactly the original action, not an unrelated
six-dimensional representation. -/
theorem hyperplane_marked_action_val {U : Type*} [AddCommGroup U] [Module Bit U]
    (ρ : Representation Bit SL5TenDimensional.Group U) (e : U ≃ₗ[Bit] V)
    (he : ∀ g u, e (ρ g u) = exteriorAction 2 g (e u))
    (g : parabolic 4) (u : fixedCommutator ρ (parabolicResidual 4)) :
    (hyperplane_marked_action ρ e he g u).val = ρ g.val u.val := by
  apply e.injective
  rw [he]
  exact congrArg Subtype.val ((hyperplane_marked_equiv ρ e he).apply_symm_apply
    (v6Action g (hyperplane_marked_equiv ρ e he u)))

/-- Equivariance with the defining orthogonal action, for the genuine source
operator and the literal upper-block quotient map. -/
theorem hyperplane_marked_orthogonal_action {U : Type*} [AddCommGroup U] [Module Bit U]
    (ρ : Representation Bit SL5TenDimensional.Group U) (e : U ≃ₗ[Bit] V)
    (he : ∀ g u, e (ρ g u) = exteriorAction 2 g (e u))
    (g : parabolic 4) (u : fixedCommutator ρ (parabolicResidual 4)) :
    v6QuadraticIsometry (hyperplane_marked_equiv ρ e he
      (hyperplane_marked_action ρ e he g u)) =
      (sl4TwoOmegaEquiv (parabolicFourBlock g)).val.val
        (v6QuadraticIsometry (hyperplane_marked_equiv ρ e he u)) := by
  change v6QuadraticIsometry ((hyperplane_marked_equiv ρ e he)
    ((hyperplane_marked_equiv ρ e he).symm _)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact v6QuadraticIsometry_action g _

/-- The fixed-space commutator in a marked hyperplane exterior model has
precisely dimension six. -/
theorem hyperplane_marked_finrank {U : Type*} [AddCommGroup U] [Module Bit U]
    (ρ : Representation Bit SL5TenDimensional.Group U) (e : U ≃ₗ[Bit] V)
    (he : ∀ g u, e (ρ g u) = exteriorAction 2 g (e u)) :
    Module.finrank Bit (fixedCommutator ρ (parabolicResidual 4)) = 6 := by
  rw [(hyperplane_marked_equiv ρ e he).finrank_eq]
  exact standard_dimensions.2.2.2.1

/-- Every nonzero invariant submodule of the marked source W is all of W.
This discharges the orthogonal submodule step in the C.4.8 exterior branch. -/
theorem hyperplane_marked_simple {U : Type*} [AddCommGroup U] [Module Bit U]
    (ρ : Representation Bit SL5TenDimensional.Group U) (e : U ≃ₗ[Bit] V)
    (he : ∀ g u, e (ρ g u) = exteriorAction 2 g (e u))
    (P : Submodule Bit (fixedCommutator ρ (parabolicResidual 4)))
    (hP : ∀ g : parabolic 4, ∀ u ∈ P, hyperplane_marked_action ρ e he g u ∈ P)
    (hne : P ≠ ⊥) : P = ⊤ := by
  let E := hyperplane_marked_equiv ρ e he
  have hm : P.map E.toLinearMap = ⊤ := by
    apply sixSpace_simple
    · intro g x hx
      obtain ⟨u, hu, rfl⟩ := hx
      exact ⟨hyperplane_marked_action ρ e he g u, hP g u hu, E.apply_symm_apply _⟩
    · intro hz
      apply hne
      apply (Submodule.eq_bot_iff P).mpr
      intro u hu
      have hx : E u ∈ P.map E.toLinearMap := ⟨u,hu,rfl⟩
      rw [hz, Submodule.mem_bot] at hx
      exact E.map_eq_zero_iff.mp hx
  apply top_unique
  intro u _
  have hu : E u ∈ P.map E.toLinearMap := by rw [hm]; trivial
  obtain ⟨v, hv, heq⟩ := hu
  exact (E.injective heq) ▸ hv

end
end Representation.BinaryParabolicExteriorSquare
