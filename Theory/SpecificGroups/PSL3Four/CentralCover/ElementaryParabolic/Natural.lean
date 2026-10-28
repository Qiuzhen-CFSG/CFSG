module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ElementaryParabolic.Residual
public import Theory.SpecificGroups.PSL3Four.CentralCover.ElementaryParabolic.AffineModule

/-!
# Natural modules in the lifted PSL₃(4) parabolics

The affine-cover calculation is applied to the literal solvable residual of
each point or line parabolic preimage. All coordinate maps use the original
covering homomorphism. In particular the module denominator is its full-group
centralizer, not a separately supplied kernel or a model certificate.

Source: Aschbacher--Smith 2.5.7, printed pp.554--555, using I.2.2(3b).
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3Four.ElementaryParabolic
variable {E : Type*} [Group E] [Finite E]

/-- The residual affine map retains a central kernel. -/
theorem residualAffine_ker_le_center
    (f : E →* PSL) (hf : Function.Surjective f) (hc : f.ker ≤ center E) (b : Bool) :
    (residualAffine f hf b).ker ≤ center (liftedResidual f b) := by
  intro x hx
  rw [residualAffine_ker] at hx
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (Subtype.ext (mem_center_iff.mp (hc hx) y.val.val))

/-- The original residual two-core, in natural coordinates. -/
def residualVectorMap
    (f : E →* PSL) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) (b : Bool) :
    pCore 2 (liftedResidual f b) →* Multiplicative (Fin 2 → F) :=
  coreVectorMap F (residualAffine f hf b) (residualAffine_surjective f hf b)
    (residualAffine_ker_isTwoGroup f hf hk b)

theorem residualVectorMap_surjective
    (f : E →* PSL) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) (b : Bool) :
    Function.Surjective (residualVectorMap f hf hk b) :=
  coreVectorMap_surjective F _ _ _

theorem residualVectorMap_ker
    (f : E →* PSL) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hc : f.ker ≤ center E) (b : Bool) :
    (residualVectorMap f hf hk b).ker =
      (center (liftedResidual f b)).subgroupOf (pCore 2 (liftedResidual f b)) :=
  coreVectorMap_ker F _ _ _ (residualAffine_ker_le_center f hf hc b)

/-- V/C_V(L∞) is the natural field-four plane, through the original quotient. -/
def residualNaturalEquiv
    (f : E →* PSL) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hc : f.ker ≤ center E) (b : Bool) :
    (pCore 2 (liftedResidual f b) ⧸
      (center (liftedResidual f b)).subgroupOf (pCore 2 (liftedResidual f b))) ≃*
        Multiplicative (Fin 2 → F) :=
  coreCentralizerQuotientEquiv F (residualAffine f hf b)
    (residualAffine_surjective f hf b) (residualAffine_ker_isTwoGroup f hf hk b)
    (residualAffine_ker_le_center f hf hc b)

@[simp] theorem residualNaturalEquiv_mk
    (f : E →* PSL) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hc : f.ker ≤ center E) (b : Bool)
    (v : pCore 2 (liftedResidual f b)) :
    residualNaturalEquiv f hf hk hc b (QuotientGroup.mk' _ v) =
      residualVectorMap f hf hk b v := rfl

/-- The literal source conjugation is the natural action of the marked quotient. -/
theorem residualVectorMap_conjugate
    (f : E →* PSL) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) (b : Bool)
    (g : liftedResidual f b) (v : pCore 2 (liftedResidual f b)) :
    residualVectorMap f hf hk b (MulAut.conjNormal g v) =
      Matrix.SL2.naturalAction F
        (residualCoreQuotientEquiv f hf hk b (QuotientGroup.mk' _ g))
        (residualVectorMap f hf hk b v) :=
  coreVectorMap_conjugate F _ _ _ g v

theorem residualNatural_faithful
    (f : E →* PSL) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) (b : Bool) :
    Function.Injective ((Matrix.SL2.naturalAction F).comp
      (residualCoreQuotientEquiv f hf hk b).toMonoidHom) :=
  (Matrix.SL2.naturalAction_injective F).comp (residualCoreQuotientEquiv f hf hk b).injective

/-- A source center with trivial Frattini subgroup supplies the elementary-core
and marked natural-module inputs on both actual parabolic residuals. -/
theorem source_natural_module
    (e : (E ⧸ center E) ≃* PSL)
    (hz : IsPGroup 2 (center E)) (hphi : frattini (center E) = ⊥) (b : Bool) :
    let f := centerProjection e
    let L := liftedResidual f b
    IsElementaryAbelian 2 (pCore 2 L) ∧ frattini (pCore 2 L) = ⊥ ∧
    ∃ (q : (L ⧸ pCore 2 L) ≃* SL(2,F))
      (v : pCore 2 L →* Multiplicative (Fin 2 → F)),
      Function.Surjective v ∧ v.ker = (center L).subgroupOf (pCore 2 L) ∧
      (∀ g : L, ∀ a : pCore 2 L,
        v (MulAut.conjNormal g a) = Matrix.SL2.naturalAction F (q (QuotientGroup.mk' _ g)) (v a)) ∧
      Function.Injective ((Matrix.SL2.naturalAction F).comp q.toMonoidHom) := by
  dsimp only
  let f := centerProjection e
  have hf := centerProjection_surjective e
  have hc : f.ker ≤ center E := by rw [centerProjection_ker]
  have hk : IsPGroup 2 f.ker := by rwa [centerProjection_ker]
  let : Fact (IsPGroup 2 (center E)) := ⟨hz⟩
  let : IsElementaryAbelian 2 (center E) :=
    (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hphi
  have hs (z : E) (hz : z ∈ f.ker) : z ^ 2 = 1 := by
    rw [centerProjection_ker] at hz
    exact elemPow_eq_one_of_isElementaryAbelian z hz
  refine ⟨residualCore_elementary f hf hc hs b, residualCore_frattini f hf hc hs b,
    residualCoreQuotientEquiv f hf hk b, residualVectorMap f hf hk b,
    residualVectorMap_surjective f hf hk b, residualVectorMap_ker f hf hk hc b,
    residualVectorMap_conjugate f hf hk b, residualNatural_faithful f hf hk b⟩

end Matrix.PSL3Four.ElementaryParabolic
end
