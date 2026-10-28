module

public import Theory.Representation.SpecialLinearNatural
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Coefficient transport of the natural special-linear module and its dual

A field equivalence acts entrywise on vectors and matrices. On a linear
functional it acts by conjugating the function with that coefficient map.
Both additive equivalences intertwine the corresponding literal matrix
actions. In particular, transporting a natural module and its dual uses one
and the same special-linear group isomorphism.

These elementary coefficient comparisons are used for all section models
in Aschbacher--Smith C.1.34; they do not classify any modules.
-/

@[expose] public section
namespace Representation.SpecialLinearFieldTransport
variable {F K : Type*} [Field F] [Field K]

/-- Entrywise coefficient transport on the natural vector space. -/
def natural (n : ℕ) (e : F ≃+* K) : (Fin n → F) ≃+ (Fin n → K) :=
  AddEquiv.piCongrRight (fun _ => e.toAddEquiv)

theorem natural_action (n : ℕ) (e : F ≃+* K)
    (g : Matrix.SpecialLinearGroup (Fin n) F) (v : Fin n → F) :
    natural n e (specialLinearNatural n g v) =
      specialLinearNatural n (Atlas.fieldEquivSL n e g) (natural n e v) := by
  ext i
  simp [natural, specialLinearNatural_apply, Matrix.mulVec, dotProduct,
    Atlas.fieldEquivSL, map_sum, map_mul]

/-- Coefficient conjugation turns an F-linear functional into a K-linear one. -/
def dualMap (n : ℕ) (e : F ≃+* K) (f : Module.Dual F (Fin n → F)) :
    Module.Dual K (Fin n → K) where
  toFun v := e (f (natural n e.symm v))
  map_add' x y := by simp [natural]
  map_smul' a v := by
    have hv : natural n e.symm (a • v) = e.symm a • natural n e.symm v := by
      ext i
      exact e.symm.map_mul _ _
    simp only [hv, map_smul, smul_eq_mul, map_mul, e.apply_symm_apply,
      RingHom.id_apply]

/-- The coefficient map on the actual linear dual, rather than an independently
chosen isomorphism with a vector space of the same dimension. -/
def dual (n : ℕ) (e : F ≃+* K) :
    Module.Dual F (Fin n → F) ≃+ Module.Dual K (Fin n → K) where
  toFun := dualMap n e
  invFun := dualMap n e.symm
  left_inv f := by
    apply LinearMap.ext
    intro v
    change e.symm (e (f ((natural n e).symm (natural n e v)))) = f v
    rw [AddEquiv.symm_apply_apply, e.symm_apply_apply]
  right_inv f := by
    apply LinearMap.ext
    intro v
    change e (e.symm (f ((natural n e) ((natural n e).symm v)))) = f v
    rw [AddEquiv.apply_symm_apply, e.apply_symm_apply]
  map_add' f g := by
    apply LinearMap.ext
    intro v
    exact e.map_add _ _

theorem dual_action (n : ℕ) (e : F ≃+* K)
    (g : Matrix.SpecialLinearGroup (Fin n) F) (v : Module.Dual F (Fin n → F)) :
    dual n e ((specialLinearNatural (k := F) n).dual g v) =
      (specialLinearNatural (k := K) n).dual (Atlas.fieldEquivSL n e g) (dual n e v) := by
  apply LinearMap.ext
  intro w
  change e (v (specialLinearNatural n g⁻¹ (natural n e.symm w))) =
    e (v (natural n e.symm (specialLinearNatural n (Atlas.fieldEquivSL n e g)⁻¹ w)))
  congr 2
  apply (natural n e).injective
  rw [natural_action]
  change specialLinearNatural n (Atlas.fieldEquivSL n e g⁻¹)
    ((natural n e) ((natural n e).symm w)) =
    (natural n e) ((natural n e).symm _)
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, map_inv]

end Representation.SpecialLinearFieldTransport
