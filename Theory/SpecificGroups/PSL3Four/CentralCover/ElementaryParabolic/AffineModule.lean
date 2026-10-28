module

public import Theory.SpecificGroups.SL2.Affine.Structure
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# Natural coordinates on the core of a central affine cover

A surjection onto the special affine group with central two-group kernel
identifies its two-core modulo its full-group centralizer with the natural
plane. The vector map retains conjugation by the original actor, and the
actor quotient acts faithfully. This is the local module used in I.2.2(3b)
and Chapter 2, 2.5.7 of Aschbacher--Smith.
-/

@[expose] public section
noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3Four.ElementaryParabolic
variable (F : Type*) [Field F]
theorem fixed_natural_eq_one (v : Multiplicative (Fin 2 → F))
    (hv : ∀ g : SL(2,F), Matrix.SL2.naturalAction F g v = v) : v = 1 := by
  let u : SL(2,F) := ⟨!![1,1;0,1], by simp [Matrix.det_fin_two]⟩
  let l : SL(2,F) := ⟨!![1,0;1,1], by simp [Matrix.det_fin_two]⟩
  have hu := congrArg (fun w : Multiplicative (Fin 2 → F) => Multiplicative.toAdd w 0) (hv u)
  have hl := congrArg (fun w : Multiplicative (Fin 2 → F) => Multiplicative.toAdd w 1) (hv l)
  change (u.val *ᵥ Multiplicative.toAdd v) 0 = Multiplicative.toAdd v 0 at hu
  change (l.val *ᵥ Multiplicative.toAdd v) 1 = Multiplicative.toAdd v 1 at hl
  simp [u, l, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hu hl
  apply Multiplicative.toAdd.injective
  ext i
  fin_cases i
  · simpa using hl
  · simpa using hu


variable [Finite F] [CharP F 2]
variable {L : Type*} [Group L] [Finite L]

/-- Coordinates of an original two-core element in the affine translation plane. -/
def coreVectorMap (f : L →* Matrix.SL2.Affine F) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) : pCore 2 L →* Multiplicative (Fin 2 → F) :=
  (Matrix.SL2.translationsEquiv F).symm.toMonoidHom.comp
    ((f.comp (pCore 2 L).subtype).codRestrict (Matrix.SL2.translations F) (by
      intro x
      rw [← Matrix.SL2.affine_twoCore_eq]
      exact (f.comap_pCore_of_ker_isPGroup hf hk).ge x.property))

theorem coreVectorMap_inl (f : L →* Matrix.SL2.Affine F) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (v : pCore 2 L) :
    SemidirectProduct.inl (coreVectorMap F f hf hk v) = f v := by
  exact congrArg Subtype.val ((Matrix.SL2.translationsEquiv F).apply_symm_apply
    ⟨f v, by
      rw [← Matrix.SL2.affine_twoCore_eq]
      exact (f.comap_pCore_of_ker_isPGroup hf hk).ge v.property⟩)

theorem coreVectorMap_surjective
    (f : L →* Matrix.SL2.Affine F) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) : Function.Surjective (coreVectorMap F f hf hk) := by
  intro v
  obtain ⟨x, hx⟩ := hf (SemidirectProduct.inl v)
  have hxc : x ∈ pCore 2 L := by
    rw [← f.comap_pCore_of_ker_isPGroup hf hk, Subgroup.mem_comap,
      Matrix.SL2.affine_twoCore_eq]
    change (f x).right = 1
    rw [hx]
    rfl
  refine ⟨⟨x, hxc⟩, (SemidirectProduct.inl_injective (φ := Matrix.SL2.naturalAction F)) ?_⟩
  exact (coreVectorMap_inl F f hf hk _).trans hx

/-- Exact natural action of each original group element. -/
theorem coreVectorMap_conjugate
    (f : L →* Matrix.SL2.Affine F) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (g : L) (v : pCore 2 L) :
    coreVectorMap F f hf hk (MulAut.conjNormal g v) =
      Matrix.SL2.naturalAction F (f g).right (coreVectorMap F f hf hk v) := by
  apply (SemidirectProduct.inl_injective (φ := Matrix.SL2.naturalAction F))
  rw [coreVectorMap_inl]
  change f (g * (v : L) * g⁻¹) = _
  rw [map_mul, map_mul, map_inv, ← coreVectorMap_inl F f hf hk v,
    Matrix.SL2.conjugate_inl]

/-- The vector kernel is exactly C_{O₂(L)}(L), as a subgroup of O₂(L). -/
theorem coreVectorMap_ker
    (f : L →* Matrix.SL2.Affine F) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hc : f.ker ≤ center L) :
    (coreVectorMap F f hf hk).ker = (center L).subgroupOf (pCore 2 L) := by
  ext v
  change coreVectorMap F f hf hk v = 1 ↔ (v : L) ∈ center L
  constructor
  · intro hv
    apply hc
    change f v = 1
    rw [← coreVectorMap_inl F f hf hk v, hv, map_one]
  · intro hv
    apply fixed_natural_eq_one
    intro a
    obtain ⟨g, hg⟩ := hf (SemidirectProduct.inr a)
    have he : MulAut.conjNormal g v = v := by
      apply Subtype.ext
      change g * (v : L) * g⁻¹ = (v : L)
      rw [mem_center_iff.mp hv g, mul_inv_cancel_right]
    have hh := coreVectorMap_conjugate F f hf hk g v
    rw [he, hg] at hh
    exact hh.symm

/-- The natural plane is the actual two-core modulo its full-group centralizer. -/
def coreCentralizerQuotientEquiv
    (f : L →* Matrix.SL2.Affine F) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hc : f.ker ≤ center L) :
    (pCore 2 L ⧸ (center L).subgroupOf (pCore 2 L)) ≃*
      Multiplicative (Fin 2 → F) :=
  (QuotientGroup.quotientMulEquivOfEq (coreVectorMap_ker F f hf hk hc).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (coreVectorMap_surjective F f hf hk))

@[simp] theorem coreCentralizerQuotientEquiv_mk
    (f : L →* Matrix.SL2.Affine F) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hc : f.ker ≤ center L) (v : pCore 2 L) :
    coreCentralizerQuotientEquiv F f hf hk hc (QuotientGroup.mk' _ v) =
      coreVectorMap F f hf hk v := rfl

/-- The quotient actor and its natural action are faithful. -/
def actorQuotientEquiv
    (f : L →* Matrix.SL2.Affine F) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) : (L ⧸ pCore 2 L) ≃* SL(2,F) :=
  (f.pCoreQuotientEquiv hf hk).trans (Matrix.SL2.affineCoreQuotientEquiv F)

theorem actorQuotient_faithful
    (f : L →* Matrix.SL2.Affine F) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) : Function.Injective
      ((Matrix.SL2.naturalAction F).comp (actorQuotientEquiv F f hf hk).toMonoidHom) :=
  (Matrix.SL2.naturalAction_injective F).comp (actorQuotientEquiv F f hf hk).injective

end Matrix.PSL3Four.ElementaryParabolic
end
