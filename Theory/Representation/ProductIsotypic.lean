module
public import Theory.Representation.IsotypicStable
public import Theory.Representation.FixedIsotypicCentralizer
public import Theory.Representation.SchurCopies
public import Theory.Representation.QuadraticFourGroup.TensorClassification.ExternalTensor
public import Mathlib.LinearAlgebra.TensorProduct.Pi
/-!
# Isotypic restrictions of irreducible product representations

The right factor preserves the first factor's canonical isotypic component.
A nonzero simple constituent therefore fills the whole irreducible product
module. Its finite copy coordinates are actual intertwiners. When that
constituent is absolutely irreducible, Schur's lemma produces a representation
on the multiplicity coordinates and a literal external tensor equivalence.

The source consumer is the deleted alternative in Aschbacher–Smith D.3.7,
printed pp.197–199. No semisimplicity or tensor-equivalence hypothesis remains.
-/
public section
open scoped MonoidAlgebra
open Module Representation
namespace Representation.ProductIsotypic
variable {k G H V W : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W]
  (ρ : Representation k (G × H) V) [ρ.IsIrreducible]
  (σ : Representation k G W) [σ.IsIrreducible]

abbrev left : Representation k G V := ρ.comp (MonoidHom.inl G H)

omit [FiniteDimensional k V] in
/-- A nonzero simple first-factor type fills an irreducible product module. -/
theorem isotypic_eq_top (f : σ.IntertwiningMap (left ρ)) (hf : f ≠ 0) :
    (Subrepresentation.ofSubmodule' (isotypicComponent k[G]
      (left ρ).asModule σ.asModule)).toSubmodule = ⊤ := by
  let S := Subrepresentation.ofSubmodule' (isotypicComponent k[G]
    (left ρ).asModule σ.asModule)
  have hstable (h : H) (v : V) (hv : v ∈ S.toSubmodule) :
      ρ (1,h) v ∈ S.toSubmodule := by
    apply SchurCopies.isotypic_stable_of_commute (left ρ) σ (ρ (1,h)) ?_ v hv
    intro g
    change ρ (1,h) * ρ (g,1) = ρ (g,1) * ρ (1,h)
    rw [←map_mul,←map_mul]
    simp
  let T : Subrepresentation ρ := {
    toSubmodule := S.toSubmodule
    apply_mem_toSubmodule g v hv := by
      have he : g = (g.1,1) * (1,g.2) := by simp
      rw [he,map_mul,Module.End.mul_apply]
      exact S.apply_mem_toSubmodule g.1 (hstable g.2 v hv) }
  have hT0 : T ≠ ⊥ := by
    intro ht
    apply hf
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    have hw : f w ∈ S.toSubmodule :=
      typeSpan_le_isotypicComponent (left ρ) σ ((show f.range ≤ typeSpan (left ρ) σ from le_iSup _ f) ⟨w,rfl⟩)
    have hh := congrArg Subrepresentation.toSubmodule ht
    change S.toSubmodule = ⊥ at hh
    have hz : f w ∈ (⊥ : Submodule k V) := hh ▸ hw
    exact hz
  exact congrArg Subrepresentation.toSubmodule
    ((IsSimpleOrder.eq_bot_or_eq_top T).resolve_left hT0)

/-- A nonzero simple constituent gives actual finite copy coordinates on the
entire first-factor restriction, without a semisimplicity premise. -/
theorem exists_copy_coordinates (f : σ.IntertwiningMap (left ρ)) (hf : f ≠ 0) :
    ∃ n : ℕ, ∃ e : V ≃ₗ[k] (Fin n → W),
      ∀ g v, e (ρ (g,1) v) = fun i => σ g (e v i) := by
  let S := Subrepresentation.ofSubmodule' (isotypicComponent k[G]
    (left ρ).asModule σ.asModule)
  have hS : S.toSubmodule = ⊤ := isotypic_eq_top ρ σ f hf
  let a : V ≃ₗ[k] S.toSubmodule := LinearEquiv.ofBijective
    (LinearMap.codRestrict S.toSubmodule (LinearMap.id : V →ₗ[k] V)
      (fun v => hS ▸ Submodule.mem_top)) ⟨fun _ _ h => congrArg Subtype.val h,
      fun v => ⟨v.val,Subtype.ext rfl⟩⟩
  obtain ⟨n,e,he⟩ := SchurCopies.isotypic_finite_rep_coordinates (left ρ) σ
  refine ⟨n,a.trans e,fun g v => ?_⟩
  exact he g (a v)

variable [FiniteDimensional k W] [σ.IsAbsolutelyIrreducible]
open scoped _root_.TensorProduct
open QuadraticFourGroup.TensorClassification

/-- An absolutely irreducible constituent gives a literal binary tensor
factorization, with an actual representation on its multiplicity space. -/
theorem exists_externalTensor (f : σ.IntertwiningMap (left ρ)) (hf : f ≠ 0) :
    ∃ n : ℕ, ∃ μ : Representation k H (Fin n → k),
      Nonempty (ρ.Equiv (externalTensor σ μ)) := by
  obtain ⟨n,e,he⟩ := exists_copy_coordinates ρ σ f hf
  let τ : Representation k H (Fin n → W) :=
    (e.conjAlgEquiv k).toAlgHom.toMonoidHom.comp (ρ.comp (MonoidHom.inr G H))
  have hsymm (g : G) (x : Fin n → W) :
      ρ (g,1) (e.symm x) = e.symm (fun i => σ g (x i)) := by
    apply e.injective
    rw [he,e.apply_symm_apply,e.apply_symm_apply]
  have hcomm (h : H) (g : G) (x : Fin n → W) :
      τ h (fun i => σ g (x i)) = fun i => σ g (τ h x i) := by
    change e (ρ (1,h) (e.symm (fun i => σ g (x i)))) = _
    rw [←hsymm]
    have hc : ρ (1,h) (ρ (g,1) (e.symm x)) = ρ (g,1) (ρ (1,h) (e.symm x)) := by
      simp only [←Module.End.mul_apply,←map_mul,Prod.mk_mul_mk,one_mul,mul_one]
    rw [hc,he]
    rfl
  obtain ⟨μ,hμ⟩ := SchurCopies.exists_multiplicity σ τ hcomm
  let b := TensorProduct.piScalarRight k k W (Fin n)
  let a := b.trans e.symm
  have hb (u : W) (c : Fin n → k) : b (u ⊗ₜ[k] c) = fun i => c i • u := rfl
  have hact : (externalTensor σ μ).Equiv ρ := Representation.Equiv.mk a (by
    intro g
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [LinearMap.comp_apply,map_add] at hx hy ⊢; rw [hx,hy]
    | tmul u c =>
      apply e.injective
      change e (e.symm (b (σ g.1 u ⊗ₜ[k] μ g.2 c))) =
        e (ρ g (e.symm (b (u ⊗ₜ[k] c))))
      rw [e.apply_symm_apply,hb,hb]
      have hg : g = (g.1,1) * (1,g.2) := by simp
      conv_rhs => rw [hg,map_mul,Module.End.mul_apply]
      rw [he]
      have hh : e (ρ (1,g.2) (e.symm (fun i => c i • u))) =
          fun i => μ g.2 c i • u := hμ g.2 c u
      rw [hh]
      funext i
      exact (map_smul (σ g.1) (μ g.2 c i) u).symm)
  exact ⟨n,μ,⟨hact.symm⟩⟩
end Representation.ProductIsotypic
