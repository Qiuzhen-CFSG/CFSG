module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.FieldComplements
public import Theory.Representation.SymplecticFourOrthogonalCover.Universal
public import Mathlib.LinearAlgebra.BilinearForm.Basic
/-!
# Complements in the actual orthogonal covering space

Every binary central cover of the derived natural Sp₄ action is a quotient
of the five-dimensional orthogonal model over the original natural
projection. Pulling back a binary hyperplane complementary to its central
kernel produces a four-dimensional field complement to the radical. Its
image is exactly the original hyperplane, its restriction is injective,
and the two stabilizers agree under that same equivariant quotient.

The polar form restricted to this complement is nondegenerate. These facts
supply the precise quotient and subspace conventions for the two orthogonal
orbits in source 11.2.2. The orbit calculation, cubic actor and Sylow-fixed
intersection remain with qt-d-1222-natural-weak-parameters; this is not the
completed source theorem. Final source assembly belongs to
qt-d-1222-natural-weak-closure-source.

Source: Aschbacher--Smith, I.2.3 and 11.2.2, printed pp.413 and 767.
-/

public noncomputable section
open Representation Submodule
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
open Representation.SymplecticFourOrthogonalCover Representation.OneCohomology
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalComplements
variable {F W : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) (L (K := F)) W}

omit [FiniteDimensional (ZMod 2) W] in
theorem cover_map_radical
    (p : ρ.IntertwiningMap (binaryNatural (K := F)))
    (f : (binaryAction (K := F)).IntertwiningMap ρ) (hf : Function.Surjective f)
    (hp : ∀ x, p (f x) = binaryProjection x) :
    f.toLinearMap.ker ≤ (radical (K := F)).restrictScalars (ZMod 2) ∧
      ((radical (K := F)).restrictScalars (ZMod 2)).map f.toLinearMap = p.toLinearMap.ker := by
  constructor
  · intro x hx
    change binaryProjection x = 0
    rw [←hp,show f x = 0 from hx,map_zero]
  · ext w
    constructor
    · rintro ⟨x,hx,rfl⟩
      change p (f x) = 0
      rw [hp]
      exact hx
    · intro hw
      obtain ⟨x,rfl⟩ := hf w
      refine ⟨x,?_,rfl⟩
      change binaryProjection x = 0
      rw [←hp]
      exact hw

theorem exists_field_complement
    (p : ρ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U : Submodule (ZMod 2) W)
    (hU : Module.finrank (ZMod 2) U + 1 = Module.finrank (ZMod 2) W)
    (hC : IsCompl U p.toLinearMap.ker) :
    ∃ f : (binaryAction (K := F)).IntertwiningMap ρ,
      Function.Surjective f ∧ (∀ x, p (f x) = binaryProjection x) ∧
      ∃ Q : Submodule F (Space (K := F)), Module.finrank F Q = 4 ∧
        IsCompl Q radical ∧ (Q.restrictScalars (ZMod 2)).map f.toLinearMap = U ∧
        Disjoint (Q.restrictScalars (ZMod 2)) f.toLinearMap.ker ∧
        ∀ P : Submodule F (Space (K := F)),
          (P.restrictScalars (ZMod 2)).map f.toLinearMap ≤ U → P ≤ Q := by
  obtain ⟨f,hf,hpf⟩ := exists_cover_quotient p hp
  obtain ⟨hk,hr⟩ := cover_map_radical p f hf hpf
  obtain ⟨Q,hQ,hQR,hQU,hQk,hgreat⟩ := field_complement_image f.toLinearMap hf U hU
    radical radical_finrank (hr.symm ▸ hC) hk
  refine ⟨f,hf,hpf,Q,?_,hQR,hQU,hQk,hgreat⟩
  rw [space_finrank] at hQ
  omega

omit [FiniteDimensional (ZMod 2) W] in
theorem stabilizer_iff
    (f : (binaryAction (K := F)).IntertwiningMap ρ)
    (Q : Submodule F (Space (K := F))) (U : Submodule (ZMod 2) W)
    (him : (Q.restrictScalars (ZMod 2)).map f.toLinearMap = U)
    (hgreat : ∀ P : Submodule F (Space (K := F)),
      (P.restrictScalars (ZMod 2)).map f.toLinearMap ≤ U → P ≤ Q)
    (g : L (K := F)) : Q.map (action g) = Q ↔ U.map (ρ g) = U := by
  let a : Space (K := F) ≃ₗ[F] Space (K := F) :=
    { action g with
      invFun := action g⁻¹
      left_inv := action.inv_self_apply g
      right_inv := action.self_inv_apply g }
  let b : W ≃ₗ[ZMod 2] W :=
    { ρ g with
      invFun := ρ g⁻¹
      left_inv := ρ.inv_self_apply g
      right_inv := ρ.self_inv_apply g }
  exact field_complement_stabilizer f.toLinearMap Q U him hgreat a b
    (fun x => LinearMap.congr_fun (f.isIntertwining' g) x)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalComplements

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalComplements
open ClassicalOrthogonal Representation.SymplecticFourOrthogonalCover
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem complement_polar_nondegenerate
    (Q : Submodule F (Space (K := F))) (hQ : IsCompl Q radical) :
    (LinearMap.BilinForm.restrict (formB 2 F).polarBilin Q).Nondegenerate := by
  have hleft : (LinearMap.BilinForm.restrict (formB 2 F).polarBilin Q).SeparatingLeft := by
    intro x hx
    have hr : x.val ∈ radical (K := F) := by
      apply (polar_radical x.val).mp
      intro y
      have hy : y ∈ Q ⊔ radical := hQ.codisjoint.eq_top.symm ▸ Submodule.mem_top
      obtain ⟨q,hq,r,hr,rfl⟩ := Submodule.mem_sup.mp hy
      rw [map_add]
      have hqr : (formB 2 F).polarBilin x.val r = 0 := by
        rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
        exact (polar_radical r).mpr hr x.val
      change (formB 2 F).polarBilin x.val q + _ = 0
      rw [show (formB 2 F).polarBilin x.val q = 0 from hx ⟨q,hq⟩,hqr,add_zero]
    exact Subtype.ext (hQ.disjoint.eq_bot.le ⟨x.property,hr⟩)
  refine ⟨hleft,?_⟩
  intro x hx
  apply hleft x
  intro y
  change (formB 2 F).polarBilin x.val y.val = 0
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
  exact hx y
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalComplements
