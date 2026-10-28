module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.GroupTheory.Coset.Card

/-!
# Restricting integral projective representations

Projection onto the identity coefficient in a free group representation has
norm equal to the identity. A projective splitting transports this witness to
the given representation. Regrouping the norm by left cosets gives a subgroup
norm witness; averaging a linear section then proves subgroup projectivity.
All these arguments work over a commutative ring. For the converse norm
criterion, projectivity of the underlying coefficient module is explicit.

This supplies the restriction step in the cyclic-subgroup proof of Feit,
*The Representation Theory of Finite Groups*, IV.2.5. It extends the
field-valued norm proofs in `ProjectivePairing.Projectivity` without changing
that module or assuming an inverse of the group order.
-/

public section

noncomputable section
open scoped BigOperators MonoidAlgebra
namespace Representation.CyclicDefect.ProjectivePairing.Singular
variable {R G : Type*} [CommRing R] [Group G] [Fintype G]

private def coeffOne : MonoidAlgebra R G →ₗ[R] MonoidAlgebra R G :=
  (MonoidAlgebra.lsingle (1 : G)).comp
    ((Finsupp.lapply (1 : G)).comp (MonoidAlgebra.coeffLinearEquiv R).toLinearMap)

private def freeProjection (α : Type*) : Module.End R (α →₀ MonoidAlgebra R G) :=
  Finsupp.mapRange.linearMap (coeffOne (R := R) (G := G))

private theorem freeProjection_norm (α : Type*) (v : α →₀ MonoidAlgebra R G) :
    ∑ g : G, (Representation.free R G α) g⁻¹
      (freeProjection α ((Representation.free R G α) g v)) = v := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finset.sum_add_distrib, hx, hy]
  | single i x =>
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [Finsupp.single_add, map_add, Finset.sum_add_distrib, hx, hy]
    | single h r =>
      have ht (g : G) : (Representation.free R G α) g⁻¹
          (freeProjection α ((Representation.free R G α) g
            (Finsupp.single i (MonoidAlgebra.single h r)))) =
          if g = h⁻¹ then Finsupp.single i (MonoidAlgebra.single h r) else 0 := by
        simp only [Representation.free_single_single, freeProjection,
          Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, coeffOne,
          LinearMap.comp_apply, Finsupp.lapply_apply, MonoidAlgebra.coeffLinearEquiv]
        by_cases hg : g = h⁻¹
        · subst g
          simp
        · have hne : g * h ≠ 1 := fun hh => hg (eq_inv_of_mul_eq_one_left hh)
          simp [hne, hg]
      simp_rw [ht]
      simp

variable {V : Type*} [AddCommGroup V] [Module R V]

/-- A projective group-algebra module has a norm witness over any commutative ring. -/
theorem exists_norm (ρ : Representation R G V)
    [Module.Projective (MonoidAlgebra R G) ρ.asModule] :
    ∃ θ : Module.End R V, ∀ v, ∑ g : G, ρ g⁻¹ (θ (ρ g v)) = v := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Module.Projective (MonoidAlgebra R G) ρ.asModule).out
  let F := Representation.free R G ρ.asModule
  let e := Representation.finsuppLEquivFreeAsModule R G ρ.asModule
  let i0 : ρ.asModule →ₗ[MonoidAlgebra R G] F.asModule := e.toLinearMap.comp s
  let q0 : F.asModule →ₗ[MonoidAlgebra R G] ρ.asModule :=
    (Finsupp.linearCombination (MonoidAlgebra R G) id).comp e.symm.toLinearMap
  let i : ρ.IntertwiningMap F := (IntertwiningMap.equivLinearMapAsModule ρ F).symm i0
  let q : F.IntertwiningMap ρ := (IntertwiningMap.equivLinearMapAsModule F ρ).symm q0
  have hqi (v : V) : q (i v) = v := by
    change ρ.asModuleEquiv (q0 (i0 (ρ.asModuleEquiv.symm v))) = v
    simpa [q0, i0, LinearMap.comp_apply] using congrArg ρ.asModuleEquiv (hs (ρ.asModuleEquiv.symm v))
  refine ⟨q.toLinearMap.comp ((freeProjection ρ.asModule).comp i.toLinearMap), fun v => ?_⟩
  change (∑ g : G, ρ g⁻¹ (q (freeProjection ρ.asModule (i (ρ g v))))) = v
  simp_rw [← q.isIntertwining, i.isIntertwining]
  rw [← map_sum, freeProjection_norm, hqi]


/-- A norm witness gives group-algebra projectivity when the underlying module is projective. -/
theorem projective_of_norm {k G V : Type*} [CommRing k] [Group G] [Fintype G]
    [AddCommGroup V] [Module k V] [Module.Projective k V] (ρ : Representation k G V)
    (θ : Module.End k V)
    (hθ : ∀ v, ∑ g : G, ρ g⁻¹ (θ (ρ g v)) = v) :
    Module.Projective k[G] ρ.asModule := by
  let : Module.Projective k ρ.asModule := Module.Projective.of_equiv' ρ.asModuleEquiv.symm
  let f : (ρ.asModule →₀ k[G]) →ₗ[k[G]] ρ.asModule :=
    Finsupp.linearCombination k[G] id
  have hf : Function.Surjective f :=
    Finsupp.linearCombination_surjective _ Function.surjective_id
  obtain ⟨s, hs⟩ := (f.restrictScalars k).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hf)
  let θ' : Module.End k ρ.asModule := ρ.asModuleEquiv.symm.toLinearMap ∘ₗ θ ∘ₗ
    ρ.asModuleEquiv.toLinearMap
  refine ⟨⟨(s ∘ₗ θ').sumOfConjugatesEquivariant G, ?_⟩⟩
  intro v
  change f ((s ∘ₗ θ').sumOfConjugatesEquivariant G v) = v
  rw [LinearMap.sumOfConjugatesEquivariant_apply, map_sum]
  simp only [LinearMap.conjugate_apply, f.map_smul]
  have hs' (w : ρ.asModule) : f (s w) = w := LinearMap.congr_fun hs w
  simp only [LinearMap.comp_apply, hs']
  apply ρ.asModuleEquiv.injective
  rw [map_sum]
  simp only [θ', LinearMap.comp_apply, LinearEquiv.coe_coe, asModuleEquiv_map_smul,
    asAlgebraHom_single, one_smul, LinearEquiv.apply_symm_apply]
  exact hθ _


/-- Regroup a norm witness by left cosets to obtain a norm witness for a subgroup. -/
theorem exists_norm_subgroup (ρ : Representation R G V)
    [Module.Projective (MonoidAlgebra R G) ρ.asModule] (H : Subgroup G) [Fintype H] :
    ∃ θ : Module.End R V, ∀ v, ∑ h : H, ρ (h : G)⁻¹ (θ (ρ (h : G) v)) = v := by
  classical
  obtain ⟨θ, hθ⟩ := exists_norm ρ
  have hbij : Function.Bijective (fun x : (G ⧸ H) × H => x.1.out * (x.2 : G)) := by
    constructor
    · rintro ⟨q, h⟩ ⟨q', h'⟩ heq
      have hq : q = q' := by
        have hx := congrArg (QuotientGroup.mk (s := H)) heq
        simpa only [QuotientGroup.mk_mul_of_mem _ h.property,
          QuotientGroup.mk_mul_of_mem _ h'.property, Quotient.out_eq'] using hx
      subst q'
      exact Prod.ext rfl (Subtype.ext (mul_left_cancel heq))
    · intro g
      refine ⟨⟨QuotientGroup.mk g, ⟨(QuotientGroup.mk (s := H) g).out⁻¹ * g, ?_⟩⟩, ?_⟩
      · exact QuotientGroup.eq.mp (Quotient.out_eq' (QuotientGroup.mk (s := H) g))
      · exact mul_inv_cancel_left _ _
  refine ⟨∑ q : G ⧸ H, (ρ q.out⁻¹).comp (θ.comp (ρ q.out)), fun v => ?_⟩
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  rw [Finset.sum_comm]
  have hterm (q : G ⧸ H) (h : H) :
      ρ (h : G)⁻¹ (ρ q.out⁻¹ (θ (ρ q.out (ρ (h : G) v)))) =
      ρ (q.out * (h : G))⁻¹ (θ (ρ (q.out * (h : G)) v)) := by
    simp [mul_inv_rev, map_mul, Module.End.mul_apply]
  simp_rw [hterm]
  rw [← Fintype.sum_prod_type (fun x : (G ⧸ H) × H =>
    ρ (x.1.out * (x.2 : G))⁻¹ (θ (ρ (x.1.out * (x.2 : G)) v)))]
  rw [Fintype.sum_bijective _ hbij _
    (fun g => ρ g⁻¹ (θ (ρ g v))) (fun _ => rfl)]
  exact hθ v

/-- Restriction preserves projectivity for representations whose underlying module is projective. -/
theorem projective_subgroup (ρ : Representation R G V) [Module.Projective R V]
    [Module.Projective (MonoidAlgebra R G) ρ.asModule] (H : Subgroup G) :
    Module.Projective (MonoidAlgebra R H) (Representation.asModule (ρ.comp H.subtype)) := by
  let : Fintype H := Fintype.ofFinite H
  obtain ⟨θ, hθ⟩ := exists_norm_subgroup ρ H
  exact projective_of_norm (ρ.comp H.subtype) θ hθ

end Representation.CyclicDefect.ProjectivePairing.Singular
