module

public import Theory.Representation.FirstCohomology
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Projective representations have trivial first cohomology

For a finite group, the free group-algebra representation has an explicit
contracting homotopy for crossed homomorphisms.  A projective module is a
retract of such a free representation, so the contraction descends along the
retraction.  This proves the projective vanishing assertion in Aschbacher--
Smith, *The Classification of Quasithin Groups*, Remark I.1.5, printed p.408.
-/

@[expose] public section

open scoped BigOperators MonoidAlgebra
open Module

namespace Representation.OneCohomology

noncomputable section

attribute [local instance] Fintype.ofFinite

variable {k G α : Type*} [Field k] [Group G] [Fintype G]

private def coeffOne : MonoidAlgebra k G →ₗ[k] k :=
  (Finsupp.lapply (1 : G)).comp (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

private def witnessTerm (h : G) : (α →₀ k[G]) →ₗ[k] α →₀ k[G] :=
  (Finsupp.mapRange.linearMap (α := α)
      (MonoidAlgebra.lsingle h : k →ₗ[k] MonoidAlgebra k G)).comp
    (Finsupp.mapRange.linearMap (α := α) (coeffOne (k := k) (G := G)))

private def witness (f : cocycles (Representation.free k G α)) : α →₀ k[G] :=
  ∑ h : G, witnessTerm h (f.val h⁻¹)

omit [Fintype G] in
private lemma free_coeff (g : G) (x : α →₀ k[G]) (i : α) (h : G) :
    (((Representation.free k G α) g x) i).coeff h = (x i).coeff (g⁻¹ * h) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | single i' v =>
      by_cases hi : i' = i
      · subst hi
        induction v using MonoidAlgebra.induction_on with
        | of g' =>
          simp only [Representation.free_single_single, MonoidAlgebra.of_apply]
          rw [Finsupp.single_apply, Finsupp.single_apply]
          by_cases e₁ : g' = g⁻¹ * h
          · simp [e₁, mul_inv_cancel_left]
          · have e₂ : g * g' ≠ h := by
              intro hh
              apply e₁
              rw [← hh, inv_mul_cancel_left]
            simp [e₁, e₂]
        | add v w hv hw => simp
        | smul r v hv => simp
      · simp [hi]

private lemma free_cocycle_principal (f : cocycles (Representation.free k G α)) :
    ∃ w, principal (Representation.free k G α) w = f := by
  refine ⟨witness f, ?_⟩
  apply Subtype.ext
  funext g
  apply Finsupp.ext
  intro i
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro h
  simp [principal, witness, witnessTerm, coeffOne]
  simp_rw [free_coeff]
  classical
  simp [Finsupp.mapRange_apply, Finsupp.single_apply]
  have hf := f.property h⁻¹ g
  have he := congrArg (fun z : α →₀ k[G] => (z i).coeff 1) hf
  simp only [Finsupp.add_apply, MonoidAlgebra.coeff_add] at he
  rw [free_coeff] at he
  simpa using sub_eq_iff_eq_add.mpr he

private noncomputable def cocycleMap {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] {ρ : Representation k G V} {σ : Representation k G W}
    (q : ρ.IntertwiningMap σ) : cocycles ρ →ₗ[k] cocycles σ where
  toFun f := ⟨fun g => q (f.val g), by
    intro g t
    change q (f.val (g * t)) = _
    rw [f.property, map_add, q.isIntertwining]⟩
  map_add' f h := by ext g; simp
  map_smul' a f := by ext g; simp

omit [Fintype G] in
private lemma cocycleMap_principal {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] {ρ : Representation k G V} {σ : Representation k G W}
    (q : ρ.IntertwiningMap σ) (v : V) :
    cocycleMap q (principal ρ v) = principal σ (q v) := by
  apply Subtype.ext
  funext g
  change q (ρ g v - v) = σ g (q v) - q v
  rw [map_sub, q.isIntertwining]

variable {V : Type*}
omit [Fintype G] in
set_option linter.style.haveILetI false in
/-- Projectivity over the group algebra forces the explicit first cohomology to vanish. -/
theorem subsingleton_H1_of_projective [Finite G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V)
    [Module.Projective (MonoidAlgebra k G) ρ.asModule] :
    Subsingleton (H1 ρ) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨s, hs⟩ :=
    (inferInstance : Module.Projective (MonoidAlgebra k G) ρ.asModule).out
  let F := Representation.free k G ρ.asModule
  let e := Representation.finsuppLEquivFreeAsModule k G ρ.asModule
  let i0 : ρ.asModule →ₗ[MonoidAlgebra k G] F.asModule := e.toLinearMap.comp s
  let q0 : F.asModule →ₗ[MonoidAlgebra k G] ρ.asModule :=
    (Finsupp.linearCombination (MonoidAlgebra k G) id).comp e.symm.toLinearMap
  let i : ρ.IntertwiningMap F :=
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ F).symm i0
  let q : F.IntertwiningMap ρ :=
    (Representation.IntertwiningMap.equivLinearMapAsModule F ρ).symm q0
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply LinearMap.range_eq_top.mpr
  intro f
  let f' := cocycleMap i f
  obtain ⟨w, hw⟩ := free_cocycle_principal f'
  refine ⟨q w, ?_⟩
  have hmap := congrArg (cocycleMap q) hw
  rw [← cocycleMap_principal q w, hmap]
  apply Subtype.ext
  funext g
  change ρ.asModuleEquiv (q0 (i0 (ρ.asModuleEquiv.symm (f.val g)))) = f.val g
  have hx := hs (ρ.asModuleEquiv.symm (f.val g))
  simpa [q0, i0, LinearMap.comp_apply] using congrArg ρ.asModuleEquiv hx

end
end Representation.OneCohomology
