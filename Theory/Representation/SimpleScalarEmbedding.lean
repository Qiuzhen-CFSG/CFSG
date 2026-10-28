module

public import Theory.Representation.EndFieldRep
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# A simple module inside a coefficient-field action

Jacobson density separates basis vectors over the actual finite Schur field.
Their images in any extension-field action are therefore linearly independent
over the larger field: apply a density coordinate projection to any proposed
linear dependence. This bounds the absolute degree of the original simple
module without requiring a constituent classification after scalar extension.
The degree-four A₆ recognition applies the bound to its binary tensor model.
-/
open scoped MonoidAlgebra
open Representation Module
@[expose] public noncomputable section
namespace Representation.SimpleScalarEmbedding
variable {k F G U V : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
 [Group G] [AddCommGroup U] [Module k U] [FiniteDimensional k U]
 [AddCommGroup V] [Module F V] [Module k V] [IsScalarTower k F V]
 [FiniteDimensional F V]
/-- The Schur-field degree of an embedded simple module is bounded by the
coefficient-field dimension of the target. -/
theorem schur_finrank_le (σ : Representation k G U) [σ.IsIrreducible]
 (ρ : Representation F G V) (i : U →ₗ[k] V) (hi : Function.Injective i)
 (hc : ∀ g u, i (σ g u) = ρ g (i u)) :
 Module.finrank (Module.End k[G] σ.asModule) σ.asModule ≤ Module.finrank F V := by
 classical
 let E := Module.End k[G] σ.asModule
 let : IsSimpleModule k[G] σ.asModule := (irreducible_iff_isSimpleModule_asModule σ).mp inferInstance
 let : Finite σ.asModule := Module.finite_of_finite k
 let : FiniteDimensional E σ.asModule := Module.Finite.of_finite
 let b := Module.finBasis E σ.asModule
 let j : σ.asModule →ₗ[k] V := i.comp σ.asModuleEquiv.toLinearMap
 have hj : Function.Injective j := hi.comp σ.asModuleEquiv.injective
 have hact (a : k[G]) (u : σ.asModule) :
   j (a • u) = ρ.asModuleEquiv (MonoidAlgebra.mapRingHom G (algebraMap k F) a •
      ρ.asModuleEquiv.symm (j u)) := by
   induction a using MonoidAlgebra.induction_linear with
   | zero => simp
   | add a a' ha ha' => simp [add_smul, ha, ha']
   | single g c =>
     rw [MonoidAlgebra.mapRingHom_single]
     change i (σ.asModuleEquiv (MonoidAlgebra.single g c • u)) = _
     rw [σ.asModuleEquiv_map_smul, ρ.asModuleEquiv_map_smul,
       asAlgebraHom_single, asAlgebraHom_single, LinearMap.smul_apply, LinearMap.smul_apply,
       ρ.asModuleEquiv.apply_symm_apply]
     change i (c • σ g (σ.asModuleEquiv u)) =
       (algebraMap k F c) • ρ g (j u)
     rw [map_smul, hc, algebraMap_smul]
     rfl
 have hli : LinearIndependent F (fun s => j (b s)) := by
   rw [Fintype.linearIndependent_iff]
   intro c hz s
   let T : Module.End E σ.asModule := (b.coord s).smulRight (b s)
   obtain ⟨a, ha⟩ := jacobson_density T (Finset.univ.image b)
   have hab (t) : a • b t = if s = t then b s else 0 := by
     rw [← ha (b t) (Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩)]
     by_cases ht : s = t
     · subst t; simp [T]
     · simp [T, ht]
   let A : Module.End F V := ρ.asAlgebraHom (MonoidAlgebra.mapRingHom G (algebraMap k F) a)
   have hA (u) : A (j u) = j (a • u) := (hact a u).symm
   have hh := congrArg A hz
   simp only [map_sum,map_smul,map_zero,hA,hab] at hh
   simp [apply_ite] at hh
   exact hh.resolve_right (fun h =>
     (b.ne_zero s) (hj (by simpa using h)))
 have hd := hli.fintype_card_le_finrank
 simpa using hd

end Representation.SimpleScalarEmbedding
