module
public import Theory.Representation.FiniteSimpleDensity
public import Mathlib.RepresentationTheory.Character

/-!
# Linear independence of irreducible trace characters

For a finite family of pairwise inequivalent finite-dimensional irreducible
representations over an algebraically closed field, the trace characters are
linearly independent. This holds in arbitrary characteristic, even for a
monoid: neither ordinary-character orthogonality nor invertibility of a
group order is used. It supplies the independence input for the modular
simple-family bound by p-regular conjugacy classes.

Simultaneous density for the actual simple monoid-algebra modules realizes
a trace-one endomorphism in one selected component and zero in every other
component. A trace-one map is obtained by projecting onto one basis vector;
the trace identity for a composition reduces its trace to that of the
identity on the field. A relation between characters extends linearly to
the monoid algebra. Evaluating at each separating algebra element forces
the corresponding coefficient to vanish. All representation spaces and
their original instances are preserved by the existing `asModule` equivalences.
-/

open scoped MonoidAlgebra BigOperators

namespace Representation

private theorem exists_trace_one
    (F V : Type*) [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Nontrivial V] :
    ∃ t : Module.End F V, LinearMap.trace F V t = 1 := by
  classical
  let b := Module.finBasis F V
  let k : Fin (Module.finrank F V) := ⟨0, Module.finrank_pos⟩
  let u := LinearMap.toSpanSingleton F V (b k)
  have hcomp : (b.coord k).comp u = LinearMap.id := by
    apply LinearMap.ext
    intro c
    simp [u]
  refine ⟨u.comp (b.coord k), ?_⟩
  rw [LinearMap.trace_comp_comm', hcomp, LinearMap.trace_id]
  simp

variable {F G ι : Type*} [Field F] [IsAlgClosed F] [Monoid G] [Fintype ι]
  (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)]
  [∀ i, FiniteDimensional F (V i)] (ρ : ∀ i, Representation F G (V i))
  [∀ i, IsIrreducible (ρ i)]

private theorem exists_simultaneous_asAlgebraHom_eq
    (hne : Pairwise fun i j => IsEmpty (Equiv (ρ i) (ρ j)))
    (f : ∀ i, Module.End F (V i)) :
    ∃ a : F[G], ∀ i, (ρ i).asAlgebraHom a = f i := by
  classical
  have hne' : Pairwise fun i j => IsEmpty ((ρ i).asModule ≃ₗ[F[G]] (ρ j).asModule) := by
    intro i j hij
    refine ⟨fun e => ?_⟩
    let e' := (IntertwiningMap.equivLinearMapAsModule (ρ i) (ρ j)).symm e.toLinearMap
    have he' : Function.Bijective e' := e.bijective
    exact (hne hij).false (e'.ofBijective he')
  obtain ⟨a, ha⟩ := Module.exists_simultaneous_smul_eq (F := F)
    (fun i => (ρ i).asModule) hne' (fun i => (ρ i).asModuleEquiv.symm.conj (f i))
  refine ⟨a, fun i => ?_⟩
  ext v
  have h := congrArg (ρ i).asModuleEquiv (ha i ((ρ i).asModuleEquiv.symm v))
  simpa [asModuleEquiv_map_smul, LinearEquiv.conj_apply] using h

public theorem linearIndependent_characters_of_pairwise_inequivalent
    (hne : Pairwise fun i j => IsEmpty (Equiv (ρ i) (ρ j))) :
    LinearIndependent F (fun i => (ρ i).character) := by
  classical
  have (i : ι) : Nontrivial (V i) := by
    have : Nontrivial (ρ i).asModule := IsSimpleModule.nontrivial F[G] (ρ i).asModule
    exact Function.Injective.nontrivial (ρ i).asModuleEquiv.injective
  choose t ht using fun i => exists_trace_one F (V i)
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let C : F[G] →ₗ[F] F := ∑ j, c j •
    ((LinearMap.trace F (V j)).comp (ρ j).asAlgebraHom.toLinearMap)
  have hCsingle (g : G) : C (MonoidAlgebra.single g 1) = 0 := by
    simpa [C, character] using congrFun hc g
  have hC : C = 0 := by
    apply MonoidAlgebra.lhom_ext'
    intro g
    apply LinearMap.ext
    intro r
    change C (MonoidAlgebra.single g r) = 0
    simpa using (C.map_smul r (MonoidAlgebra.single g 1)).trans
      (by simp only [hCsingle g, smul_zero])
  obtain ⟨a, ha⟩ := exists_simultaneous_asAlgebraHom_eq V ρ hne
    (fun j => if j = i then t j else 0)
  have hCa := congrArg (fun f : F[G] →ₗ[F] F => f a) hC
  simp only [C, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, smul_eq_mul, LinearMap.zero_apply] at hCa
  simpa only [ha, apply_ite, ht, map_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] using hCa

end Representation
