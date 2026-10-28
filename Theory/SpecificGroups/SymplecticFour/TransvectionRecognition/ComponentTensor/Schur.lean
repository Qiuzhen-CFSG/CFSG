module
public import Theory.Representation.ProductIsotypic
public import Theory.Representation.PerfectDegreeThree
public import Theory.Representation.EndFieldDegree
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.Tactic.Linarith

/-!
# Finite Schur fields for commuting perfect factors

A perfect action of degree one is trivial. Over a finite field the commutant
of an irreducible action is a field, so any commuting perfect action is also
trivial. The scalar-extension degree formula then proves that a nontrivial
perfect irreducible action of degree two is absolutely irreducible. For two
nontrivial commuting perfect factors in degree four, the existing degree-three
bound gives the same conclusion over the original coefficient field.

These are the Schur and dimension inputs for the tensor-product branch of
Aschbacher--Smith G.4.9, printed pp.341--342. No tensor realization or minimal
coefficient-field hypothesis is assumed.
-/

public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace Representation.ComponentTensor
variable {F G H V : Type*} [Field F] [Group G] [Group H]
  [AddCommGroup V] [Module F V]

private theorem eq_one_of_commuting [Group.IsPerfect G] {M : Type*} [Monoid M]
    (f : G →* M) (hc : ∀g h,f g*f h=f h*f g) : f=1 := by
  let f' := f.toHomUnits
  let : Group.IsPerfect f'.range := Group.IsPerfect.range f'
  let : IsMulCommutative f'.range := ⟨⟨by
    rintro ⟨_,g,rfl⟩ ⟨_,h,rfl⟩
    exact Subtype.ext (Units.ext (hc g h))⟩⟩
  ext g
  exact congrArg (fun x : f'.range => (x.val:M))
    (Subsingleton.elim (⟨f' g,g,rfl⟩ : f'.range) 1)

/-- A perfect action in dimension at most one is trivial. -/
theorem eq_one_of_finrank_le_one [Group.IsPerfect G] [FiniteDimensional F V]
    (ρ : Representation F G V) (hdim : Module.finrank F V≤1) : ρ=1 := by
  rcases Nat.eq_zero_or_pos (Module.finrank F V) with hz | hp
  · let : Subsingleton V := Module.finrank_zero_iff.mp hz
    ext g v
    exact Subsingleton.elim _ _
  · have he : Module.finrank F V=1 := by omega
    apply eq_one_of_commuting ρ
    intro g h
    obtain ⟨a,ha,_⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one he (ρ g)
    obtain ⟨b,hb,_⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one he (ρ h)
    rw [ha,hb]
    simp [smul_smul,mul_comm]

set_option backward.isDefEq.respectTransparency false in
/-- A perfect group commuting with an irreducible finite-field action acts
trivially, since the Schur endomorphism ring is a finite field. -/
theorem commuting_eq_one_of_irreducible [Finite F] [FiniteDimensional F V]
    [Group.IsPerfect H] (ρ : Representation F G V) [ρ.IsIrreducible]
    (σ : Representation F H V) (hc : ∀g h,ρ g*σ h=σ h*ρ g) : σ=1 := by
  let t : H →* IntertwiningMap ρ ρ := {
    toFun h := ⟨σ h,fun g=>(hc g h).symm⟩
    map_one' := by ext v; exact DFunLike.congr_fun (map_one σ) v
    map_mul' a b := by ext v; exact DFunLike.congr_fun (map_mul σ a b) v }
  let e := IntertwiningMap.equivAlgEnd ρ
  have he : e.toMonoidHom.comp t=1 := eq_one_of_commuting _ (fun _ _=>mul_comm _ _)
  ext h v
  have ht : t h=1 := e.injective (by rw [map_one]; exact DFunLike.congr_fun he h)
  exact DFunLike.congr_fun (congrArg IntertwiningMap.toLinearMap ht) v

variable [Finite F] [FiniteDimensional F V]

private theorem absolute_of_end_degree_one (ρ : Representation F G V) [ρ.IsIrreducible]
    (hd : Module.finrank F (Module.End F[G] ρ.asModule)=1) :
    ρ.IsAbsolutelyIrreducible := by
  apply (isAbsolutelyIrreducible_iff_surjective ρ).mpr
  let e := IntertwiningMap.equivAlgEnd ρ
  intro f
  obtain ⟨c,hc⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hd).surjective (e f)
  refine ⟨c,e.injective ?_⟩
  rw [e.commutes]
  exact hc

/-- A nontrivial irreducible perfect action of degree two over a finite field
is absolutely irreducible over that same field. -/
theorem absolute_of_perfect_degree_two [Group.IsPerfect G]
    (ρ : Representation F G V) [ρ.IsIrreducible]
    (hnt : ρ≠1) (hdim : Module.finrank F V=2) : ρ.IsAbsolutelyIrreducible := by
  let E := Module.End F[G] ρ.asModule
  let : Finite ρ.asModule := Module.finite_of_finite F
  let : FiniteDimensional E ρ.asModule := Module.Finite.of_finite
  have hnE : ρ.endFieldRep≠1 := by
    intro h
    apply hnt
    ext g v
    exact congrArg ρ.asModuleEquiv
      (DFunLike.congr_fun (DFunLike.congr_fun h g) (ρ.asModuleEquiv.symm v))
  have hdE : 2≤Module.finrank E ρ.asModule := by
    by_contra! h
    exact hnE (eq_one_of_finrank_le_one (F:=E) ρ.endFieldRep (by change Module.finrank E ρ.asModule≤1; omega))
  have he : 0<Module.finrank F E := Module.finrank_pos
  have hh := finrank_eq_endField_mul ρ
  rw [hdim] at hh
  apply absolute_of_end_degree_one ρ
  change Module.finrank F E=1
  nlinarith

/-- An irreducible degree-four product action, nontrivial on each perfect
factor, has scalar commutant over the given finite field. -/
theorem absolute_of_perfect_product_degree_four [Group.IsPerfect G] [Group.IsPerfect H]
    (ρ : Representation F (G×H) V) [ρ.IsIrreducible]
    (hl : ρ.comp (MonoidHom.inl G H)≠1)
    (hr : ρ.comp (MonoidHom.inr G H)≠1)
    (hdim : Module.finrank F V=4) : ρ.IsAbsolutelyIrreducible := by
  let E := Module.End F[G×H] ρ.asModule
  let : Finite ρ.asModule := Module.finite_of_finite F
  let : FiniteDimensional E ρ.asModule := Module.Finite.of_finite
  let l := ρ.endFieldRep.comp (MonoidHom.inl G H)
  let r := ρ.endFieldRep.comp (MonoidHom.inr G H)
  have hln : l≠1 := by
    intro h
    apply hl
    ext g v
    exact congrArg ρ.asModuleEquiv
      (DFunLike.congr_fun (DFunLike.congr_fun h g) (ρ.asModuleEquiv.symm v))
  have hrn : r≠1 := by
    intro h
    apply hr
    ext g v
    exact congrArg ρ.asModuleEquiv
      (DFunLike.congr_fun (DFunLike.congr_fun h g) (ρ.asModuleEquiv.symm v))
  have hdE : 4≤Module.finrank E ρ.asModule := by
    by_contra! h
    apply hrn
    apply PerfectDegreeThree.commuting_eq_one_of_finrank_le_three l r hln (by change Module.finrank E ρ.asModule≤3; omega)
    intro g h
    change ρ.endFieldRep (g,1)*ρ.endFieldRep (1,h)=
      ρ.endFieldRep (1,h)*ρ.endFieldRep (g,1)
    rw [←map_mul,←map_mul]
    simp
  have he : 0<Module.finrank F E := Module.finrank_pos
  have hh := finrank_eq_endField_mul ρ
  rw [hdim] at hh
  apply absolute_of_end_degree_one ρ
  change Module.finrank F E=1
  nlinarith
end Representation.ComponentTensor
