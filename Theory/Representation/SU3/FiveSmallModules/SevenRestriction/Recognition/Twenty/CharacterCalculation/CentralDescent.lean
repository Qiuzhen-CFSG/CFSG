module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.Inputs
public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline.NonlinearMultiplicity
public import Theory.Representation.PGroupScalarWitness
public import Theory.Representation.EndFieldRep
public import Theory.SpecificGroups.SU3.Quasisimplicity

/-!
# Central descent for all simple degree-twenty SU₃(5) modules

The nonlinear root calculation bounds every central-kernel representation
below by twenty, over every finite field of characteristic two. For a simple
module of dimension twenty, apply that bound over its actual Schur
endomorphism field. The scalar-tower dimension formula forces this field to
be the original coefficient field, proving absolute irreducibility.

Perfectness makes the determinant trivial. Schur's lemma then makes a
central element a scalar with both cube and twentieth power one, so it acts
trivially. Quasisimplicity supplies the reverse kernel containment. Finally,
the exact nonlinear multiplicity formula forces the embedded root center to
have zero fixed space. This distinguishes the root center from the SU center.

`trivial_twenty_factor_structure` in `CharacterCalculation` applies these results
to the literal comparison quotient, whose input is only irreducibility over
its original field. No composition-factor catalogue is used.

Source: extraspecial degree theory in `RootEigenline.NonlinearMultiplicity`;
Huppert II.10.12–13 for the actual SU carrier. Application: Guralnick–Malle,
*Classification of 2F-modules I*, Proposition 4.3, pp.10–11, and
Aschbacher–Smith K.2, printed p.453.
-/

public section

open BenderSuzuki.MatrixGroups Subgroup
open HermitianForm.OddPrimeSylow.NormalizedOuter
open scoped MonoidAlgebra
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
open Degrees.RootEigenline
universe u v

private theorem central_cube_acts_trivially
    {K G U : Type*} [Field K] [Group G] [Group.IsPerfect G]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K G U) [τ.IsAbsolutelyIrreducible]
    (hd : Module.finrank K U = 20) (z : G) (hz : z ∈ center G)
    (hz3 : z ^ 3 = 1) : τ z = 1 := by
  let : τ.IsIrreducible := IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible τ
  let : Nontrivial U := Subrepresentation.irreducible_module_nontrivial τ
  obtain ⟨a, ha⟩ := exists_scalar_of_mem_center_of_absolutelyIrreducible τ z hz
  change τ z = a • (1 : Module.End K U) at ha
  have ha3 : a ^ 3 = 1 := by
    apply (algebraMap K (Module.End K U)).injective
    rw [map_pow, map_one]
    change (a • (1 : Module.End K U)) ^ 3 = 1
    rw [← ha, ← map_pow, hz3, map_one]
  have ha20 : a ^ 20 = 1 := by
    have hdet : LinearMap.det (τ z) = 1 := by
      let f : G →* Kˣ := MonoidHom.toHomUnits (LinearMap.det.comp τ)
      let : Group.IsPerfect f.range := Group.IsPerfect.range f
      have h : (⟨f z, ⟨z, rfl⟩⟩ : f.range) = 1 := Subsingleton.elim _ _
      exact congrArg (fun b : f.range => (b.val : K)) h
    simpa only [ha, LinearMap.det_smul, map_one, hd, mul_one] using hdet
  have ha1 : a = 1 := by
    calc
      a = a ^ (20 + 1) := by rw [pow_add, ha20, pow_one, one_mul]
      _ = (a ^ 3) ^ 7 := by rw [← pow_mul]
      _ = 1 := by rw [ha3, one_pow]
  rw [ha, ha1, one_smul]

private theorem standard_fixed_card
    {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5) :
    Nat.card {x : F // (FormTransport.standardForm J).conj x = x} = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  simpa only [FormTransport.standardForm_conj, pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
    J.conj 5 1 (by decide) (by simpa using hc) (by simpa using hconj)

/-- Absolute degree twenty kills the entire SU center over the original field. -/
theorem center_le_ker_of_absolute_twenty
    {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    {K U : Type v} [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K (standardGroup J) U) [τ.IsAbsolutelyIrreducible]
    (hd : Module.finrank K U = 20) : center (standardGroup J) ≤ τ.ker := by
  let J₀ := FormTransport.standardForm J
  have hf := standard_fixed_card J hc hconj
  let : Group.IsPerfect (standardGroup J) :=
    J₀.special_isPerfect_of_fixed_card (by decide : 2 < 5) hc hf
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    J₀.projective_isPerfect_of_fixed_card (by decide : 2 < 5) hc hf
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    BenderSuzuki.External.huppert_II_10_13 J₀ 5 (by decide) hc hf
  have hz : center (ProjectiveSpecialUnitaryMatrixGroup J₀) = ⊥ := by
    rcases (inferInstance : (center (ProjectiveSpecialUnitaryMatrixGroup J₀)).Normal).eq_bot_or_eq_top
      with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h)).elim
  intro z hzmem
  apply MonoidHom.mem_ker.mpr
  apply central_cube_acts_trivially τ hd z hzmem
  have hzker : z ∈ J₀.specialToProjective.ker := by
    rw [J₀.specialToProjective_ker_eq_center hz]
    exact hzmem
  exact congrArg Subtype.val (J₀.specialToProjective_ker_cube ⟨z, hzker⟩)

private theorem ker_le_center_of_irreducible_twenty
    {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    {K U : Type v} [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K (standardGroup J) U) [τ.IsIrreducible]
    (hd : Module.finrank K U = 20) : τ.ker ≤ center (standardGroup J) := by
  classical
  let : Theory.GroupTheory.IsQuasisimple (standardGroup J) :=
    (FormTransport.standardForm J).special_isQuasisimple_of_fixed_card
      (by decide : 2 < 5) hc (standard_fixed_card J hc hconj)
  rcases Theory.GroupTheory.IsQuasisimple.normal_le_center_or_eq_top τ.ker with hk | hk
  · exact hk
  have htriv (g : standardGroup J) : τ g = 1 :=
    MonoidHom.mem_ker.mp (hk ▸ mem_top g)
  let b := Module.finBasis K U
  let i : Fin (Module.finrank K U) := ⟨0, by omega⟩
  let W : Subrepresentation τ :=
    { toSubmodule := Submodule.span K {b i}
      apply_mem_toSubmodule := by
        intro g v hv
        simpa only [htriv, Module.End.one_apply] using hv }
  have hWne : W ≠ ⊥ := by
    intro hW
    have hv : b i ∈ W := Submodule.subset_span (Set.mem_singleton (b i))
    rw [hW] at hv
    exact b.ne_zero i hv
  have hWtop : W = ⊤ := (eq_bot_or_eq_top W).resolve_left hWne
  have he : W.toSubmodule = ⊤ := congrArg Subrepresentation.toSubmodule hWtop
  have hdim : Module.finrank K W.toSubmodule = 1 := finrank_span_singleton (b.ne_zero i)
  rw [he, finrank_top, hd] at hdim
  omega

/-- A simple degree-twenty module over a finite binary-characteristic field is already absolute. -/
theorem absolute_of_irreducible_twenty
    {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    {K U : Type v} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K (standardGroup J) U) [τ.IsIrreducible]
    (hd : Module.finrank K U = 20) : τ.IsAbsolutelyIrreducible := by
  let E := Module.End K[standardGroup J] τ.asModule
  let : Finite τ.asModule := Module.finite_of_finite K
  let : FiniteDimensional E τ.asModule := Module.Finite.of_finite
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap K E).injective 2
  have hk : τ.endFieldRep.ker ≤ center (standardGroup J) := by
    intro g hg
    apply ker_le_center_of_irreducible_twenty J hc hconj τ hd
    apply MonoidHom.mem_ker.mpr
    ext v
    have h := LinearMap.congr_fun (MonoidHom.mem_ker.mp hg) (τ.asModuleEquiv.symm v)
    exact congrArg τ.asModuleEquiv h
  obtain ⟨a, ha, hdim⟩ := root_nonlinear_multiplicity_input
    F J hc hconj E τ.asModule τ.endFieldRep hk
  have hmin : 20 ≤ Module.finrank E τ.asModule := by omega
  have ht := Module.finrank_mul_finrank K E τ.asModule
  rw [τ.asModuleEquiv.finrank_eq, hd] at ht
  have hEpos : 0 < Module.finrank K E := Module.finrank_pos
  have hE : Module.finrank K E = 1 := by nlinarith
  apply (isAbsolutelyIrreducible_iff_surjective τ).mpr
  apply (algebraMap_surj_iff_surj τ).mp
  exact (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hE).2

/-- Every simple degree-twenty module has exactly the SU center as kernel
and no fixed vectors for the embedded root center. -/
theorem irreducible_twenty_kernel_and_root_invariants
    {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    {K U : Type v} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K (standardGroup J) U) [τ.IsIrreducible]
    (hd : Module.finrank K U = 20) :
    τ.ker = center (standardGroup J) ∧
      invariants (τ.comp (standardRootCenter J).subtype) = ⊥ := by
  have hk := ker_le_center_of_irreducible_twenty J hc hconj τ hd
  let : τ.IsAbsolutelyIrreducible := absolute_of_irreducible_twenty J hc hconj τ hd
  refine ⟨hk.antisymm (center_le_ker_of_absolute_twenty J hc hconj τ hd), ?_⟩
  obtain ⟨a, ha, hdim⟩ := root_nonlinear_multiplicity_input F J hc hconj K U τ hk
  have hz : Module.finrank K (invariants (τ.comp (standardRootCenter J).subtype)) = 0 := by
    rw [hd] at hdim
    omega
  exact Submodule.finrank_eq_zero.mp hz
end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
