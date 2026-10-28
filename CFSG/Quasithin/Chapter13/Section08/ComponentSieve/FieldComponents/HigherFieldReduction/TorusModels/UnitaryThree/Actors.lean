module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree.Setup
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.RootNormalizer
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.TorusAction
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.DiagonalActors

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals

/-!
# Arbitrary unitary Borel actors and the three-residual fixer

For the standard special and projective unitary models, a two-group actor
stabilizing the concrete root range has an actual semilinear formula with
an upper triangular unitary representative and a two-power field parameter.
Only existence of an arbitrary semilinear formula is an earlier
classification input. Two-power order of the parameter and triangularity
are derived here, including when an involution power of the actor is inner.

The source displacement condition restricts to the image of the full
three-residual of `Eˣ`. In applications `B` is `borelResidual B₀`; its
identifications with `B₀` and its root two-core remain explicit Borel
premises. The triangular formula detects the field action on this full
torus, retaining the projective cubic kernel. Away from fixed-field degree
three, the field parameter is identity. Removing the root factor leaves a
diagonal actor whose order divides the odd number `|E| - 1`, so the given
two-subgroup forces this remaining actor to be identity. Thus the fixer is
exactly the root inner image, for arbitrary two-power actors.

The final two theorems state this calculation for `B = borelResidual B₀`.
Their only structural inputs beyond the stated Borel identities and actor
hypotheses are concrete semilinear coverage, the matrix form of GLS3,
Theorem 2.5.12(a,d,f) and Section 2.7. Coverage, the Borel identities and
transport from other forms and Sylow subgroups belong to the source
assembly; none is asserted by this conditional standard-model calculation.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954 (PDF p.971).
-/

public section

open Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree
variable {D K : Type*} [Group D] [Group K]

theorem fixesThreeTorus_displacement (B : Subgroup D) (a : MulAut D)
    (ha : FixesThreeTorus B a) (f : K →* D) (hf : f.range ≤ B)
    (k : K) (hk : k ∈ pResidual 3 K) : a (f k) * (f k)⁻¹ ∈ B.pCoreIn 2 := by
  let g : K →* B := f.codRestrict B (fun x => hf ⟨x, rfl⟩)
  have hg : g k ∈ pResidual 3 B :=
    map_pResidual_le 3 g (mem_map_of_mem g hk)
  have ht : f k ∈ residualIn 3 B := mem_map_of_mem B.subtype hg
  exact ha _ ((show residualIn 3 B ≤ residualIn 3 B ⊔ B.pCoreIn 2 from le_sup_left) ht)

theorem inner_root_fixes (B U : Subgroup D) (hU : B.pCoreIn 2 = U)
    (a : MulAut D) (ha : a ∈ U.map MulAut.conj) : FixesThreeTorus B a := by
  obtain ⟨u, hu, rfl⟩ := ha
  exact inner_twoCore_fixes B u (hU.symm ▸ hu)

variable {E : Type*} [Field E] (J : HermitianForm 3 E)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
open HermitianForm.BorelTorus

theorem special_torus_displacement
    (B : Subgroup J.specialSubgroup) (hB : B = specialBorel J hJ)
    (hU : B.pCoreIn 2 = specialRoot J hJ)
    (a : MulAut J.specialSubgroup) (ha : FixesThreeTorus B a)
    (k : Eˣ) (hk : k ∈ pResidual 3 Eˣ) :
    a (hermitianTorusSU J hJ k) * (hermitianTorusSU J hJ k)⁻¹ ∈ specialRoot J hJ := by
  rw [← hU]
  apply fixesThreeTorus_displacement B a ha (hermitianTorusSU J hJ) _ k hk
  rw [hB]
  exact le_sup_right

theorem projective_torus_displacement
    (B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hB : B = projectiveBorel J hJ) (hU : B.pCoreIn 2 = projectiveRoot J hJ)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : FixesThreeTorus B a)
    (k : Eˣ) (hk : k ∈ pResidual 3 Eˣ) :
    a (hermitianTorusPSU J hJ k) * (hermitianTorusPSU J hJ k)⁻¹ ∈ projectiveRoot J hJ := by
  rw [← hU]
  apply fixesThreeTorus_displacement B a ha (hermitianTorusPSU J hJ) _ k hk
  rw [hB]
  exact le_sup_right

variable [Finite E]

/-- Semilinear coverage for the given special-unitary actor supplies a
triangular representative and a field parameter of two-power order. -/
theorem special_actor_witness
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (A : Subgroup (MulAut J.specialSubgroup)) (hA : IsPGroup 2 A)
    (a : MulAut J.specialSubgroup) (ha : a ∈ A)
    (hroot : (specialRoot J hJ).map a.toMonoidHom = specialRoot J hJ)
    (hform : ∃ σ : E ≃+* E, J.HasSpecialUnitarySemilinearForm a σ) :
    ∃ (σ : E ≃+* E) (u : J.unitarySubgroup),
      (∃ r : ℕ, σ ^ (2 ^ r) = 1) ∧
      (∀ x : J.specialSubgroup,
        (a x).val = u.val * Matrix.GeneralLinearGroup.map σ.toRingHom x.val * u.val⁻¹) ∧
      u.val.val 1 0 = 0 ∧ u.val.val 2 0 = 0 ∧ u.val.val 2 1 = 0 := by
  obtain ⟨r, hr⟩ := hA ⟨a, ha⟩
  have hr' : a ^ (2 ^ r) = 1 := congrArg Subtype.val hr
  obtain ⟨σ, hσ⟩ := hform
  obtain ⟨τ, ⟨u, hu⟩, ht⟩ := hσ.exists_twoPower_field J hJ hr'
  have hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  exact ⟨τ, u, ht, hu,
    SemilinearActors.special_semilinear_upper J hJ hcard hfixed a τ u hu hroot⟩

/-- The projective witness is a formula in the genuine PGL image; no
scalar-kernel cancellation or uniqueness of field parameters is assumed. -/
theorem projective_actor_witness
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) (hA : IsPGroup 2 A)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ∈ A)
    (hroot : (projectiveRoot J hJ).map a.toMonoidHom = projectiveRoot J hJ)
    (hform : ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ) :
    ∃ (σ : E ≃+* E) (u : J.unitarySubgroup),
      (∃ r : ℕ, σ ^ (2 ^ r) = 1) ∧
      (∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
        (a x).val = Matrix.ProjGenLinGroup.mk u.val *
          Matrix.ProjGenLinGroup.map σ.toRingHom x.val *
          (Matrix.ProjGenLinGroup.mk u.val)⁻¹) ∧
      u.val.val 1 0 = 0 ∧ u.val.val 2 0 = 0 ∧ u.val.val 2 1 = 0 := by
  obtain ⟨r, hr⟩ := hA ⟨a, ha⟩
  have hr' : a ^ (2 ^ r) = 1 := congrArg Subtype.val hr
  obtain ⟨σ, hσ⟩ := hform
  obtain ⟨τ, ⟨u, hu⟩, ht⟩ := hσ.exists_twoPower_field J hJ hr'
  have hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  exact ⟨τ, u, ht, hu,
    SemilinearActors.projective_semilinear_upper J hJ hcard hfixed a τ u hu hroot⟩

/-- For SU₃ away from degree three, an actor in a two-subgroup containing
the root inner image fixes the source section exactly when it is root inner.
Semilinear coverage is an explicit earlier classification input; the field
parameter order, triangularity and diagonal elimination are proved. -/
theorem special_fixesThreeTorus_iff
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n)) (hn3 : n ≠ 3)
    (B : Subgroup J.specialSubgroup) (hB : B = specialBorel J hJ)
    (hU : B.pCoreIn 2 = specialRoot J hJ)
    (A : Subgroup (MulAut J.specialSubgroup)) (hA : IsPGroup 2 A)
    (hUA : (specialRoot J hJ).map MulAut.conj ≤ A)
    (a : MulAut J.specialSubgroup) (ha : a ∈ A)
    (hroot : (specialRoot J hJ).map a.toMonoidHom = specialRoot J hJ)
    (hform : ∃ σ : E ≃+* E, J.HasSpecialUnitarySemilinearForm a σ) :
    FixesThreeTorus B a ↔ a ∈ (specialRoot J hJ).map MulAut.conj := by
  constructor
  · intro hfix
    obtain ⟨σ, u, ⟨r, hr⟩, hu, h10, h20, h21⟩ :=
      special_actor_witness J hJ hn hcard hconj A hA a ha hroot hform
    have hσ : σ = 1 := (special_field_eq_one_or_degree_three J hJ hn hcard hconj σ hr
      (fun k hk => (SemilinearActors.special_semilinear_torus_displacement_iff
        J hJ a σ u h10 h20 h21 hu k).mp
          (special_torus_displacement J hJ B hB hU a hfix k hk))).resolve_right hn3
    subst σ
    apply SemilinearActors.special_identity_field_mem_root_inner
      J hJ hcard hn A hA hUA a ha u h10 h20 h21
    intro x
    rw [hu]
    change u.val * Matrix.GeneralLinearGroup.map (RingHom.id E) x.val * u.val⁻¹ = _
    simp
  · exact inner_root_fixes B (specialRoot J hJ) hU a

/-- The same arbitrary-actor calculation in the actual PSU₃ image. Fixation
is tested in the full projective torus, retaining its genuine cubic kernel. -/
theorem projective_fixesThreeTorus_iff
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n)) (hn3 : n ≠ 3)
    (B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hB : B = projectiveBorel J hJ) (hU : B.pCoreIn 2 = projectiveRoot J hJ)
    (A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) (hA : IsPGroup 2 A)
    (hUA : (projectiveRoot J hJ).map MulAut.conj ≤ A)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ∈ A)
    (hroot : (projectiveRoot J hJ).map a.toMonoidHom = projectiveRoot J hJ)
    (hform : ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ) :
    FixesThreeTorus B a ↔ a ∈ (projectiveRoot J hJ).map MulAut.conj := by
  constructor
  · intro hfix
    obtain ⟨σ, u, ⟨r, hr⟩, hu, h10, h20, h21⟩ :=
      projective_actor_witness J hJ hn hcard hconj A hA a ha hroot hform
    have hσ : σ = 1 := (projective_field_eq_one_or_degree_three J hJ hn hcard hconj σ hr
      (fun k hk => (SemilinearActors.projective_semilinear_torus_displacement_iff
        J hJ a σ u h10 h20 h21 hu k).mp
          (projective_torus_displacement J hJ B hB hU a hfix k hk))).resolve_right hn3
    subst σ
    apply SemilinearActors.projective_identity_field_mem_root_inner
      J hJ hcard hn A hA hUA a ha u h10 h20 h21
    intro x
    rw [hu]
    change Matrix.ProjGenLinGroup.mk u.val *
      Matrix.ProjGenLinGroup.map (RingHom.id E) x.val *
      (Matrix.ProjGenLinGroup.mk u.val)⁻¹ = _
    rw [Matrix.ProjGenLinGroup.map_id, MonoidHom.id_apply]
  · exact inner_root_fixes B (projectiveRoot J hJ) hU a

/-- Conditional standard SU₃ calculation for the source Borel residual.
The Borel task supplies `hB` and `hU`; `hform` is the concrete semilinear
coverage from GLS3, Theorem 2.5.12(a,d,f) and Section 2.7. Every actor in
`A` is allowed, including those with inner involution powers. -/
theorem special_borelResidual_fixesThreeTorus_iff
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n)) (hn3 : n ≠ 3)
    (hB : borelResidual (specialBorel J hJ) = specialBorel J hJ)
    (hU : (borelResidual (specialBorel J hJ)).pCoreIn 2 = specialRoot J hJ)
    (A : Subgroup (MulAut J.specialSubgroup)) (hA : IsPGroup 2 A)
    (hUA : (specialRoot J hJ).map MulAut.conj ≤ A)
    (hroot : ∀ a ∈ A, (specialRoot J hJ).map a.toMonoidHom = specialRoot J hJ)
    (hform : ∀ a ∈ A, ∃ σ : E ≃+* E, J.HasSpecialUnitarySemilinearForm a σ) :
    ∀ a ∈ A, FixesThreeTorus (borelResidual (specialBorel J hJ)) a ↔
      a ∈ (specialRoot J hJ).map MulAut.conj := by
  intro a ha
  exact special_fixesThreeTorus_iff J hJ hn hcard hconj hn3
    (borelResidual (specialBorel J hJ)) hB hU A hA hUA a ha (hroot a ha) (hform a ha)

/-- Conditional standard PSU₃ calculation for the source Borel residual,
using genuine `HasUnitarySemilinearForm` coverage as the earlier
classification input and keeping the two Borel identities explicit. -/
theorem projective_borelResidual_fixesThreeTorus_iff
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n)) (hn3 : n ≠ 3)
    (hB : borelResidual (projectiveBorel J hJ) = projectiveBorel J hJ)
    (hU : (borelResidual (projectiveBorel J hJ)).pCoreIn 2 = projectiveRoot J hJ)
    (A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) (hA : IsPGroup 2 A)
    (hUA : (projectiveRoot J hJ).map MulAut.conj ≤ A)
    (hroot : ∀ a ∈ A, (projectiveRoot J hJ).map a.toMonoidHom = projectiveRoot J hJ)
    (hform : ∀ a ∈ A, ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ) :
    ∀ a ∈ A, FixesThreeTorus (borelResidual (projectiveBorel J hJ)) a ↔
      a ∈ (projectiveRoot J hJ).map MulAut.conj := by
  intro a ha
  exact projective_fixesThreeTorus_iff J hJ hn hcard hconj hn3
    (borelResidual (projectiveBorel J hJ)) hB hU A hA hUA a ha (hroot a ha) (hform a ha)


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree
