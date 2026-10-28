module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Inputs
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Induction
public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline.Geometry

/-!
# Recognition of degree-twenty-one modules from the root multiplicity

The root-center fixed space is Borel invariant because the Borel normalizes
both the root subgroup and its characteristic center. If this space has
dimension one, its scalars define a character over the original field.
Frobenius reciprocity and the kernel quotient then give the exact
principal-series subquotient required by the recognition contract.

In degree twenty-one the independent nonlinear multiplicity formula forces
this fixed-space dimension to be one. No linear-weight gap, splitting-field
assumption or faithful action on the full special unitary group is needed.
The nonlinear formula remains an explicit premise until its owner proves it.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

public section

open BenderSuzuki.MatrixGroups
open HermitianForm.OddPrimeSylow.NormalizedOuter
open HermitianForm.BorelTorus

namespace Representation.SU3.FiveSmallModules.SevenRestriction

private theorem eigenline_of_invariant_line
    {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (L : Submodule K V)
    (hd : Module.finrank K L = 1)
    (hL : ∀ g v, v ∈ L → ρ g v ∈ L) :
    ∃ (χ : G →* Kˣ) (v : V), v ≠ 0 ∧ ∀ g, ρ g v = (χ g : K) • v := by
  classical
  obtain ⟨v, hv, hspan⟩ := finrank_eq_one_iff'.mp hd
  have hv' : (v : V) ≠ 0 := fun h => hv (Subtype.ext h)
  have hline (g : G) : ∃ a : K, ρ g (v : V) = a • (v : V) := by
    obtain ⟨a, ha⟩ := hspan ⟨ρ g v, hL g v v.property⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  choose a ha using hline
  have hone : a 1 = 1 := by
    apply smul_left_injective K hv'
    simpa using (ha 1).symm
  have hmul (g h : G) : a (g * h) = a g * a h := by
    apply smul_left_injective K hv'
    change a (g * h) • (v : V) = (a g * a h) • (v : V)
    rw [← ha, map_mul, Module.End.mul_apply, ha, map_smul, ha, smul_smul, mul_comm]
  have hne (g : G) : a g ≠ 0 := by
    intro hz
    have hh := hmul g g⁻¹
    rw [mul_inv_cancel, hone, hz, zero_mul] at hh
    exact one_ne_zero hh
  exact ⟨{ toFun := fun g => Units.mk0 (a g) (hne g)
           map_one' := Units.ext hone
           map_mul' := fun g h => Units.ext (hmul g h) }, v, hv', ha⟩

private theorem normalizes_center_image
    {G : Type*} [Group G] [Finite G] (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer ((Subgroup.center P).map P.subtype : Set G) := by
  intro g hg
  apply Subgroup.mem_normalizer_fintype
  rintro z ⟨z, hz, rfl⟩
  let a : P ≃* P := P.normalizerMonoidHom ⟨g, hg⟩
  have haz : a z ∈ Subgroup.center P :=
    (Subgroup.characteristic_iff_le_comap.mp inferInstance a) hz
  exact ⟨a z, haz, rfl⟩

open Degrees.RootEigenline

/-- The literal Borel normalizes the image of the intrinsic root center. -/
theorem borel_normalizes_root_center
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F) :
    standardBorel J ≤ Subgroup.normalizer (standardRootCenter J : Set (standardGroup J)) := by
  apply le_trans _ (normalizes_center_image (standardRoot J))
  exact sup_le (standardRoot J).le_normalizer
    (specialTorus_normalizes_root (FormTransport.standardForm J) rfl)

/-- A one-dimensional root-center fixed space gives a Borel character over
the original coefficient field. -/
theorem borel_eigenline_of_center_fixed_dimension_one
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (τ : Representation K (standardGroup J) V)
    (hd : Module.finrank K (invariants (τ.comp (standardRootCenter J).subtype)) = 1) :
    ∃ (χ : standardBorel J →* Kˣ) (v : V),
      v ≠ 0 ∧ ∀ b : standardBorel J, τ b v = (χ b : K) • v := by
  let Z := standardRootCenter J
  let L := invariants (τ.comp Z.subtype)
  apply eigenline_of_invariant_line (τ.comp (standardBorel J).subtype) L hd
  intro b v hv z
  have hz : (b : standardGroup J)⁻¹ * z * b ∈ Z := by
    simpa only [Subgroup.coe_inv, inv_inv] using (Subgroup.mem_normalizer_iff.mp
      (borel_normalizes_root_center J (b⁻¹).property) (z : standardGroup J)).mp z.property
  have hh := hv ⟨(b : standardGroup J)⁻¹ * z * b, hz⟩
  change τ ((b : standardGroup J)⁻¹ * z * b) v = v at hh
  change τ (z : standardGroup J) (τ b v) = τ b v
  rw [← Module.End.mul_apply, ← map_mul]
  calc
    τ ((z : standardGroup J) * b) v =
        τ ((b : standardGroup J) * ((b : standardGroup J)⁻¹ * z * b)) v := by
      congr 2
      group
    _ = τ b v := by rw [map_mul, Module.End.mul_apply, hh]

universe u v

/-- In degree twenty-one the nonlinear multiplicity calculation supplies the
fixed line and hence the exact induced-character subquotient. -/
theorem principal_series_recognition_twenty_one_of_nonlinear
    (hnonlinear : RootNonlinearMultiplicityInput.{u, v})
    {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    {K U : Type v} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K (standardGroup J) U)
    (hk : τ.ker ≤ Subgroup.center (standardGroup J))
    (hi : τ.IsAbsolutelyIrreducible) (hd : Module.finrank K U = 21) :
    ∃ (χ : standardBorel J →* Kˣ)
      (S : Subrepresentation (ind (standardBorel J).subtype (scalarCharacter χ)))
      (T : Subrepresentation S.toRepresentation),
      Nonempty (τ.Equiv T.quotientRepresentation) := by
  obtain ⟨a, ha, hda⟩ := hnonlinear F J hc hconj K U τ hk
  have hz : Module.finrank K (invariants (τ.comp (standardRootCenter J).subtype)) = 1 := by
    omega
  obtain ⟨χ, v, hv, hχ⟩ := borel_eigenline_of_center_fixed_dimension_one J τ hz
  let : τ.IsAbsolutelyIrreducible := hi
  let : τ.IsIrreducible := IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible τ
  refine ⟨χ, ?_⟩
  exact principal_series_subquotient_of_eigenline
    (K := K) (G := standardGroup J) (V := U) (standardBorel J) τ χ v hv hχ

end Representation.SU3.FiveSmallModules.SevenRestriction
