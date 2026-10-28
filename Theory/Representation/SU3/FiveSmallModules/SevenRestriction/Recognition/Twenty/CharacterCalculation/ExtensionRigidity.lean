module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.ExtensionRigidity.Inputs
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.ExtensionRigidity.Injectivity
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.Geometry
public import Theory.SpecificGroups.SU3.Quasisimplicity

/-!
# From the averaged Bruhat calculation to extension rigidity

Conjugate the second action by the given Borel equivalence. Both actions now
have literally the same Borel matrices and hence the same averaged Bruhat
operator. The zero root-center invariant spaces give the same right sides.
Injectivity identifies their Weyl actions. The actual upper and opposite
projective roots generate PSU; the central-kernel hypothesis then lifts
agreement to SU. Transport back gives the requested equivalence over K.

The checked uniform injectivity calculation discharges the remaining premise,
proving `TwentyBorelExtensionRigidity` for the supplied Borel equivalence.
No irreducibility or splitting-field hypothesis is imposed on either input,
and the conclusion retains the original coefficient field.

Source: Huppert II.10.12–13 for the concrete Bruhat relation and root generation.
Application: Guralnick–Malle, Classification of 2F-modules I, Proposition 4.3,
pp.10–11, and Aschbacher–Smith K.2, printed p.453.
-/

public section

open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open HermitianForm.BorelTorus HermitianForm.OddPrimeSylow.NormalizedOuter

namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity
variable {F : Type*} [Field F] (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- For central-trivial SU actions, agreement on the Borel and Weyl element
implies agreement everywhere. The genuine projective root generation
is pulled back together with the actual central kernel. -/
theorem eq_of_borel_weyl [Finite F]
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    (ρ σ : Representation K J.specialSubgroup V)
    (hρ : center J.specialSubgroup ≤ ρ.ker)
    (hσ : center J.specialSubgroup ≤ σ.ker)
    (hb : ∀ g ∈ specialBorel J hJ, ρ g = σ g)
    (hw : ρ (hermitianWeylSU J hJ) = σ (hermitianWeylSU J hJ)) : ρ = σ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hf : Nat.card {x : F // J.conj x = x} = 5 := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
      J.conj 5 1 (by decide) (by simpa using hc) (by simpa using hconj)
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    huppert_II_10_13 J 5 (by decide) hc hf
  let H : Subgroup J.specialSubgroup := ρ.eqLocus σ
  have hr (z : hermitianUnipotentCoord J) : hermitianUnipotentSU J hJ z ∈ H :=
    hb _ (mem_sup_left ⟨_, rfl⟩)
  have hw' : hermitianWeylSU J hJ ∈ H := hw
  have hroot (z : hermitianUnipotentCoord J) :
      J.specialToProjective (hermitianUnipotentSU J hJ z) = Coverage.root J hJ z := by
    apply Subtype.ext
    rw [J.specialToProjective_apply_val]
    rfl
  have hweyl : J.specialToProjective (hermitianWeylSU J hJ) = Coverage.weyl J hJ := by
    apply Subtype.ext
    rw [J.specialToProjective_apply_val]
    rfl
  have hle : Coverage.rootGroup J hJ ⊔ Coverage.oppositeRootGroup J hJ ≤
      H.map J.specialToProjective := by
    apply sup_le
    · rintro x ⟨z, rfl⟩
      rw [← hroot]
      exact mem_map_of_mem _ (hr z)
    · rintro x ⟨z, rfl⟩
      have hm := mem_map_of_mem J.specialToProjective
        (H.mul_mem (H.mul_mem hw' (hr z)) (H.inv_mem hw'))
      simpa only [map_mul, map_inv, hroot, hweyl, Coverage.oppositeRoot_apply] using hm
  have hm : H.map J.specialToProjective = ⊤ := by
    apply top_le_iff.mp
    rw [← Coverage.rootGroup_sup_oppositeRootGroup J hJ (by decide : 1 < 5) hc hf]
    exact hle
  have hk : J.specialToProjective.ker ≤ H := by
    intro g hg
    change ρ g = σ g
    exact (hρ (J.specialToProjective_ker_le_center hg)).trans
      (hσ (J.specialToProjective_ker_le_center hg)).symm
  have he := congrArg (Subgroup.comap J.specialToProjective) hm
  rw [comap_map_eq, comap_top, sup_eq_left.mpr hk] at he
  exact MonoidHom.ext fun g => show g ∈ H from he.symm ▸ mem_top g

variable {W : Type*} [AddCommGroup W] [Module K W]

/-- Transport the supplied Borel equivalence, solve the Weyl equations,
and return an equivalence over the original coefficient field. -/
theorem equiv_of_injective [Finite F]
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    (ρ : Representation K J.specialSubgroup V) (σ : Representation K J.specialSubgroup W)
    (hρ : center J.specialSubgroup ≤ ρ.ker)
    (hσ : center J.specialSubgroup ≤ σ.ker)
    (hzρ : invariants (ρ.comp ((center (specialRoot J hJ)).map
      (specialRoot J hJ).subtype).subtype) = ⊥)
    (hzσ : invariants (σ.comp ((center (specialRoot J hJ)).map
      (specialRoot J hJ).subtype).subtype) = ⊥)
    (e : Representation.Equiv (ρ.comp (specialBorel J hJ).subtype)
      (σ.comp (specialBorel J hJ).subtype))
    (hinj : Function.Injective (rootCosetOperator J hJ ρ)) : Nonempty (ρ.Equiv σ) := by
  let τ : Representation K J.specialSubgroup V :=
    (e.toLinearEquiv.symm.conjAlgEquiv K).toMonoidHom.comp σ
  have hb : ∀ g ∈ specialBorel J hJ, ρ g = τ g := by
    intro g hg
    exact (e.symm.conj_apply_self ⟨g, hg⟩).symm
  have ht : center J.specialSubgroup ≤ τ.ker := by
    intro g hg
    change e.toLinearEquiv.symm.conj (σ g) = 1
    rw [show σ g = 1 from hσ hg]
    exact map_one (e.toLinearEquiv.symm.conjAlgEquiv K)
  have hzt : invariants (τ.comp ((center (specialRoot J hJ)).map
      (specialRoot J hJ).subtype).subtype) = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    have hm : e v ∈ invariants (σ.comp ((center (specialRoot J hJ)).map
        (specialRoot J hJ).subtype).subtype) := by
      intro g
      change σ (g : J.specialSubgroup) (e.toLinearEquiv v) = e.toLinearEquiv v
      have hh := congrArg e.toLinearEquiv (hv g)
      change e.toLinearEquiv (e.toLinearEquiv.symm (σ g (e.toLinearEquiv v))) = e.toLinearEquiv v at hh
      simpa only [LinearEquiv.apply_symm_apply] using hh
    have hh : e v = 0 := by simpa only [hzσ, Submodule.mem_bot] using hm
    exact (e.toLinearEquiv.map_eq_zero_iff).mp hh
  have hw := weyl_eq_of_injective J hJ ρ τ hzρ hzt hb hinj
  have heq := eq_of_borel_weyl J hJ hc hconj ρ τ hρ ht hb hw
  refine ⟨Representation.Equiv.mk e.toLinearEquiv ?_⟩
  intro g
  ext v
  have hh := LinearMap.congr_fun (congrArg (fun t : Representation K J.specialSubgroup V => t g) heq) v
  change ρ g v = e.toLinearEquiv.symm (σ g (e.toLinearEquiv v)) at hh
  change e.toLinearEquiv (ρ g v) = σ g (e.toLinearEquiv v)
  rw [hh, LinearEquiv.apply_symm_apply]

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity

namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
open Degrees.RootEigenline
universe v

/-- The averaged-operator injectivity calculation discharges the entire
extension contract on the original representations and their supplied Borel equivalence. -/
theorem twenty_borel_extension_rigidity_of_rootCosetInjectivity
    (hinj : TwentyRootCosetInjectivity.{v}) : TwentyBorelExtensionRigidity.{v} := by
  intro F _ _ J hc hconj K _ _ _ U _ _ _ W _ _ _ ρ σ hd _hdσ hρ hσ hzρ hzσ he
  obtain ⟨e⟩ := he
  apply ExtensionRigidity.equiv_of_injective (FormTransport.standardForm J) rfl hc hconj
    ρ σ hρ hσ hzρ hzσ e
  exact hinj F J hc hconj K U ρ hd hρ hzρ

/-- The supplied degree-twenty Borel equivalence extends to an equivalence
of the original SU representations. The checked averaged Bruhat calculation
determines the Weyl action without an irreducibility or splitting hypothesis. -/
theorem twenty_borel_extension_rigidity : TwentyBorelExtensionRigidity.{v} :=
  twenty_borel_extension_rigidity_of_rootCosetInjectivity twenty_rootCoset_injectivity

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
