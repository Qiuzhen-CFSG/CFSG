module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline.NonlinearMultiplicity.RootGeometry
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CharacterCoverage
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison

/-!
# Root fusion and torus powers inside the actual SU₃(5) Borel

The root subgroup inside the Borel is identified with the existing
extraspecial group of order 125. The norm calculation in
`NonlinearMultiplicity.RootGeometry` is refined here to retain the torus
parameter of each central conjugation. This supplies fusion inside the Borel,
as required when applying the minimum-degree argument to Borel submodules.

The actual projective torus has order eight. Hence eighth powers of the
special torus belong to the SU center, and act trivially on representations
whose kernels contain that center. These are the concrete geometric inputs
to the root-intertwiner and torus-fixed-vector route.

Source: Huppert II.10.4 and II.10.12, and the root-group calculation underlying
Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3.
-/

@[expose] public section

noncomputable section
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open HermitianForm.BorelTorus HermitianForm.OddPrimeSylow.NormalizedOuter
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.BorelComparison
open Degrees.RootEigenline
open Degrees.RootEigenline.NonlinearMultiplicity
variable {F : Type*} [Field F] (J : HermitianForm 3 F)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

private theorem specialRoot_injective : Function.Injective (hermitianUnipotentSU J hJ) := by
  intro z w h
  apply Coverage.root_injective J hJ
  apply Subtype.ext
  exact congrArg ProjGenLinGroup.mk (congrArg Subtype.val h)

private def coordinateSpecialEquiv : hermitianUnipotentCoord J ≃* specialRoot J hJ :=
  MulEquiv.ofBijective (hermitianUnipotentSU J hJ).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr (specialRoot_injective J hJ),
      (hermitianUnipotentSU J hJ).rangeRestrict_surjective⟩

private theorem fixed_card [Finite F] (hc : Nat.card F = 5 ^ 2)
    (hconj : ∀ x, J.conj x = x ^ 5) : Nat.card {x : F // J.conj x = x} = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 5 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
    J.conj 5 1 (by decide) (by simpa only [pow_one] using hc)
    (by simpa only [pow_one] using hconj)

private theorem coord_center (z : hermitianUnipotentCoord J) (hz : z.val.1 = 0) :
    z ∈ center (hermitianUnipotentCoord J) := by
  apply mem_center_iff.mpr
  intro w
  apply Subtype.ext
  apply Prod.ext
  · exact add_comm _ _
  · change w.val.2 + z.val.2 - w.val.1 * J.conj z.val.1 =
      z.val.2 + w.val.2 - z.val.1 * J.conj w.val.1
    simp [hz, add_comm]

private theorem central_pow (z : hermitianUnipotentCoord J) (hz : z.val.1 = 0) (i : ℕ) :
    (z ^ i).val = (0, (i : F) * z.val.2) := by
  induction i with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul]; rfl
  | succ i ih =>
    rw [pow_succ]
    change ((z ^ i).val.1 + z.val.1,
      (z ^ i).val.2 + z.val.2 - (z ^ i).val.1 * J.conj z.val.1) = _
    rw [ih, hz]
    simp [Nat.cast_succ, add_mul]

/-- A nonidentity root-central element is fused to every nonidentity power
by actual SU torus elements. -/
public theorem specialRoot_central_torus_fusion [Finite F] (hc : Nat.card F = 5 ^ 2)
    (hconj : ∀ x, J.conj x = x ^ 5) :
    ∃ z : specialRoot J hJ, z ∈ center (specialRoot J hJ) ∧ z ≠ 1 ∧
      ∀ i : ℕ, 0 < i → i < 5 → ∃ k : Fˣ,
        hermitianTorusSU J hJ k * (z : J.specialSubgroup) * (hermitianTorusSU J hJ k)⁻¹ = (z : J.specialSubgroup) ^ i := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 5 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  have hf := fixed_card J hc hconj
  have hn : ∃ x : F, J.conj x ≠ x := by
    by_contra! hn
    let e : {x : F // J.conj x = x} ≃ F :=
      { toFun := Subtype.val
        invFun := fun x => ⟨x, hn x⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hh := Nat.card_congr e
    rw [hc, hf] at hh
    norm_num at hh
  obtain ⟨x, hx⟩ := hn
  let z : hermitianUnipotentCoord J := ⟨(0, x - J.conj x), by
    change (x - J.conj x) + J.conj (x - J.conj x) + 0 * J.conj 0 = 0
    rw [map_sub, J.conj_involutive]
    ring⟩
  have hz : z.val.1 = 0 := rfl
  have hz1 : z ≠ 1 := by
    intro he
    exact hx.symm (sub_eq_zero.mp (congrArg (fun w : hermitianUnipotentCoord J => w.val.2) he))
  refine ⟨coordinateSpecialEquiv J hJ z,
    (centerCongr (coordinateSpecialEquiv J hJ) ⟨z, coord_center J z hz⟩).property,
    (coordinateSpecialEquiv J hJ).map_ne_one_iff.mpr hz1, ?_⟩
  intro i hi0 hi5
  have hi : (i : F) ≠ 0 := by
    intro he
    exact Nat.not_dvd_of_pos_of_lt hi0 hi5 ((CharP.cast_eq_zero_iff F 5 i).mp he)
  obtain ⟨k, hk0, hk⟩ := huppert_II_10_4_norm_surjective J 5 hc hf
    (i : F)⁻¹ (by simp) (inv_ne_zero hi)
  let ku : Fˣ := Units.mk0 k hk0
  have ha : hermitianTorusAction J ku z = z ^ i := by
    apply Subtype.ext
    rw [central_pow J z hz i]
    apply Prod.ext
    · rw [hermitianTorusAction_fst, hz]; simp
    · rw [hermitianTorusAction_snd]
      change z.val.2 * (J.conj k)⁻¹ * k⁻¹ = (i : F) * z.val.2
      calc
        _ = z.val.2 * (k * J.conj k)⁻¹ := by rw [mul_inv]; ring
        _ = (i : F) * z.val.2 := by rw [hk, inv_inv, mul_comm]
  refine ⟨ku, ?_⟩
  change hermitianTorusSU J hJ ku * hermitianUnipotentSU J hJ z * _ =
    hermitianUnipotentSU J hJ z ^ i
  apply (mul_inv_eq_iff_eq_mul).mpr
  rw [← map_pow, ← ha]
  exact Subtype.ext (hermitianTorusGL_mul_unipotent J ku z)


end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.BorelComparison

namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.BorelComparison
open Subgroup BenderSuzuki.MatrixGroups
open Degrees Degrees.RootEigenline
open Degrees.RootEigenline.NonlinearMultiplicity
open HermitianForm.OddPrimeSylow.NormalizedOuter

variable {F : Type*} [Field F] (J : HermitianForm 3 F)

/-- The root subgroup inside the literal Borel carrier. -/
abbrev borelRoot : Subgroup (standardBorel J) :=
  (standardRoot J).subgroupOf (standardBorel J)

/-- The embedded root has exactly the original special-unitary root carrier. -/
def borelRootEquiv : borelRoot J ≃* standardRoot J :=
  Subgroup.subgroupOfEquivOfLe (show standardRoot J ≤ standardBorel J from le_sup_left)

/-- The root inside the Borel is extraspecial of order 125. -/
theorem borelRoot_structure [Finite F] (hc : Nat.card F = 5 ^ 2)
    (hconj : ∀ x, J.conj x = x ^ 5) :
    IsExtraspecial 5 (borelRoot J) ∧ Nat.card (borelRoot J) = 5 ^ 3 := by
  obtain ⟨hp, hcard⟩ := specialRoot_structure (FormTransport.standardForm J) rfl hc hconj
  exact ⟨IsExtraspecial.of_mulEquiv (borelRootEquiv J).symm hp,
    (Nat.card_congr (borelRootEquiv J).toEquiv).trans hcard⟩

/-- All nonidentity powers of a central generator are fused inside the
actual Borel, with an explicit full-torus parameter. -/
theorem borelRoot_central_fusion [Finite F] (hc : Nat.card F = 5 ^ 2)
    (hconj : ∀ x, J.conj x = x ^ 5) :
    ∃ z : borelRoot J, z ∈ center (borelRoot J) ∧ z ≠ 1 ∧
      ∀ i : ℕ, 0 < i → i < 5 → ∃ k : Fˣ,
        Degrees.principalTorusIn J k * (z : standardBorel J) *
          (Degrees.principalTorusIn J k)⁻¹ = (z : standardBorel J) ^ i := by
  obtain ⟨z, hz, hz1, hfusion⟩ :=
    specialRoot_central_torus_fusion (FormTransport.standardForm J) rfl hc hconj
  refine ⟨(borelRootEquiv J).symm z,
    (centerCongr (borelRootEquiv J).symm ⟨z, hz⟩).property,
    (borelRootEquiv J).symm.map_ne_one_iff.mpr hz1, ?_⟩
  intro i hi0 hi5
  obtain ⟨k, hk⟩ := hfusion i hi0 hi5
  refine ⟨k, ?_⟩
  apply Subtype.ext
  exact hk

/-- Restricting to the Borel preserves the literal root-center fixed space. -/
theorem borelRootCenter_invariants_eq_bot
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (ρ : Representation K (standardGroup J) V)
    (hfix : invariants (ρ.comp (standardRootCenter J).subtype) = ⊥) :
    invariants ((ρ.comp (standardBorel J).subtype).comp
      ((center (borelRoot J)).map (borelRoot J).subtype).subtype) = ⊥ := by
  apply bot_unique
  intro v hv
  have hmem : v ∈ invariants (ρ.comp (standardRootCenter J).subtype) := by
    rintro ⟨x, hx⟩
    obtain ⟨w, hw, rfl⟩ := hx
    have hwB := (centerCongr (borelRootEquiv J).symm ⟨w, hw⟩).property
    exact hv ⟨(borelRootEquiv J).symm w, ⟨(borelRootEquiv J).symm w, hwB, rfl⟩⟩
  rw [hfix] at hmem
  exact hmem

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.BorelComparison

open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.BorelTorus HermitianForm.OddPrimeSylow.NormalizedOuter
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.BorelComparison
open Degrees Degrees.RootEigenline

variable {F : Type*} [Field F] (J : HermitianForm 3 F)

/-- The eighth power of every full-torus element belongs to the SU center.
This uses the actual projective torus of order eight. -/
theorem torus_pow_eight_mem_center [Finite F]
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5) (k : Fˣ) :
    (principalTorusIn J k : standardGroup J) ^ 8 ∈ center (standardGroup J) := by
  let J₀ := FormTransport.standardForm J
  have ht : Nat.card (projectiveTorus J₀ rfl) = 8 := by
    simpa using projective_card J₀ rfl hc hconj
  have hp := pow_card_eq_one'
    (x := (⟨hermitianTorusPSU J₀ rfl k, ⟨k, rfl⟩⟩ : projectiveTorus J₀ rfl))
  rw [ht] at hp
  apply J₀.specialToProjective_ker_le_center
  apply MonoidHom.mem_ker.mpr
  rw [map_pow]
  have he : J₀.specialToProjective (principalTorusIn J k : standardGroup J) =
      hermitianTorusPSU J₀ rfl k := by
    apply Subtype.ext
    rw [J₀.specialToProjective_apply_val]
    rfl
  rw [he]
  exact congrArg Subtype.val hp

/-- On a module with trivial SU-center action, every full-torus operator
has eighth power one. In characteristic two this is a unipotent operator. -/
theorem torus_operator_pow_eight [Finite F]
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (ρ : Representation K (standardGroup J) V)
    (hcenter : center (standardGroup J) ≤ ρ.ker) (k : Fˣ) :
    ρ (principalTorusIn J k : standardGroup J) ^ 8 = 1 := by
  rw [← map_pow]
  exact MonoidHom.mem_ker.mp (hcenter (torus_pow_eight_mem_center J hc hconj k))

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.BorelComparison
