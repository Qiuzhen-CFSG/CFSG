module

public import Theory.SpecificGroups.PSU3.UniversalCover.Projection
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.TwoPrimary.MixedCommutators
public import Theory.GroupTheory.PerfectCentralCoverPrimeReduction
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity.DirectSylowCenters.UnitaryActions

/-!
# No defining-characteristic kernel for PSU₃ over even fields

For a perfect central double cover, the proved unitary normalizer action forces
its Sylow center to equal the covering kernel. But the mixed commutator lemma
makes every lift of a central root element central in the lifted Sylow. A
nonidentity central root element therefore gives a contradiction. The general
prime-kernel quotient reduction excludes two from every finite perfect central
cover, including the literal universal projection.

A genuine change of Hermitian basis transports this calculation to arbitrary
nondegenerate forms without changing the original kernel. All exponents n ≥ 2
are retained, including q = 4.

Source: Aschbacher–Smith I.1.3, printed p.407 (PDF p.418), and GLS3,
Theorem 6.1.4, Tables 6.1.2–3. Coordinates and norm-one tori: Huppert II.10.12.
-/

public section
open Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm
open BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
open BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.EvenCenterAction
open PerfectCentralCovering

namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound

/-- A standard-form binary unitary group admits no perfect central double cover. -/
private theorem cover_kernel_card_ne_two_standard
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ n)
    {E : Type*} [Group E] [Finite E]
    (c : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card c.toMonoidHom.ker ≠ 2 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa [Nat.card_eq_fintype_card, pow_mul] using hcard)
  intro hck
  let Q : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
    EvenTwoRank.rootSylow J hJ (by omega : 0 < n) hcard hfixed
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective c.surjective 2 Q
  have hmap : (P : Subgroup E).map c.toMonoidHom = (Q : Subgroup _) := by
    rw [← Sylow.coe_mapSurjective c.surjective P, hP]
  have hQroot : (Q : Subgroup _) = projectiveRoot J hJ := by
    rw [EvenTwoRank.rootSylow_coe J hJ (by omega : 0 < n) hcard hfixed]
    rfl
  let b : Multiplicative (fixedField J) := Multiplicative.ofAdd 1
  have hb : b ≠ 1 := by
    intro h
    exact one_ne_zero (α := fixedField J) (congrArg Multiplicative.toAdd h)
  have hz : centralMap J hJ b ≠ 1 := by
    intro h
    apply hb
    apply (EvenCenterAction.centralMap_injective J hJ)
    simpa using h
  have hzQ : (centralMap J hJ b : _) ∈ (Q : Subgroup _) := by
    rw [hQroot]
    exact centralImage_le_root J hJ ⟨b, rfl⟩
  obtain ⟨x, hxP, hxz⟩ : ∃ x : E, x ∈ (P : Subgroup E) ∧
      c.toMonoidHom x = centralMap J hJ b := by
    have hm : (centralMap J hJ b : _) ∈ (P : Subgroup E).map c.toMonoidHom := by
      rw [hmap]
      exact hzQ
    exact hm
  have hxcenter : (⟨x, hxP⟩ : P) ∈ center P := by
    apply mem_center_iff.mpr
    intro y
    have hyP : (y : E) ∈ (P : Subgroup _) := y.property
    have hyQ : c.toMonoidHom (y : E) ∈ (Q : Subgroup _) := by
      rw [← hmap]
      exact ⟨y, hyP, rfl⟩
    have hyroot : c.toMonoidHom (y : E) ∈ projectiveRoot J hJ := by
      rw [← hQroot]
      exact hyQ
    have hxy := commute_of_central_root_images J hJ
      (lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) hn))
      hcard hfixed c.toMonoidHom c.surjective c.ker_le_center b hxz hyroot
    exact Subtype.ext hxy.eq.symm
  have hcenterker :=
    BenderSuzuki.ZD.DirectSylowCenters.UnitaryActions.cover_center J hJ hn hcard hfixed
      c hck (MulEquiv.refl _) P
  have hxker : x ∈ c.toMonoidHom.ker := by
    have hxmap : x ∈ (center P).map (P : Subgroup _).subtype :=
      ⟨⟨x, hxP⟩, hxcenter, rfl⟩
    rw [hcenterker] at hxmap
    exact hxmap
  exact hz (by simpa [hxz] using (MonoidHom.mem_ker.mp hxker))

open OddPrimeSylow.NormalizedOuter.FormTransport in
/-- Two does not divide any finite perfect central kernel over the actual
PSU₃(q), with arbitrary Hermitian form and q = 2^n, n ≥ 2. -/
theorem not_two_dvd_cover_kernel
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    {E : Type*} [Group E] [Finite E]
    (c : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ 2 ∣ Nat.card c.toMonoidHom.ker := by
  have hfixed := card_fixed J hcard hconj
  obtain ⟨e⟩ := exists_projectiveEquiv J (2 ^ n) hcard hfixed
  let J₀ := standardForm J
  let f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J₀) := {
    toMonoidHom := e.toMonoidHom.comp c.toMonoidHom
    surjective := e.surjective.comp c.surjective
    isPerfect := c.isPerfect
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
      exact c.ker_le_center }
  have hker : f.toMonoidHom.ker = c.toMonoidHom.ker :=
    MonoidHom.ker_comp_of_injective _ _ e.injective
  have hfixed₀ : Nat.card {x : F // J₀.conj x = x} = 2 ^ n := by
    simpa only [J₀, standardForm_conj] using hfixed
  rw [← hker]
  apply f.not_dvd_card_kernel_of_no_prime_kernel
  intro D _ _ d
  exact cover_kernel_card_ne_two_standard J₀ (standardForm_form J) hn hcard hfixed₀ d

/-- The literal universal perfect cover of the actual even-field PSU₃ has
odd kernel order, for every Hermitian form and every exponent n ≥ 2. -/
theorem not_two_dvd_universal_kernel
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    ¬ 2 ∣ Nat.card
      (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker := by
  have hq : 2 < 2 ^ n := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hn)
  let := projective_isQuasisimple J hq hcard hconj
  exact not_two_dvd_cover_kernel J hn hcard hconj (universalCover _)

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound
