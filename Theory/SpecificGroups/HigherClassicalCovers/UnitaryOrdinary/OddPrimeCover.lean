module

public import Theory.GroupTheory.CentralExtensionPullback
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime.Index
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime.Lifts.Sections
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime.Lifts.Relations
public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic
public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryCyclotomic
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.PerfectCentralCoverPrimeReduction
public import Theory.GroupTheory.CoveringKernelEquiv
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient

/-!
# Odd central covers of PSU₄ over prime fixed fields

For primes greater than three, compatible torus-equivariant root lifts split
the positive subgroup in every prime-degree cover. Pulling the original
projective cover back along SU₄ → PSU₄ applies that construction without
assuming any universal covering property. Its section descends to the actual
projective Sylow subgroup, and transfer excludes the defining prime.
The two independent torus calculations exclude every other odd prime.

Consequently every finite perfect cover has a two-group kernel, and an odd
kernel is trivial. The final adapters use the original marked central quotient.
At the exceptional prime three only the proved three-group support conclusion
is asserted; neither a scalar lift nor a local-rank obstruction is assumed.

Source: Aschbacher–Smith A.2.17, printed p.39, and I.1.4; GLS3 §6.1.
-/

open Subgroup PerfectCentralCovering BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover
open OddFourClosure.DefiningPrime

public theorem prime_kernel_positive_section {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 4 F) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hcard : Nat.card F=p^2) (hconj : ∀ x, J.conj x=x^p)
    {E : Type*} [Group E] (f : E →* HyperbolicSU J)
    (hf : Function.Surjective f) (hc : f.ker ≤ center E)
    (hker : Nat.card f.ker=p) :
    ∃ s : positive J →* E, f.comp s=(positive J).subtype := by
  obtain ⟨L⟩ := equivariantRootLifts_of_prime_kernel J f hf hc hp hp3 hcard hconj hker
  exact EquivariantRootLifts.exists_positive_section_of_prime J L hp hp3 hcard hconj hf hc

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover

open Matrix Subgroup PerfectCentralCovering BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover
open OddFourClosure.DefiningPrime
open CentralExtension

public theorem not_defining_dvd_kernel {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 4 F) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hcard : Nat.card F=p^2) (hconj : ∀ x, J.conj x=x^p)
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  let : Fact p.Prime := ⟨hp⟩
  let : Finite (ProjGenLinGroup (Fin 4) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  apply f.not_dvd_card_kernel_of_prime_kernel_local_sections
  intro D _ _ d hd
  obtain ⟨e⟩ := exists_hyperbolic_special_equiv J hp hcard hconj
  let g : HyperbolicSU J →* ProjectiveSpecialUnitaryMatrixGroup J :=
    (project J).comp e.toMonoidHom
  have hg : Function.Surjective g := (project_surjective J).comp e.surjective
  have hkg : Nat.card g.ker=Nat.gcd 4 (p+1) := by
    rw [Nat.card_congr (Theory.GroupTheory.Covering.kerMulEquivOfSquare g
      (project J) e (MulEquiv.refl _) (fun _ => rfl)).toEquiv]
    exact card_project_kernel J hconj hcard
  have hcop : Nat.Coprime p (Nat.card g.ker) := by
    rw [hkg]
    apply (hp.coprime_iff_not_dvd).mpr
    intro hh
    have hd4 : p ∣ 2^2 := hh.trans (Nat.gcd_dvd_left 4 (p+1))
    have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd4)
    omega
  let u := pullbackRight d.toMonoidHom g
  have hu : Function.Surjective u := pullbackRight_surjective _ _ d.surjective
  have hc : u.ker ≤ center (pullback d.toMonoidHom g) :=
    pullbackRight_central _ _ d.ker_le_center
  have hku : Nat.card u.ker=p := by
    rw [Nat.card_congr (pullbackKernelEquiv d.toMonoidHom g).toEquiv]
    exact hd
  obtain ⟨s,hs⟩ := prime_kernel_positive_section J hp hp3 hcard hconj u hu hc hku
  have hinj : Function.Injective (g.comp (positive J).subtype) :=
    injective_comp_subtype_of_coprime_ker g hcop (positive J)
      (positiveSylow J hp hcard hconj).isPGroup'
  obtain ⟨t,ht⟩ := exists_section_on_image_of_pullback d.toMonoidHom g (positive J) hinj s hs
  refine ⟨(positive J).map g,t,?_,ht⟩
  exact fun hh => not_dvd_positive_index J hp hcard hconj
    (hh.trans ((positive J).index_map_dvd hg))

public theorem not_nondefining_dvd_kernel {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 4 F) {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : r.Prime) (hr2 : r ≠ 2) (hrp : r ≠ p)
    (hcard : Nat.card F=p^2) (hconj : ∀ x, J.conj x=x^p)
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact r.Prime := ⟨hr⟩
  by_cases hd : r ∣ p^2-1
  · exact Nondefining.unitary_not_dvd_kernel_of_dvd_sq_sub_one J hcard hconj hp2 hr2 hrp hd f
  · exact Nondefining.unitary_not_dvd_kernel_of_not_dvd_sq_sub_one J hcard hconj hr2 hrp hd f

public theorem injective_of_odd_kernel {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 4 F) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hcard : Nat.card F=p^2) (hconj : ∀ x, J.conj x=x^p)
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J))
    (ho : Odd (Nat.card f.toMonoidHom.ker)) :
    Function.Injective f.toMonoidHom := by
  apply f.toMonoidHom.ker_eq_bot_iff.mp
  apply Subgroup.eq_bot_of_card_eq
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro r hr hd
  by_cases hrp : r=p
  · exact not_defining_dvd_kernel J hp hp3 hcard hconj f (hrp ▸ hd)
  have hr2 : r ≠ 2 := fun he => ho.not_two_dvd_nat (he ▸ hd)
  exact not_nondefining_dvd_kernel J hp (by omega) hr hr2 hrp hcard hconj f hd

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover

open Subgroup PerfectCentralCovering BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover

public theorem kernel_isPGroup_of_odd {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 4 F) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : Nat.card F=p^2) (hconj : ∀ x, J.conj x=x^p)
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J))
    (ho : Odd (Nat.card f.toMonoidHom.ker)) :
    IsPGroup p f.toMonoidHom.ker := by
  apply (isPGroup_iff_primeFactors_card_subset hp.ne_zero).mpr
  intro r hr
  obtain ⟨hr,hd,_⟩ := Nat.mem_primeFactors.mp hr
  have hrp : r=p := by
    by_contra hne
    have hr2 : r ≠ 2 := fun he => ho.not_two_dvd_nat (he ▸ hd)
    exact not_nondefining_dvd_kernel J hp hp2 hr hr2 hne hcard hconj f hd
  subst r
  exact Nat.mem_primeFactors.mpr ⟨hp,dvd_rfl,hp.ne_zero⟩

public theorem kernel_isTwoGroup {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 4 F) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hcard : Nat.card F=p^2) (hconj : ∀ x, J.conj x=x^p)
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    IsPGroup 2 f.toMonoidHom.ker := by
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro r hr
  obtain ⟨hr,hd,_⟩ := Nat.mem_primeFactors.mp hr
  have hr2 : r=2 := by
    by_contra hne
    by_cases hrp : r=p
    · exact not_defining_dvd_kernel J hp hp3 hcard hconj f (hrp ▸ hd)
    · exact not_nondefining_dvd_kernel J hp (by omega) hr hne hrp hcard hconj f hd
  subst r
  exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two,dvd_rfl,by decide⟩

public theorem center_isTwoGroup_of_quotient_equiv {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 4 F) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hcard : Nat.card F=p^2) (hconj : ∀ x, J.conj x=x^p)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (e : E ⧸ center E ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    IsPGroup 2 (center E) := by
  have hh := kernel_isTwoGroup J hp hp3 hcard hconj (centralQuotientCover e)
  change IsPGroup 2 (centralQuotientCover e).toMonoidHom.ker at hh
  rwa [centralQuotientCover_ker] at hh

public theorem center_eq_bot_of_quotient_equiv {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 4 F) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hcard : Nat.card F=p^2) (hconj : ∀ x, J.conj x=x^p)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (e : E ⧸ center E ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (ho : Odd (Nat.card (center E))) : center E=⊥ := by
  rw [← centralQuotientCover_ker e]
  exact (MonoidHom.ker_eq_bot_iff _).mpr (injective_of_odd_kernel J hp hp3 hcard hconj
    (centralQuotientCover e) (by simpa only [centralQuotientCover_ker] using ho))

public theorem center_isThreeGroup_of_card_nine {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 4 F) (hcard : Nat.card F=9)
    (hconj : ∀ x, J.conj x=x^3)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (e : E ⧸ center E ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (ho : Odd (Nat.card (center E))) : IsPGroup 3 (center E) := by
  have hh := kernel_isPGroup_of_odd J Nat.prime_three (by decide) hcard hconj
      (centralQuotientCover e) (by simpa only [centralQuotientCover_ker] using ho)
  change IsPGroup 3 (centralQuotientCover e).toMonoidHom.ker at hh
  rwa [centralQuotientCover_ker] at hh

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover
