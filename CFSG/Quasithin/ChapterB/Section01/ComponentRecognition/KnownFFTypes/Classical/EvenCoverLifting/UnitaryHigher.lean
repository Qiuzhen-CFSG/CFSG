module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.EvenCoverLifting.Descent
public import Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel
public import Theory.GroupTheory.CoveringComparisonKernelCard
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Higher unitary coverings from multiplier bounds

The given central-quotient isomorphism supplies quasisimplicity of the actual
projective unitary matrix group. The canonical SU-to-PSU projection has the
proved kernel order `gcd(n,q+1)`. A universal-kernel bound dividing a power of
two times that order therefore makes the comparison to SU have two-group
kernel. Descent through `O₂(L)=1` produces a central quotient of the original
SU group, preserving the field, dimension, Hermitian form and conjugation.

For PSU₆(2), the scalar kernel has order three. The bound twelve allows the
exceptional two-primary kernel and still gives the required descent; no
universality of ordinary SU₆(2) is asserted.

The finite multiplier bounds and perfectness of the concrete SU group remain
explicit prerequisites. These are conditional assembly results, not completed
higher-unitary covering calculations. Source: Aschbacher–Smith, B.1.13,
printed pp.73–74; GLS3, Section 6.1, Theorems 6.1.2 and 6.1.4 and
Corollary 6.1.5. The ordinary range here is n ≥ 5 excluding (5,4) and (6,2);
the latter exceptional case is handled by the separate twelve-bound adapter.
-/

public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open PerfectCentralCovering
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.UnitaryHigher
universe u
variable {L : Type u} [Group L] [Finite L] [IsQuasisimple L]
open Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel

omit [Finite L] in
/-- Model quasisimplicity comes from the actual source component quotient. -/
theorem projective_isQuasisimple {n : ℕ} {F : Type} [Field F]
    (J : HermitianForm n F) (e : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.symm.isSimpleGroup
  exact IsQuasisimple.of_surjective
    (e.toMonoidHom.comp (QuotientGroup.mk' (center L)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))

/-- The literal SU-to-PSU projection as a perfect central cover, once SU
perfectness has been proved. -/
@[expose] def specialCover {n : ℕ} {F : Type} [Field F] (J : HermitianForm n F)
    [Group.IsPerfect J.specialSubgroup] :
    PerfectCentralCovering.Cover J.specialSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) where
  toMonoidHom := project J
  surjective := project_surjective J
  isPerfect := inferInstance
  ker_le_center := project_kernel_le_center J

/-- A prime-to-two canonical multiplier bound yields a central quotient of
the same SU group after the exceptional two-group kernel is killed. -/
theorem isCentralQuotient_of_multiplier_bound (hcore : pCore 2 L = ⊥)
    {n q : ℕ} (hn : 0 < n) (F : Type) [Field F] [Finite F]
    (J : HermitianForm n F) (hcard : Nat.card F = q ^ 2)
    (hconj : ∀ x, J.conj x = x ^ q)
    (hperfect : Group.IsPerfect J.specialSubgroup)
    (e : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    {r : ℕ} (hbound : Nat.card (universalProjection
      (ProjectiveSpecialUnitaryMatrixGroup J)).ker ∣ 2 ^ r * Nat.gcd n (q + 1)) :
    IsCentralQuotient L J.specialSubgroup := by
  let : NeZero n := ⟨hn.ne'⟩
  let : Group.IsPerfect J.specialSubgroup := hperfect
  let : IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J) := projective_isQuasisimple J e
  let : IsQuasisimple J.specialSubgroup := (specialCover J).isQuasisimple
  let f := (specialCover J).toCovering
  let c := universalQuasisimpleCover (ProjectiveSpecialUnitaryMatrixGroup J)
  have hc : Covering.IsUniversal.{0,0,u} c := universalQuasisimpleCover_isUniversal _
  have hc₀ : Covering.IsUniversal.{0,0,0} c := universalQuasisimpleCover_isUniversal _
  let a := hc₀.lift f
  have hfac : f.comp a = c := hc₀.lift_fac f
  have hcard' : Nat.card c.toMonoidHom.ker ∣ 2 ^ r * Nat.card f.toMonoidHom.ker := by
    change Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker ∣
      2 ^ r * Nat.card (project J).ker
    rw [card_project_kernel J hconj hcard]
    exact hbound
  let g : Covering L (ProjectiveSpecialUnitaryMatrixGroup J) :=
    { toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
      surjective := e.surjective.comp (QuotientGroup.mk'_surjective _) }
  obtain ⟨k, _⟩ := hc.exists_covering_of_kernel_card_dvd a f hfac hcard' g hcore
  exact isCentralQuotient_of_covering k

/-- The actual even-Lie consumer retains all the supplied unitary data. -/
theorem isEvenLieGroup_of_multiplier_bound (hcore : pCore 2 L = ⊥)
    {n q : ℕ} (hp : KnownSimple.UnitaryParameters n q) (he : Even q)
    (F : Type) [Field F] [Finite F] (J : HermitianForm n F)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    (hperfect : Group.IsPerfect J.specialSubgroup)
    (e : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    {r : ℕ} (hbound : Nat.card (universalProjection
      (ProjectiveSpecialUnitaryMatrixGroup J)).ker ∣ 2 ^ r * Nat.gcd n (q + 1)) :
    IsEvenLieGroup L :=
  .classical (.unitary n q hp he F J hcard hconj
    (isCentralQuotient_of_multiplier_bound hcore (by have := hp.2.1; omega)
      F J hcard hconj hperfect e hbound))

/-- The actual SU₆(2)-to-PSU₆(2) scalar kernel has order three. -/
theorem six_two_project_kernel_card
    (F : Type) [Field F] [Finite F] (J : HermitianForm 6 F)
    (hcard : Nat.card F = 4) (hconj : ∀ x, J.conj x = x ^ 2) :
    Nat.card (project J).ker = 3 := by
  simpa using card_project_kernel J hconj (show Nat.card F = 2 ^ 2 by simpa using hcard)

/-- The exceptional multiplier bound twelve suffices, because the comparison
kernel has order dividing four and its image lies in the trivial two-core. -/
theorem isCentralQuotient_six_two_of_multiplier_bound (hcore : pCore 2 L = ⊥)
    (F : Type) [Field F] [Finite F] (J : HermitianForm 6 F)
    (hcard : Nat.card F = 4) (hconj : ∀ x, J.conj x = x ^ 2)
    (hperfect : Group.IsPerfect J.specialSubgroup)
    (e : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hbound : Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker ∣ 12) :
    IsCentralQuotient L J.specialSubgroup :=
  isCentralQuotient_of_multiplier_bound hcore (by decide) F J
    (by simpa using hcard) hconj hperfect e (r := 2) (by simpa using hbound)

/-- PSU₆(2) feeds the even-Lie conclusion through actual two-primary descent. -/
theorem isEvenLieGroup_six_two_of_multiplier_bound (hcore : pCore 2 L = ⊥)
    (F : Type) [Field F] [Finite F] (J : HermitianForm 6 F)
    (hcard : Nat.card F = 4) (hconj : ∀ x, J.conj x = x ^ 2)
    (hperfect : Group.IsPerfect J.specialSubgroup)
    (e : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hbound : Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker ∣ 12) :
    IsEvenLieGroup L := by
  have hp : KnownSimple.UnitaryParameters 6 2 := by
    exact ⟨Nat.prime_two.isPrimePow, by omega, by omega, by omega⟩
  exact .classical (.unitary 6 2 hp (by decide) F J (by simpa using hcard) hconj
    (isCentralQuotient_six_two_of_multiplier_bound hcore F J hcard hconj hperfect e hbound))

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.UnitaryHigher
