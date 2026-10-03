module

public import Theory.GroupTheory.ZStar.LocalBlockSection

/-!
# Canonical local core support as a projection identity

Completeness splits a local class function into its orthogonal projections
onto the chosen principal block and its complement. The local core-support
condition is equivalent to the complementary projection vanishing on the
local odd core, hence to the principal projection fixing the section there.
Specializing to the compatible local congruence datum gives the canonical
Brauer-section compatibility interface used by the modular assembly.

No support statement is assumed or proved unconditionally here: this is the
exact equivalence between two formulations of that remaining modular input.
It is ported from historical `Submission/ZStar/CanonicalLocalCoreSupportScratch.lean`
at commit `c3503435`. The projection and compatibility definitions are exposed
because subsequent projection and support proofs use their finite-sum meaning.
-/

public section

noncomputable section

open scoped BigOperators

namespace Glauberman.ZStar

namespace LocalBlockSection

open ModularBlock.PrincipalBlockConstruction

universe u

attribute [local instance] Fintype.ofFinite

variable {G : Type u} [Group G] [Finite G]

/-- Orthogonal projection of a local class function onto the ordinary
irreducible characters in the chosen principal congruence block. -/
@[expose] noncomputable def localPrincipalBlockProjection
    {H : Type*} [Group H] [Finite H]
    (e : PrincipalCongruenceBlockData H)
    (f : ConjClassFunction H) :
    ConjClassFunction H :=
  ∑ j ∈ e.block,
    classFunctionInner f (e.chi j) • e.chi j

/-- The complementary projection onto irreducibles outside the chosen local
principal block. -/
@[expose] noncomputable def localOutsideBlockProjection
    {H : Type*} [Group H] [Finite H]
    (e : PrincipalCongruenceBlockData H)
    (f : ConjClassFunction H) :
    ConjClassFunction H :=
  ∑ j ∈ (Finset.univ \ e.block),
    classFunctionInner f (e.chi j) • e.chi j

@[simp] theorem localPrincipalBlockProjection_apply
    {H : Type*} [Group H] [Finite H]
    (e : PrincipalCongruenceBlockData H)
    (f : ConjClassFunction H) (C : ConjClasses H) :
    localPrincipalBlockProjection e f C =
      ∑ j ∈ e.block,
        classFunctionInner f (e.chi j) * e.chi j C := by
  simp [localPrincipalBlockProjection]

@[simp] theorem localOutsideBlockProjection_apply
    {H : Type*} [Group H] [Finite H]
    (e : PrincipalCongruenceBlockData H)
    (f : ConjClassFunction H) (C : ConjClasses H) :
    localOutsideBlockProjection e f C =
      ∑ j ∈ (Finset.univ \ e.block),
        classFunctionInner f (e.chi j) * e.chi j C := by
  simp [localOutsideBlockProjection]

/-- Completeness splits every local class function into its principal-block
and outside-block orthogonal projections. -/
theorem localPrincipalBlockProjection_add_outside
    {H : Type*} [Group H] [Finite H]
    (e : PrincipalCongruenceBlockData H)
    (f : ConjClassFunction H) :
    localPrincipalBlockProjection e f + localOutsideBlockProjection e f = f := by
  ext C
  change localPrincipalBlockProjection e f C +
    localOutsideBlockProjection e f C = f C
  rw [localPrincipalBlockProjection_apply,
    localOutsideBlockProjection_apply]
  have hall := completeFamily_apply_eq_sum_inner
    e.complete f C
  rw [hall]
  have hsplit := Finset.sum_sdiff (e.block.subset_univ)
    (f := fun j : e.I =>
      classFunctionInner f (e.chi j) * e.chi j C)
  rw [← hsplit]
  ac_rfl

/-- The support target is precisely fixedness of the local section under the
local principal-block projector on the local odd core. -/
theorem localPrincipalBlockCoreSupport_iff_projection_fixed
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G)
    (e : PrincipalCongruenceBlockData
      (Subgroup.centralizer ({z} : Set G))) :
    LocalPrincipalBlockCoreSupport d i z e ↔
      ∀ x : Subgroup.centralizer ({z} : Set G),
        x ∈ pPrimeCore 2 (Subgroup.centralizer ({z} : Set G)) →
          localPrincipalBlockProjection e (localSectionClassFunction d i z)
              (ConjClasses.mk x) =
            localSectionClassFunction d i z (ConjClasses.mk x) := by
  constructor
  · intro hsupport x hx
    have houtside :
        localOutsideBlockProjection e (localSectionClassFunction d i z)
            (ConjClasses.mk x) = 0 := by
      simpa only [localOutsideBlockProjection_apply] using hsupport x hx
    have hsplit := congrArg
      (fun f : ConjClassFunction
          (Subgroup.centralizer ({z} : Set G)) => f (ConjClasses.mk x))
      (localPrincipalBlockProjection_add_outside e
        (localSectionClassFunction d i z))
    change
      localPrincipalBlockProjection e (localSectionClassFunction d i z)
          (ConjClasses.mk x) +
        localOutsideBlockProjection e (localSectionClassFunction d i z)
          (ConjClasses.mk x) =
        localSectionClassFunction d i z (ConjClasses.mk x) at hsplit
    rw [houtside, add_zero] at hsplit
    exact hsplit
  · intro hfixed x hx
    have hsplit := congrArg
      (fun f : ConjClassFunction
          (Subgroup.centralizer ({z} : Set G)) => f (ConjClasses.mk x))
      (localPrincipalBlockProjection_add_outside e
        (localSectionClassFunction d i z))
    change
      localPrincipalBlockProjection e (localSectionClassFunction d i z)
          (ConjClasses.mk x) +
        localOutsideBlockProjection e (localSectionClassFunction d i z)
          (ConjClasses.mk x) =
        localSectionClassFunction d i z (ConjClasses.mk x) at hsplit
    have hfixed' := hfixed x hx
    have houtside :
        localOutsideBlockProjection e (localSectionClassFunction d i z)
            (ConjClasses.mk x) = 0 := by
      rw [hfixed'] at hsplit
      apply add_left_cancel
      exact hsplit.trans (add_zero _).symm
    simpa only [localOutsideBlockProjection_apply] using houtside

/-- Canonical-data version of the exact Brauer-section compatibility theorem
still needed from the second main theorem on blocks. -/
@[expose] def CanonicalBrauerSectionCompatibility
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G) : Prop :=
  ∀ x : Subgroup.centralizer ({z} : Set G),
    x ∈ pPrimeCore 2 (Subgroup.centralizer ({z} : Set G)) →
      localPrincipalBlockProjection
          (compatibleCentralizerPrincipalCongruenceBlockData d z)
          (localSectionClassFunction d i z) (ConjClasses.mk x) =
        localSectionClassFunction d i z (ConjClasses.mk x)

theorem canonicalLocalPrincipalBlockCoreSupport_iff_brauerCompatibility
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G) :
    CanonicalLocalPrincipalBlockCoreSupport d i z ↔
      CanonicalBrauerSectionCompatibility d i z := by
  exact localPrincipalBlockCoreSupport_iff_projection_fixed d i z
    (compatibleCentralizerPrincipalCongruenceBlockData d z)

end LocalBlockSection

end Glauberman.ZStar


