module

public import Theory.GroupTheory.ZStar.LocalSectionCharacter
public import Theory.Character.ModularBlock.CompatibleCongruence
public import Theory.Character.ModularBlock.PrincipalKernel

/-!
# Local principal-block core support and section invariance

The section of an ambient character at `z` has a canonical complete local
irreducible expansion. The exact modular support condition says that the part
outside the local principal block vanishes on the local odd core. Removing
that vanishing part gives a principal-block expansion there. Every local
principal-block character kills the local odd core, so the expansion is
constant on it, proving the required section identity.

The canonical local datum uses the ambient root's canonical power and the
contraction of the same ambient prime ideal. Support is proved here for the
distinguished principal character and converted to section invariance in
general; no unconditional support for arbitrary block members is assumed.
That remaining modular theorem is supplied by CharacterwiseSupport.

This is the support and assembly portion of historical
`Submission/ZStar/LocalBlockSection.lean` at commit `c3503435`. The ordinary
integer expansion is a lower prerequisite. Alternate solvable kernel witnesses
are re-exported only by the historical Glauberman module.
Definitions of the support predicates and compatible local data are exposed
because projection and Brauer-compatibility proofs use their exact meaning.
-/

public section

noncomputable section
open scoped BigOperators
namespace Glauberman.ZStar.LocalBlockSection
open ModularBlock ModularBlock.PrincipalBlockConstruction BenderSuzuki.PFAppendixIII
universe u
attribute [local instance] Fintype.ofFinite
variable {G : Type u} [Group G] [Finite G]

/-- A principal-local-block expansion of the `z`-section of an ambient
character on the local odd core.  This is the only part of the ordinary-
character reformulation of the specialized second main theorem on blocks
needed here.  It combines Feit III.4.11, III.7.5, III.9.4 and IV.6.1 with
the full-rank decomposition-matrix statement in IV.6.6. -/
structure LocalPrincipalBlockExpansion
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G) where
  localData :
    PrincipalCongruenceBlockData (Subgroup.centralizer ({z} : Set G))
  coeff : localData.I → ℂ
  expand : ∀ x : Subgroup.centralizer ({z} : Set G),
    x ∈ pPrimeCore 2 (Subgroup.centralizer ({z} : Set G)) →
    d.chi i (ConjClasses.mk (z * (x : G))) =
      ∑ j ∈ localData.block,
        coeff j * localData.chi j (ConjClasses.mk x)

/-- The exact local support statement left by the ordinary character
expansion: the non-principal-block part vanishes on the local odd core.

This is a proposition specifying the expansion support. Feit III.4.11,
Nagao III.7.5, and Brauer correspondence III.9.4 give the local block
support through IV.6.1; the blockwise decomposition-matrix result IV.6.6
identifies it with the ordinary-character statement below. -/
@[expose] def LocalPrincipalBlockCoreSupport
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G)
    (e : PrincipalCongruenceBlockData
      (Subgroup.centralizer ({z} : Set G))) : Prop :=
  ∀ x : Subgroup.centralizer ({z} : Set G),
    x ∈ pPrimeCore 2 (Subgroup.centralizer ({z} : Set G)) →
      ∑ j ∈ (Finset.univ \ e.block),
        classFunctionInner
            (localSectionClassFunction d i z) (e.chi j) *
          e.chi j (ConjClasses.mk x) = 0

/-- A fixed constructed principal congruence block for the involution
centralizer.  Its existence is already unconditional.  This legacy choice is
kept for statements which do not need compatibility with an ambient modular
place; the canonical support predicate below uses the compatible datum. -/
@[expose] noncomputable def localPrincipalCongruenceBlockData (z : G) :
    PrincipalCongruenceBlockData
      (Subgroup.centralizer ({z} : Set G)) :=
  Classical.choice (exists_principalCongruenceBlockData
    (Subgroup.centralizer ({z} : Set G)))

/-- The local principal congruence-block datum formed using the canonical
power of the ambient root and contraction of the ambient prime. -/
noncomputable abbrev compatibleCentralizerPrincipalCongruenceBlockData
    (d : PrincipalCongruenceBlockData G) (z : G) :
    PrincipalCongruenceBlockData
      (Subgroup.centralizer ({z} : Set G)) :=
  CompatibleLocalBlock.compatibleSubgroupPrincipalCongruenceBlockData d
    (Subgroup.centralizer ({z} : Set G))

/-- The single canonical support proposition left to prove by the specialized
second main theorem on blocks.  The local datum is taken over the contraction
of the ambient modular place, so its block idempotent can be compared directly
with the Brauer image of the ambient principal-block idempotent. -/
@[expose] def CanonicalLocalPrincipalBlockCoreSupport
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G) : Prop :=
  LocalPrincipalBlockCoreSupport d i z
    (compatibleCentralizerPrincipalCongruenceBlockData d z)

/-- Local support is unconditional for the distinguished ambient principal
character, for any choice of local principal congruence-block data.  Its
local section is the local principal character itself, so orthogonality makes
every coefficient outside the local principal block vanish identically. -/
theorem localPrincipalBlockCoreSupport_principal
    (d : PrincipalCongruenceBlockData G) (z : G)
    (e : PrincipalCongruenceBlockData
      (Subgroup.centralizer ({z} : Set G))) :
    LocalPrincipalBlockCoreSupport d d.principal z e := by
  classical
  have hsection :
      localSectionClassFunction d d.principal z = e.chi e.principal := by
    ext C
    rcases ConjClasses.exists_rep C with ⟨x, rfl⟩
    rw [localSectionClassFunction_mk, d.principal_eq, e.principal_eq]
    simp
  rcases completeFamily_form_basis e.complete with ⟨b, hb⟩
  intro x _hx
  apply Finset.sum_eq_zero
  intro j hj
  have hj_not_block : j ∉ e.block := (Finset.mem_sdiff.mp hj).2
  have hj_ne : e.principal ≠ j := by
    intro h
    apply hj_not_block
    rw [← h]
    exact e.principal_mem
  have hinner :
      classFunctionInner
          (localSectionClassFunction d d.principal z) (e.chi j) = 0 := by
    rw [hsection]
    rw [← completeFamily_basis_repr_eq_inner
      e.complete b hb (e.chi e.principal) j]
    rw [← hb e.principal, b.repr_self_apply]
    simp [hj_ne]
  rw [hinner, zero_mul]

/-- Canonical-data specialization of
`localPrincipalBlockCoreSupport_principal`. -/
theorem canonicalLocalPrincipalBlockCoreSupport_principal
    (d : PrincipalCongruenceBlockData G) (z : G) :
    CanonicalLocalPrincipalBlockCoreSupport d d.principal z :=
  localPrincipalBlockCoreSupport_principal d z
    (compatibleCentralizerPrincipalCongruenceBlockData d z)

/-- Core support yields the weighted local principal-block expansion used by
the section calculation. -/
@[expose] noncomputable def localPrincipalBlockExpansion_of_coreSupport
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G)
    (e : PrincipalCongruenceBlockData
      (Subgroup.centralizer ({z} : Set G)))
    (hsupport : LocalPrincipalBlockCoreSupport d i z e) :
    LocalPrincipalBlockExpansion d i z := by
  let a : e.I → ℂ := fun j =>
    classFunctionInner
      (localSectionClassFunction d i z) (e.chi j)
  refine {
    localData := e
    coeff := a
    expand := ?_ }
  intro x hx
  rw [localSection_eq_sum_all_irreducibles d i z e x]
  have hsplit := Finset.sum_sdiff (e.block.subset_univ)
    (f := fun j : e.I => a j * e.chi j (ConjClasses.mk x))
  rw [← hsplit]
  change
    (∑ j ∈ Finset.univ \ e.block,
      classFunctionInner
          (localSectionClassFunction d i z) (e.chi j) *
        e.chi j (ConjClasses.mk x)) + _ = _
  rw [hsupport x hx, zero_add]

/-- The completed odd-core kernel theorem turns a local principal-block
expansion into section invariance.  Thus the only remaining local theorem is
the existence of the expansion itself. -/
theorem section_invariance_of_localPrincipalBlockExpansion
    (d : PrincipalCongruenceBlockData G) {i : d.I} {z v : G}
    (hlocal : LocalPrincipalBlockExpansion d i z)
    (hv : v ∈
      (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype) :
    d.chi i (ConjClasses.mk (z * v)) = d.chi i (ConjClasses.mk z) := by
  rcases Subgroup.mem_map.mp hv with ⟨vC, hvC, rfl⟩
  change d.chi i (ConjClasses.mk (z * (vC : G))) = _
  rw [hlocal.expand vC hvC]
  have hone :
      d.chi i (ConjClasses.mk z) =
        ∑ j ∈ hlocal.localData.block,
          hlocal.coeff j *
            hlocal.localData.chi j
              (ConjClasses.mk
                (1 : Subgroup.centralizer ({z} : Set G))) := by
    simpa using hlocal.expand
      (1 : Subgroup.centralizer ({z} : Set G)) (pPrimeCore 2 _).one_mem
  rw [hone]
  simpa using PrincipalBlockKernel.weighted_block_sum_mul_right_eq
    hlocal.localData hlocal.coeff
      (1 : Subgroup.centralizer ({z} : Set G)) vC hvC

/-- The target section identity follows from the exact local core-support
statement, with no separately supplied coefficients. -/
theorem section_invariance_of_localPrincipalBlockCoreSupport
    (d : PrincipalCongruenceBlockData G) {i : d.I} {z v : G}
    (e : PrincipalCongruenceBlockData
      (Subgroup.centralizer ({z} : Set G)))
    (hsupport : LocalPrincipalBlockCoreSupport d i z e)
    (hv : v ∈
      (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype) :
    d.chi i (ConjClasses.mk (z * v)) = d.chi i (ConjClasses.mk z) := by
  exact section_invariance_of_localPrincipalBlockExpansion d
    (localPrincipalBlockExpansion_of_coreSupport d i z e hsupport) hv

/-- Canonical-support form of the target section identity. -/
theorem section_invariance_of_canonicalLocalPrincipalBlockCoreSupport
    (d : PrincipalCongruenceBlockData G) {i : d.I} {z v : G}
    (hsupport : CanonicalLocalPrincipalBlockCoreSupport d i z)
    (hv : v ∈
      (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype) :
    d.chi i (ConjClasses.mk (z * v)) = d.chi i (ConjClasses.mk z) := by
  exact section_invariance_of_localPrincipalBlockCoreSupport d
    (compatibleCentralizerPrincipalCongruenceBlockData d z) hsupport hv

/-- A family of local principal-block expansions supplies the section identity
required by `PrincipalCongruenceBlockData.toPrincipalTwoBlockData`.

The existence of this family is exactly the remaining specialized second
main theorem on blocks. -/
theorem principalBlock_section_invariance_of_localPrincipalBlockExpansions
    (d : PrincipalCongruenceBlockData G)
    (hlocal : ∀ i ∈ d.block, ∀ z : G, IsInvolution z →
      LocalPrincipalBlockExpansion d i z) :
    ∀ i ∈ d.block, ∀ z : G, IsInvolution z → ∀ v : G,
      v ∈ (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype →
      d.chi i (ConjClasses.mk (z * v)) = d.chi i (ConjClasses.mk z) := by
  intro i hi z hzI v hv
  exact section_invariance_of_localPrincipalBlockExpansion
    d (hlocal i hi z hzI) hv

/-- A uniform version phrased only in terms of the exact local support
statement supplied by the specialized second main theorem on blocks. -/
theorem principalBlock_section_invariance_of_localPrincipalBlockCoreSupports
    (d : PrincipalCongruenceBlockData G)
    (hsupport : ∀ i ∈ d.block, ∀ z : G, IsInvolution z →
      ∃ e : PrincipalCongruenceBlockData
          (Subgroup.centralizer ({z} : Set G)),
        LocalPrincipalBlockCoreSupport d i z e) :
    ∀ i ∈ d.block, ∀ z : G, IsInvolution z → ∀ v : G,
      v ∈ (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype →
      d.chi i (ConjClasses.mk (z * v)) = d.chi i (ConjClasses.mk z) := by
  intro i hi z hzI v hv
  rcases hsupport i hi z hzI with ⟨e, he⟩
  exact section_invariance_of_localPrincipalBlockCoreSupport d e he hv

/-- The exact uniform remaining theorem, stated using the already constructed
canonical local congruence blocks. -/
theorem principalBlock_section_invariance_of_canonicalLocalPrincipalBlockCoreSupport
    (d : PrincipalCongruenceBlockData G)
    (hsupport : ∀ i ∈ d.block, ∀ z : G, IsInvolution z →
      CanonicalLocalPrincipalBlockCoreSupport d i z) :
    ∀ i ∈ d.block, ∀ z : G, IsInvolution z → ∀ v : G,
      v ∈ (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype →
      d.chi i (ConjClasses.mk (z * v)) = d.chi i (ConjClasses.mk z) := by
  intro i hi z hzI v hv
  exact section_invariance_of_canonicalLocalPrincipalBlockCoreSupport d
    (hsupport i hi z hzI) hv


end Glauberman.ZStar.LocalBlockSection
