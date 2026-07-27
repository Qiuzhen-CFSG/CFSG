import Submission.FeitThompson.PCore.CentralizerControl
import Submission.ZStar.CompatibleLocalBlock
import Submission.ZStar.PrincipalBlockKernel
import Submission.ZStar.CentralIdempotentSupport

/-!
# Local principal-block section invariance

This file records the part of the local section argument that follows from
the already formalized principal-block odd-core kernel theorem.

For a general finite group, Feit III.4.11, III.7.5, and III.9.4 show that the
restriction of an ambient principal-block section to odd-order elements is
supported on the principal block of the involution centralizer.  The predicate
`LocalPrincipalBlockCoreSupport` isolates exactly that support statement.
Ordinary character completeness then supplies canonical coefficients, while
Feit IV.4.12(ii), already formalized in `PrincipalBlockKernel`, makes every
local principal-block summand constant on the local odd core.

The same conclusion is already unconditional when the local odd core maps
into the global odd core.  In particular this holds for solvable ambient
groups by the existing centralizer-control theorem.
-/

noncomputable section

namespace Submission.ZStar

namespace LocalBlockSection

open PrincipalBlockConstruction

universe u

attribute [local instance] Fintype.ofFinite

variable {G : Type u} [Group G] [Finite G]

/-- Regard an element as an element of its own centralizer. -/
def selfInCentralizer (z : G) :
    Subgroup.centralizer ({z} : Set G) :=
  ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

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

/-! The following canonical expansion separates the elementary character
linear algebra from the genuinely modular support assertion. -/

noncomputable def localSectionClassFunction
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G) :
    Representation.ClassFunction (Subgroup.centralizer ({z} : Set G)) :=
  Representation.classFunctionOfInvariant
    (fun x : Subgroup.centralizer ({z} : Set G) =>
      d.chi i (ConjClasses.mk (z * (x : G)))) (by
        intro x h
        apply congrArg (d.chi i)
        apply Eq.symm
        apply ConjClasses.mk_eq_mk_iff_isConj.mpr
        apply isConj_iff.mpr
        refine ⟨(h : G), ?_⟩
        have hh : (h : G) * z = z * (h : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp h.2
        change (h : G) * (z * (x : G)) * (h : G)⁻¹ =
          z * (((h * x * h⁻¹ :
            Subgroup.centralizer ({z} : Set G))) : G)
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        calc
          (h : G) * (z * (x : G)) * (h : G)⁻¹ =
              ((h : G) * z) * (x : G) * (h : G)⁻¹ := by
                simp only [mul_assoc]
          _ = (z * (h : G)) * (x : G) * (h : G)⁻¹ := by rw [hh]
          _ = z * ((h : G) * (x : G) * (h : G)⁻¹) := by
                simp only [mul_assoc])

@[simp] theorem localSectionClassFunction_mk
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G)
    (x : Subgroup.centralizer ({z} : Set G)) :
    localSectionClassFunction d i z (ConjClasses.mk x) =
      d.chi i (ConjClasses.mk (z * (x : G))) := rfl

/-! The involution section is already an ordinary virtual character.  This
is the characteristic-zero eigenspace part of the higher-decomposition-number
construction; the remaining modular theorem is the support of this virtual
character on the local principal block. -/

private def rangeSubrepresentation
    {H V : Type*} [Group H] [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ H V) (p : Module.End ℂ V)
    (hcomm : ∀ h : H, p * rho h = rho h * p) : Subrepresentation rho where
  toSubmodule := LinearMap.range p
  apply_mem_toSubmodule h := by
    rintro _ ⟨v, rfl⟩
    refine ⟨rho h v, ?_⟩
    exact LinearMap.congr_fun (hcomm h) v

private theorem half_one_add_idempotent
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) (hf : f * f = 1) :
    IsIdempotentElem ((2 : ℂ)⁻¹ • (1 + f) : Module.End ℂ V) := by
  change (((2 : ℂ)⁻¹ • (1 + f)) * ((2 : ℂ)⁻¹ • (1 + f)) :
      Module.End ℂ V) = (2 : ℂ)⁻¹ • (1 + f)
  ext v
  have hfv : f (f v) = v := by
    simpa using LinearMap.congr_fun hf v
  simp [hfv]
  module

private theorem half_one_sub_idempotent
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) (hf : f * f = 1) :
    IsIdempotentElem ((2 : ℂ)⁻¹ • (1 - f) : Module.End ℂ V) := by
  change (((2 : ℂ)⁻¹ • (1 - f)) * ((2 : ℂ)⁻¹ • (1 - f)) :
      Module.End ℂ V) = (2 : ℂ)⁻¹ • (1 - f)
  ext v
  have hfv : f (f v) = v := by
    simpa using LinearMap.congr_fun hf v
  simp [hfv]
  module

/-- The section of an ordinary character at an element of square one is a
virtual character of its centralizer: it is the difference of the characters
on the `+1` and `-1` eigenspaces. -/
theorem localSection_isVirtualCharacter
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G)
    (hz : z * z = 1) :
    Representation.IsVirtualCharacter
      (fun x : Subgroup.centralizer ({z} : Set G) =>
        d.chi i (ConjClasses.mk (z * (x : G)))) := by
  classical
  let C := Subgroup.centralizer ({z} : Set G)
  rcases (d.complete.1 i).1 with ⟨n, rho, hchar⟩
  let rhoC : Representation ℂ C (Fin n → ℂ) := rho.comp C.subtype
  let zC : C := selfInCentralizer z
  let f : Module.End ℂ (Fin n → ℂ) := rhoC zC
  let pPlus : Module.End ℂ (Fin n → ℂ) := (2 : ℂ)⁻¹ • (1 + f)
  let pMinus : Module.End ℂ (Fin n → ℂ) := (2 : ℂ)⁻¹ • (1 - f)
  have hf : f * f = 1 := by
    rw [← map_mul]
    change rho (z * z) = 1
    rw [hz, map_one]
  have hfcomm (x : C) : f * rhoC x = rhoC x * f := by
    rw [← map_mul, ← map_mul]
    apply congrArg rhoC
    apply Subtype.ext
    change z * (x : G) = (x : G) * z
    exact (Subgroup.mem_centralizer_singleton_iff.mp x.2).symm
  have hpPlusComm (x : C) : pPlus * rhoC x = rhoC x * pPlus := by
    dsimp [pPlus]
    noncomm_ring [hfcomm x]
  have hpMinusComm (x : C) : pMinus * rhoC x = rhoC x * pMinus := by
    dsimp [pMinus]
    noncomm_ring [hfcomm x]
  let plusSub : Subrepresentation rhoC :=
    rangeSubrepresentation rhoC pPlus hpPlusComm
  let minusSub : Subrepresentation rhoC :=
    rangeSubrepresentation rhoC pMinus hpMinusComm
  let plusRep := plusSub.toRepresentation
  let minusRep := minusSub.toRepresentation
  have hsection (x : C) :
      d.chi i (ConjClasses.mk (z * (x : G))) =
        plusRep.character x - minusRep.character x := by
    rw [hchar]
    change rho.character (z * (x : G)) = _
    rw [Representation.character, map_mul]
    change LinearMap.trace ℂ (Fin n → ℂ) (f * rhoC x) = _
    have hfp : f = pPlus - pMinus := by
      apply LinearMap.ext
      intro v
      simp [pPlus, pMinus]
      module
    have hmul : f * rhoC x = rhoC x * pPlus - rhoC x * pMinus := by
      rw [hfp, sub_mul, (hpPlusComm x).symm, (hpMinusComm x).symm]
    have hpPlus : IsIdempotentElem pPlus :=
      half_one_add_idempotent f hf
    have hpMinus : IsIdempotentElem pMinus :=
      half_one_sub_idempotent f hf
    have htracePlus :=
      CentralIdempotentSupport.trace_comp_idempotent_eq_trace_range
        pPlus (rhoC x) hpPlus (by
          simpa only [← Module.End.mul_eq_comp] using (hpPlusComm x).symm)
    have htraceMinus :=
      CentralIdempotentSupport.trace_comp_idempotent_eq_trace_range
        pMinus (rhoC x) hpMinus (by
          simpa only [← Module.End.mul_eq_comp] using (hpMinusComm x).symm)
    calc
      LinearMap.trace ℂ (Fin n → ℂ) (f * rhoC x) =
          LinearMap.trace ℂ (Fin n → ℂ)
            (rhoC x * pPlus - rhoC x * pMinus) :=
        congrArg (LinearMap.trace ℂ (Fin n → ℂ)) hmul
      _ = LinearMap.trace ℂ (Fin n → ℂ) (rhoC x * pPlus) -
          LinearMap.trace ℂ (Fin n → ℂ) (rhoC x * pMinus) := by
        rw [map_sub]
      _ = plusRep.character x - minusRep.character x := by
        have hplus :
            LinearMap.trace ℂ (Fin n → ℂ) (rhoC x * pPlus) =
              plusRep.character x := by
          rw [Module.End.mul_eq_comp]
          change LinearMap.trace ℂ (Fin n → ℂ) (rhoC x ∘ₗ pPlus) =
            LinearMap.trace ℂ (LinearMap.range pPlus) (plusRep x)
          calc
            _ = LinearMap.trace ℂ (LinearMap.range pPlus)
                ((rhoC x).restrict _) := htracePlus
            _ = _ := by
              congr 1
        have hminus :
            LinearMap.trace ℂ (Fin n → ℂ) (rhoC x * pMinus) =
              minusRep.character x := by
          rw [Module.End.mul_eq_comp]
          change LinearMap.trace ℂ (Fin n → ℂ) (rhoC x ∘ₗ pMinus) =
            LinearMap.trace ℂ (LinearMap.range pMinus) (minusRep x)
          calc
            _ = LinearMap.trace ℂ (LinearMap.range pMinus)
                ((rhoC x).restrict _) := htraceMinus
            _ = _ := by
              congr 1
        rw [hplus, hminus]
  let plusStd := Section1.standardizeRepresentation plusRep
  let minusStd := Section1.standardizeRepresentation minusRep
  let dims : Fin 2 → ℕ := Fin.cases
    (Module.finrank ℂ (LinearMap.range pPlus))
    (fun _ : Fin 1 => Module.finrank ℂ (LinearMap.range pMinus))
  let reps : (k : Fin 2) → Representation ℂ C (Fin (dims k) → ℂ) :=
    Fin.cases (motive := fun k => Representation ℂ C (Fin (dims k) → ℂ))
      plusStd (fun k => Fin.cases minusStd (fun j => Fin.elim0 j) k)
  let weights : Fin 2 → ℤ := Fin.cases 1 (fun _ : Fin 1 => -1)
  refine ⟨2, weights, dims, reps, ?_⟩
  ext x
  rw [hsection x]
  have hweights0 : weights (0 : Fin 2) = 1 := rfl
  have hweights1 : weights (1 : Fin 2) = -1 := rfl
  have hreps0 : reps (0 : Fin 2) = plusStd := rfl
  have hreps1 : reps (1 : Fin 2) = minusStd := rfl
  rw [show Representation.virtualCharacterOfRepresentations 2 weights dims reps x =
      plusStd.character x - minusStd.character x by
    rw [Representation.virtualCharacterOfRepresentations]
    rw [Fin.sum_univ_two]
    rw [hweights0, hweights1, hreps0, hreps1]
    norm_num [sub_eq_add_neg]
    rfl]
  rw [Section1.standardizeRepresentation_character,
    Section1.standardizeRepresentation_character]

/-- The canonical coefficients of an involution section against local
irreducible characters are integers. -/
theorem localSection_inner_eq_int
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G)
    (hz : z * z = 1)
    (e : PrincipalCongruenceBlockData
      (Subgroup.centralizer ({z} : Set G))) (j : e.I) :
    ∃ a : ℤ,
      Representation.classFunctionInner
          (localSectionClassFunction d i z) (e.chi j) = (a : ℂ) := by
  classical
  let C := Subgroup.centralizer ({z} : Set G)
  let phi : Section1.ClassFunction C :=
    Section1.ofConjClassFunction (localSectionClassFunction d i z)
  have hphiClass : Section1.IsClassFunction phi :=
    Section1.ofConjClassFunction_isClassFunction _
  have hphiVirt : Representation.IsVirtualCharacter phi := by
    change Representation.IsVirtualCharacter
      (fun x : C => d.chi i (ConjClasses.mk (z * (x : G))))
    simpa [C] using localSection_isVirtualCharacter d i z hz
  let psi : Section1.ClassFunction C := Section1.ofConjClassFunction (e.chi j)
  have hpsiVirt : Representation.IsVirtualCharacter psi := by
    rcases (e.complete.1 j).1 with ⟨n, rho, hchar⟩
    refine ⟨1, (fun _ : Fin 1 => (1 : ℤ)), (fun _ : Fin 1 => n),
      (fun _ : Fin 1 => rho), ?_⟩
    ext x
    rw [show psi x = rho.character x by
      change e.chi j (ConjClasses.mk x) = rho.character x
      rw [hchar]
      rfl]
    simp [Representation.virtualCharacterOfRepresentations]
  obtain ⟨a, ha⟩ :=
    Section3.scalarProduct_isVirtualCharacter_eq_int hphiVirt hpsiVirt
  refine ⟨a, ?_⟩
  have hinner :=
    Section1.representation_inner_toConjClassFunction_right
      phi hphiClass (e.chi j)
  have hto :
      Section1.toConjClassFunction phi hphiClass =
        localSectionClassFunction d i z := by
    ext c
    rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
    rfl
  rw [hto] at hinner
  exact hinner.trans ha

theorem localSection_eq_sum_all_irreducibles
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G)
    (e : PrincipalCongruenceBlockData
      (Subgroup.centralizer ({z} : Set G)))
    (x : Subgroup.centralizer ({z} : Set G)) :
    d.chi i (ConjClasses.mk (z * (x : G))) =
      ∑ j : e.I,
        Representation.classFunctionInner
            (localSectionClassFunction d i z) (e.chi j) *
          e.chi j (ConjClasses.mk x) := by
  simpa using Representation.completeFamily_apply_eq_sum_inner
    e.complete (localSectionClassFunction d i z) (ConjClasses.mk x)

/-- For an involution, the complete local irreducible expansion of its section
has integer coefficients. -/
theorem localSection_eq_sum_all_irreducibles_int
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G)
    (hz : z * z = 1)
    (e : PrincipalCongruenceBlockData
      (Subgroup.centralizer ({z} : Set G))) :
    ∃ a : e.I → ℤ, ∀ x : Subgroup.centralizer ({z} : Set G),
      d.chi i (ConjClasses.mk (z * (x : G))) =
        ∑ j : e.I, (a j : ℂ) * e.chi j (ConjClasses.mk x) := by
  classical
  choose a ha using fun j : e.I => localSection_inner_eq_int d i z hz e j
  refine ⟨a, fun x => ?_⟩
  rw [localSection_eq_sum_all_irreducibles d i z e x]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [ha j]

/-- The exact local support statement left by the ordinary character
expansion: the non-principal-block part vanishes on the local odd core.

This is a Prop rather than an opaque chosen expansion.  Feit III.4.11,
Nagao III.7.5, and Brauer correspondence III.9.4 give the local block
support through IV.6.1; the blockwise decomposition-matrix result IV.6.6
identifies it with the ordinary-character statement below. -/
def LocalPrincipalBlockCoreSupport
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G)
    (e : PrincipalCongruenceBlockData
      (Subgroup.centralizer ({z} : Set G))) : Prop :=
  ∀ x : Subgroup.centralizer ({z} : Set G),
    x ∈ pPrimeCore 2 (Subgroup.centralizer ({z} : Set G)) →
      ∑ j ∈ (Finset.univ \ e.block),
        Representation.classFunctionInner
            (localSectionClassFunction d i z) (e.chi j) *
          e.chi j (ConjClasses.mk x) = 0

/-- A fixed constructed principal congruence block for the involution
centralizer.  Its existence is already unconditional.  This legacy choice is
kept for statements which do not need compatibility with an ambient modular
place; the canonical support predicate below uses the compatible datum. -/
noncomputable def localPrincipalCongruenceBlockData (z : G) :
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
def CanonicalLocalPrincipalBlockCoreSupport
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
  rcases Representation.completeFamily_form_basis e.complete with ⟨b, hb⟩
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
      Representation.classFunctionInner
          (localSectionClassFunction d d.principal z) (e.chi j) = 0 := by
    rw [hsection]
    rw [← Representation.completeFamily_basis_repr_eq_inner
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
noncomputable def localPrincipalBlockExpansion_of_coreSupport
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G)
    (e : PrincipalCongruenceBlockData
      (Subgroup.centralizer ({z} : Set G)))
    (hsupport : LocalPrincipalBlockCoreSupport d i z e) :
    LocalPrincipalBlockExpansion d i z := by
  let a : e.I → ℂ := fun j =>
    Representation.classFunctionInner
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
      Representation.classFunctionInner
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

/-- An alternative sufficient representation-level witness for the local
section calculation.

This is stronger than the generalized-decomposition expansion above, but is
convenient whenever an actual local representation is already available.
Only agreement on the odd core is recorded, since those are the only values
used below. -/
structure LocalSectionKernelWitness
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G) where
  n : ℕ
  theta : Representation ℂ (Subgroup.centralizer ({z} : Set G)) (Fin n → ℂ)
  core_le_ker :
    pPrimeCore 2 (Subgroup.centralizer ({z} : Set G)) ≤ theta.ker
  agrees_on_core : ∀ x : Subgroup.centralizer ({z} : Set G),
    x ∈ pPrimeCore 2 (Subgroup.centralizer ({z} : Set G)) →
      d.chi i (ConjClasses.mk (z * (x : G))) =
        theta.character (selfInCentralizer z * x)

/-- Once the local section representation is known to lie over the local
principal block, its odd-core kernel gives section invariance immediately. -/
theorem section_invariance_of_localSectionKernelWitness
    (d : PrincipalCongruenceBlockData G) {i : d.I} {z v : G}
    (hlocal : LocalSectionKernelWitness d i z)
    (hv : v ∈
      (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype) :
    d.chi i (ConjClasses.mk (z * v)) = d.chi i (ConjClasses.mk z) := by
  rcases Subgroup.mem_map.mp hv with ⟨vC, hvC, rfl⟩
  have hagree :
      d.chi i
          (ConjClasses.mk
            (z * (Subgroup.centralizer ({z} : Set G)).subtype vC)) =
        hlocal.theta.character (selfInCentralizer z * vC) := by
    simpa using hlocal.agrees_on_core vC hvC
  have hagreeOne :
      d.chi i (ConjClasses.mk z) =
        hlocal.theta.character (selfInCentralizer z) := by
    simpa using hlocal.agrees_on_core 1 (pPrimeCore 2 _).one_mem
  rw [hagree, hagreeOne]
  have hvker : vC ∈ hlocal.theta.ker := hlocal.core_le_ker hvC
  rw [MonoidHom.mem_ker] at hvker
  simp [Representation.character, map_mul, hvker]

/-- A family of the local witnesses supplies exactly the section-invariance
field expected by `PrincipalCongruenceBlockData.toPrincipalTwoBlockData`. -/
theorem principalBlock_section_invariance_of_localSectionKernelWitnesses
    (d : PrincipalCongruenceBlockData G)
    (hlocal : ∀ i ∈ d.block, ∀ z : G, IsInvolution z →
      LocalSectionKernelWitness d i z) :
    ∀ i ∈ d.block, ∀ z : G, IsInvolution z → ∀ v : G,
      v ∈ (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype →
      d.chi i (ConjClasses.mk (z * v)) = d.chi i (ConjClasses.mk z) := by
  intro i hi z hzI v hv
  exact section_invariance_of_localSectionKernelWitness
    d (hlocal i hi z hzI) hv

/-- The global affording representation itself is a local witness whenever
the centralizer odd core maps into the global odd core. -/
noncomputable def localSectionKernelWitness_of_localCore_le_globalCore
    (d : PrincipalCongruenceBlockData G) {i : d.I} (hi : i ∈ d.block)
    (z : G)
    (hlocal :
      (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
          (Subgroup.centralizer ({z} : Set G)).subtype ≤
        pPrimeCore 2 G) :
    LocalSectionKernelWitness d i z := by
  let n : ℕ := Classical.choose (d.complete.1 i).1
  have hn : ∃ rho : Representation ℂ G (Fin n → ℂ),
      d.chi i = Representation.characterClassFunction rho :=
    Classical.choose_spec (d.complete.1 i).1
  let rho : Representation ℂ G (Fin n → ℂ) := Classical.choose hn
  have hchar : d.chi i = Representation.characterClassFunction rho :=
    Classical.choose_spec hn
  refine {
    n := n
    theta := rho.comp (Subgroup.centralizer ({z} : Set G)).subtype
    core_le_ker := ?_
    agrees_on_core := ?_ }
  · intro x hx
    have hxMap : (x : G) ∈
        (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
          (Subgroup.centralizer ({z} : Set G)).subtype := by
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hxKer : (x : G) ∈ rho.ker :=
      PrincipalBlockKernel.pPrimeCore_le_representation_ker_of_mem_block
        d hi rho hchar (hlocal hxMap)
    rw [MonoidHom.mem_ker] at hxKer ⊢
    exact hxKer
  · intro x _hx
    rw [hchar]
    rfl

/-- If the odd core of the involution centralizer maps into the global odd
core, the global principal-block kernel theorem already gives the desired
section identity. -/
theorem section_invariance_of_localCore_le_globalCore
    (d : PrincipalCongruenceBlockData G) {i : d.I} (hi : i ∈ d.block)
    (z v : G)
    (hlocal :
      (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
          (Subgroup.centralizer ({z} : Set G)).subtype ≤
        pPrimeCore 2 G)
    (hv : v ∈
      (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype) :
    d.chi i (ConjClasses.mk (z * v)) = d.chi i (ConjClasses.mk z) := by
  exact PrincipalBlockKernel.character_mul_right_eq_of_mem_block
    d hi z v (hlocal hv)

/-- The odd core of an element centralizer maps into the global odd core in
a finite solvable group.  This specializes the existing centralizer-control
theorem from a cyclic `2`-subgroup to the singleton centralizer used by the
Z*-argument. -/
theorem localCore_le_globalCore_of_solvable
    (hsolv : IsSolvable G) (z : G) (hzI : IsInvolution z) :
    (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype ≤
      pPrimeCore 2 G := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R : Subgroup G := Subgroup.zpowers z
  have hzOrder : orderOf z = 2 := orderOf_eq_two
    (by simpa [pow_two] using hzI.2) hzI.1
  have hRp : IsPGroup 2 R := by
    have hcard : Nat.card (Subgroup.zpowers z) = 2 ^ 1 := by
      rw [Nat.card_zpowers, hzOrder]
      norm_num
    exact IsPGroup.of_card (n := 1) (by simpa [R] using hcard)
  have hcentralizer :
      Subgroup.centralizer (R : Set G) =
        Subgroup.centralizer ({z} : Set G) := by
    change Subgroup.centralizer (Subgroup.zpowers z : Set G) =
      Subgroup.centralizer ({z} : Set G)
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hlocal :=
    pPrimeCore_map_centralizer_le_pPrimeCore_of_solvable
      hsolv 2 R hRp
  rw [hcentralizer] at hlocal
  exact hlocal

/-- Principal-block section invariance for finite solvable groups. -/
theorem principalBlock_section_invariance_of_solvable
    (d : PrincipalCongruenceBlockData G) (hsolv : IsSolvable G)
    {i : d.I} (hi : i ∈ d.block) (z : G) (hzI : IsInvolution z)
    (v : G)
    (hv : v ∈
      (pPrimeCore 2 (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype) :
    d.chi i (ConjClasses.mk (z * v)) = d.chi i (ConjClasses.mk z) := by
  exact section_invariance_of_localCore_le_globalCore d hi z v
    (localCore_le_globalCore_of_solvable hsolv z hzI) hv

end LocalBlockSection

end Submission.ZStar
