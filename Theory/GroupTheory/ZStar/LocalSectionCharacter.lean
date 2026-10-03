module

public import Theory.Character.ModularBlock.Congruence
public import Theory.Character.ModularBlock.IdempotentTrace
public import Theory.Character.CharacterValues
public import Theory.GroupTheory.ZStar.LocalReduction
public import Theory.Representation.Standardization
public import Theory.Character.VirtualScalarProduct

/-!
# Integer character expansions of involution sections

The section `x ↦ chi(z*x)` is a class function on the centralizer of `z`.
When `z` squares to one, split its action using the idempotents `(1+z)/2`
and `(1-z)/2`. Their invariant images give two representations whose character
difference is the section. The idempotent trace theorem identifies the traces
on these images with the projected ambient traces.

Thus the section is a virtual character. Integrality of inner products of
virtual characters, together with the complete ordinary character family,
gives its canonical local expansion with integer coefficients. No block-support
claim is used here; that is a separate modular input in LocalBlockSection.

This is the ordinary-character portion of historical
`Submission/ZStar/LocalBlockSection.lean` at commit `c3503435`. The section
function and self-centralizer element have exposed bodies for the downstream
support and witness constructions; their underlying production definitions
are reused.
-/

public section

noncomputable section
open scoped BigOperators
namespace Glauberman.ZStar.LocalBlockSection
open ModularBlock.PrincipalBlockConstruction BenderSuzuki.PFAppendixIII
universe u
attribute [local instance] Fintype.ofFinite
variable {G : Type u} [Group G] [Finite G]

/-- Regard an element as an element of its own centralizer. -/
@[expose] def selfInCentralizer (z : G) :
    Subgroup.centralizer ({z} : Set G) :=
  ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

/-! The following canonical expansion separates the elementary character
linear algebra from the genuinely modular support assertion. -/

@[expose] noncomputable def localSectionClassFunction
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G) :
    ConjClassFunction (Subgroup.centralizer ({z} : Set G)) :=
  conjClassFunctionOfInvariant
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
    IsVirtualCharacter
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
      ModularBlock.CentralIdempotentSupport.trace_comp_idempotent_eq_trace_range
        pPlus (rhoC x) hpPlus (by
          simpa only [← Module.End.mul_eq_comp] using (hpPlusComm x).symm)
    have htraceMinus :=
      ModularBlock.CentralIdempotentSupport.trace_comp_idempotent_eq_trace_range
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
  rw [show virtualCharacterOfRepresentations 2 weights dims reps x =
      plusStd.character x - minusStd.character x by
    rw [virtualCharacterOfRepresentations]
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
      classFunctionInner
          (localSectionClassFunction d i z) (e.chi j) = (a : ℂ) := by
  classical
  let C := Subgroup.centralizer ({z} : Set G)
  let phi : ClassFunction C :=
    fun x => localSectionClassFunction d i z (ConjClasses.mk x)
  have hphiVirt : IsVirtualCharacter phi := by
    change IsVirtualCharacter
      (fun x : C => d.chi i (ConjClasses.mk (z * (x : G))))
    simpa [C] using localSection_isVirtualCharacter d i z hz
  let psi : ClassFunction C := fun x => e.chi j (ConjClasses.mk x)
  have hpsiVirt : IsVirtualCharacter psi := by
    rcases (e.complete.1 j).1 with ⟨n, rho, hchar⟩
    refine ⟨1, (fun _ : Fin 1 => (1 : ℤ)), (fun _ : Fin 1 => n),
      (fun _ : Fin 1 => rho), ?_⟩
    ext x
    rw [show psi x = rho.character x by
      change e.chi j (ConjClasses.mk x) = rho.character x
      rw [hchar]
      rfl]
    simp [virtualCharacterOfRepresentations]
  exact hphiVirt.scalarProduct_int hpsiVirt

theorem localSection_eq_sum_all_irreducibles
    (d : PrincipalCongruenceBlockData G) (i : d.I) (z : G)
    (e : PrincipalCongruenceBlockData
      (Subgroup.centralizer ({z} : Set G)))
    (x : Subgroup.centralizer ({z} : Set G)) :
    d.chi i (ConjClasses.mk (z * (x : G))) =
      ∑ j : e.I,
        classFunctionInner
            (localSectionClassFunction d i z) (e.chi j) *
          e.chi j (ConjClasses.mk x) := by
  simpa using completeFamily_apply_eq_sum_inner
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


end Glauberman.ZStar.LocalBlockSection

