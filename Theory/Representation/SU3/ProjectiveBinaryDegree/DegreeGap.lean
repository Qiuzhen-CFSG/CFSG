module
public import Theory.Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.Catalogue
public import Theory.Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.FrobeniusCounts
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all Theory.Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.WordBounds

/-!
# The characteristic-two gap above the natural unitary degree

The actual unitary tensor catalogue supplies a model over the algebraic
closure of the Schur field. Its graph-twisted Frobenius period gives the
binary dimension as the period times the tensor degree. Below 8b, the
numerical alternatives leave exactly one natural or dual factor and period
2b. Both coefficient-embedded actions are faithful, and their intertwiners
transfer faithfulness back to the original binary representation.

The result proves the characteristic-two part of Fong--Seitz I (4D),
printed pp.21--23: below 8b the degree is 6b and the full SU₃ acts faithfully.
The cubic-kernel argument in `ProjectiveBinaryDegree` applies it to PSU₃.
The internal import below exposes the period-count predicate only to this
implementation; its premises are discharged by the actual Schur-word proof.
-/

public noncomputable section
open BenderSuzuki.MatrixGroups Representation
open Representation.SL3.BinaryDefiningFactors
open scoped MonoidAlgebra TensorProduct
namespace Representation.SU3.ProjectiveBinaryDegree
open TensorCatalogue

private theorem four_mul_le_three_pow {r : ℕ} (hr : 2 ≤ r) : 4*r ≤ 3^r := by
  induction r, hr using Nat.le_induction with
  | base => decide
  | succ r hr ih => rw [pow_succ]; nlinarith

private theorem eight_mul_le_eight_pow {r : ℕ} (hr : 0 < r) : 8*r ≤ 8^r := by
  induction r, hr using Nat.le_induction with
  | base => decide
  | succ r hr ih => rw [pow_succ]; nlinarith

/-- The twisted-period counts exclude all but a singleton natural or dual
word below the next characteristic-two degree. -/
theorem single_factor_of_degree_lt (b e : ℕ) (_he : 0 < e)
    (w : List Factor) (hp : PeriodCounts b e w) (hd : e * wordDegree w < 8*b) :
    e = 2*b ∧ naturalCount w = 1 ∧ adjointCount w = 0 := by
  have hnle : 3 ^ naturalCount w ≤ wordDegree w := by
    rw [wordDegree_eq]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hale : 8 ^ adjointCount w ≤ wordDegree w := by
    rw [wordDegree_eq]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  rcases hp with ⟨r,hr,hperiod,hcount⟩ | ⟨r,hr,hperiod,hcount⟩
  · have hpow : 3^r ≤ wordDegree w :=
      (Nat.pow_le_pow_right (by decide) hcount).trans hnle
    have hrone : r=1 := by
      by_contra h
      have hsmall := four_mul_le_three_pow (r := r) (by omega)
      have hmul := Nat.mul_le_mul_left e (hsmall.trans hpow)
      nlinarith
    subst r
    have hes : e=2*b := by simpa using hperiod
    have hdegree : wordDegree w < 4 := by nlinarith
    have hn : naturalCount w=1 := by
      by_contra h
      have hlarge := Nat.pow_le_pow_right (n := 3) (by decide)
        (show 2 ≤ naturalCount w by omega)
      norm_num at hlarge
      omega
    have ha : adjointCount w=0 := by
      by_contra h
      have hlarge := Nat.pow_le_pow_right (n := 8) (by decide)
        (show 1 ≤ adjointCount w by omega)
      norm_num at hlarge
      omega
    exact ⟨hes,hn,ha⟩
  · have hpow : 8^r ≤ wordDegree w :=
      (Nat.pow_le_pow_right (by decide) hcount).trans hale
    have hmul := Nat.mul_le_mul_left e ((eight_mul_le_eight_pow hr).trans hpow)
    nlinarith

private theorem natural_injective {F K : Type*} [Field F] [Field K]
    (J : HermitianForm 3 F) (ι : F →+* K) : Function.Injective (natural J ι) := by
  intro g h he
  apply Subtype.ext
  apply Units.ext
  ext i j
  apply ι.injective
  have hv := congrArg (fun f : Module.End K (Fin 3 → K) => f (Pi.single j 1) i) he
  simpa only [natural_apply, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.map_apply] using hv

private theorem natural_dual_injective {F K : Type*} [Field F] [Field K]
    (J : HermitianForm 3 F) (ι : F →+* K) : Function.Injective (natural J ι).dual := by
  intro g h he
  apply inv_injective
  apply natural_injective J ι
  apply LinearMap.ext
  intro v
  funext i
  exact congrArg (fun f : Module.End K (Module.Dual K (Fin 3 → K)) =>
    f (LinearMap.proj i) v) he

private theorem equiv_injective {G K V W : Type*} [Group G] [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {ρ : Representation K G V} {τ : Representation K G W}
    (E : ρ.Equiv τ) (hτ : Function.Injective τ) : Function.Injective ρ := by
  intro g h he
  apply hτ
  ext w
  obtain ⟨v,rfl⟩ := E.toLinearEquiv.surjective w
  have hg := LinearMap.congr_fun (E.isIntertwining' g) v
  have hh := LinearMap.congr_fun (E.isIntertwining' h) v
  exact hg.symm.trans ((congrArg (fun f : Module.End K V => E (f v)) he).trans hh)

/-- Fong--Seitz I (4D), characteristic two: a nontrivial irreducible binary
SU₃ action below degree `8*b` has degree `6*b` and is faithful. The actual unitary tensor catalogue,
Schur scalar extension and twisted Frobenius periods are all discharged. -/
theorem eq_minimum_and_injective_of_irreducible_finrank_lt
    {F V : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {b : ℕ} (hb : 2 ≤ b)
    (hcard : Nat.card F=(2^b)^2) (hconj : ∀ x,J.conj x=x^(2^b))
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) J.specialSubgroup V) [IsIrreducible σ]
    (hne : ∃ g,σ g≠1) (hd : Module.finrank (ZMod 2) V < 8*b) :
    Module.finrank (ZMod 2) V = 6*b ∧ Function.Injective σ := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card,←pow_mul] using hcard)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let E := Module.End (ZMod 2)[J.specialSubgroup] σ.asModule
  let K := AlgebraicClosure E
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap E K).injective 2
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let ι : F →+* K := (IsAlgClosed.lift (R := ZMod 2) (S := F) (M := K)).toRingHom
  obtain ⟨w,hw,⟨φ⟩⟩ := exists_schur_word_model J σ b hb ι hcard hconj
  have hp := periodCounts_of_schur_word J σ hb hconj ι w hw
    (word_isIrreducible J b hb hcard hconj ι)
    (fun u v hu hv he => (word_equiv_iff J b hb hcard hconj ι u v hu hv).mp he)
    ⟨φ⟩ hne
  have hdim : Module.finrank (ZMod 2) V = schurDegree 2 σ * wordDegree w := by
    rw [finrank_eq_schurDegree_mul 2 σ K, φ.toLinearEquiv.finrank_eq, finrank_wordSpace]
  obtain ⟨he,hn,ha⟩ := single_factor_of_degree_lt b (schurDegree 2 σ)
    (schurDegree_pos 2 σ) w hp (hdim ▸ hd)
  refine ⟨?_,?_⟩
  · rw [hdim,he,wordDegree_eq,hn,ha]
    ring
  have hfaith : Function.Injective (extendScalars K σ.endFieldRep) := by
    obtain ⟨ι',hnat | hdual⟩ := word_single_factor J ι w hn ha
    · obtain ⟨ψ⟩ := hnat
      exact equiv_injective (φ.trans ψ) (natural_injective J ι')
    · obtain ⟨ψ⟩ := hdual
      exact equiv_injective (φ.trans ψ) (natural_dual_injective J ι')
  intro g h he
  apply hfaith
  have he' : σ.endFieldRep g = σ.endFieldRep h := by
    ext v
    apply σ.asModuleEquiv.injective
    simpa only [endFieldRep_apply'] using LinearMap.congr_fun he (σ.asModuleEquiv v)
  simp only [extendScalars_apply, he']

end Representation.SU3.ProjectiveBinaryDegree
