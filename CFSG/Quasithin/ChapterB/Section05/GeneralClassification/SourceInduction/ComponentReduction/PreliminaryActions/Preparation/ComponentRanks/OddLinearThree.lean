module

public import Theory.GroupTheory.PrimeRankElementary
public import Theory.Representation.AbelianAllWeights
public import Theory.Representation.GeneralLinearNatural
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Odd-prime rank of the degree-three component models

An elementary abelian odd-prime subgroup of SL₃ in characteristic two acts
semisimply over the algebraic closure. Collect a basis from its simultaneous
character spaces. Determinant one makes the third character value the inverse
of the product of the first two, giving an injection into two groups of p-th
roots of unity and hence order at most p². The elementary-abelian rank
criterion then bounds the original abelian-generator prime rank.

The proof generalizes the existing cubic-torsion calculation in
`Theory/Representation/CubicTorsionDegreeThree.lean`. Its actual consumer is
`Preparation.stronglyQuasithin_of_componentModels`, for the SL₃ row of the
full B.5.5(1iv) component list. This computation does not classify an action.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.5 and
the reduction preceding B.5.9, printed pp.104–107; the character argument
underlying A.3.21(c), printed pp.55–56.
-/

public section

open Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.Preparation.ComponentRanks
open Representation
variable {E K V : Type*} [Field E] [Group K]
  [AddCommGroup V] [Module E V] [IsMulCommutative K]
  [FiniteDimensional E V] [IsAlgClosed E]

private theorem exists_character_basis (sigma : Representation E K V)
    (horder : (Nat.card K : E) ≠ 0) (hdim : Module.finrank E V = 3) :
    ∃ (b : Basis (Fin 3) E V) (w : Fin 3 → sigma.CharacterWeight),
      ∀ k i, sigma k (b i) = (w i).val k • b i := by
  classical
  let W : sigma.CharacterWeight → Submodule E V :=
    fun chi => sigma.characterWeightSpace chi.val
  have hind : iSupIndep W :=
    (sigma.characterWeightSpace_independent horder).comp Subtype.val_injective
  have hi : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind
      (sigma.iSup_characterWeightSpace_eq_top horder)
  let b₀ := hi.collectedBasis (fun chi => Module.finBasis E (W chi))
  let e := b₀.indexEquiv ((Module.finBasis E V).reindex (finCongr hdim))
  refine ⟨b₀.reindex e, fun i => (e.symm i).1, ?_⟩
  intro k i
  have hm := hi.collectedBasis_mem (fun chi => Module.finBasis E (W chi)) (e.symm i)
  have he : ∀ k, sigma k (b₀ (e.symm i)) =
      (((e.symm i).1.val k : Eˣ) : E) • b₀ (e.symm i) := by
    change b₀ (e.symm i) ∈ sigma.characterWeightSpace (e.symm i).1.val at hm
    simpa only [characterWeightSpace, Submodule.mem_iInf,
      Module.End.mem_eigenspace_iff] using hm
  simpa only [Basis.coe_reindex, Function.comp_apply, Units.smul_def] using he k


/-- Two character values determine a determinant-one operator of degree three. -/
private theorem card_le_sq_of_pow_det_one (sigma : Representation E K V)
    {p : ℕ} [Fact p.Prime]
    (horder : (Nat.card K : E) ≠ 0) (hdim : Module.finrank E V = 3)
    (hfaith : Function.Injective sigma) (hpow : ∀ k : K, k ^ p = 1)
    (hdet : ∀ k, LinearMap.det (sigma k) = 1) : Nat.card K ≤ p ^ 2 := by
  classical
  obtain ⟨b, w, hw⟩ := exists_character_basis sigma horder hdim
  have hmat (k : K) : LinearMap.toMatrix b b (sigma k) =
      Matrix.diagonal (fun i => ((w i).val k : E)) := by
    ext i j
    simp only [LinearMap.toMatrix_apply, hw, Units.smul_def, map_smul,
      Finsupp.smul_apply, Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst j; simp
    · simp [Matrix.diagonal, hij, Ne.symm hij]
  have hprod (k : K) : (((w 0).val k : E) * ((w 1).val k : E)) * ((w 2).val k : E) = 1 := by
    have he := hdet k
    rw [← LinearMap.det_toMatrix b, hmat, Matrix.det_diagonal, Fin.prod_univ_three] at he
    exact he
  let chi (i : Fin 3) : K →* rootsOfUnity p E :=
    (w i).val.codRestrict (rootsOfUnity p E) (fun k => by
      rw [mem_rootsOfUnity, ← map_pow, hpow, map_one])
  let f := (chi 0).prod (chi 1)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro k hk
    have h0 : ((w 0).val k : E) = 1 :=
      congrArg (fun z : rootsOfUnity p E × rootsOfUnity p E => (z.1.val : E)) hk
    have h1 : ((w 1).val k : E) = 1 :=
      congrArg (fun z : rootsOfUnity p E × rootsOfUnity p E => (z.2.val : E)) hk
    have h2 : ((w 2).val k : E) = 1 := by simpa only [h0, h1, one_mul] using hprod k
    have hi : ∀ i, ((w i).val k : E) = 1 := by
      intro i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    apply hfaith
    rw [map_one]
    apply b.ext
    intro i
    simp only [hw, Units.smul_def, hi, one_smul, Module.End.one_apply]
  have hh := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at hh
  exact hh.trans (by simpa only [pow_two] using Nat.mul_self_le_mul_self (card_rootsOfUnity E p))


/-- The determinant relation removes the third independent character. -/
theorem linearThree_odd_primeRank_le_two
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) :
    primeRank p (Matrix.SpecialLinearGroup (Fin 3) F) ≤ 2 := by
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro A hA
  let := hA
  let E := AlgebraicClosure F
  let f : Matrix.SpecialLinearGroup (Fin 3) F →*
      Matrix.SpecialLinearGroup (Fin 3) E := Matrix.SpecialLinearGroup.map (algebraMap F E)
  have hf : Function.Injective f := by
    intro a b h
    ext i j
    apply (algebraMap F E).injective
    exact congrArg (fun c : Matrix.SpecialLinearGroup (Fin 3) E => c i j) h
  let sigma : Representation E A (Fin 3 → E) :=
    (specialLinearNatural 3).comp (f.comp A.subtype)
  have hsigma : Function.Injective sigma :=
    (specialLinearNatural_injective 3).comp (hf.comp A.subtype_injective)
  have hpF : (p : F) ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff F 2]
    exact hp.not_two_dvd_nat
  have horderF : (Nat.card A : F) ≠ 0 := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hn, Nat.cast_pow]
    exact pow_ne_zero n hpF
  have horder : (Nat.card A : E) ≠ 0 := by
    intro h
    apply horderF
    apply (algebraMap F E).injective
    simpa using h
  apply card_le_sq_of_pow_det_one sigma horder
    (by simp only [Module.finrank_pi, Fintype.card_fin]) hsigma
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p A))
  intro a
  change LinearMap.det (Matrix.toLin' (f a.val).val) = 1
  rw [LinearMap.det_toLin']
  exact (f a.val).property
end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.Preparation.ComponentRanks
