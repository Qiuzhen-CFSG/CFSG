module

public import Theory.SpecificGroups.ProjectiveDimensionThree.NondefiningThreeRank
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank
public import Theory.SpecificGroups.PSL3.ProjectionKernel
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.GroupTheory.CentralCoprimePrimeLift
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero
public import Theory.Quasithin.CoprimeRank
public import Theory.Representation.CubicTorsionDegreeThree
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import BenderSuzuki.External.Huppert.II.theorem_10_4
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Ordinary and cubic ranks for the degree-three classical covers

This file records the matrix statements used by the odd-centre branch.  The
ordinary odd-prime bound is proved on the actual determinant-one matrix
groups: a faithful elementary abelian action has at most three simultaneous
weights, and the determinant-one equation removes one weight.  The central
quotient maps are used only after this calculation, so the cubic scalar kernel
is retained in the cover statements.

Source: Aschbacher--Smith, A.2.12(I) and A.2.18, printed pp.36--37 and 40.
-/

public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Module Representation
open scoped MatrixGroups IsMulCommutative

namespace Theory.SpecificGroups.Classical

private theorem char_two_of_card_pow_two {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hcard : Nat.card F = 2 ^ n) : CharP F 2 := by
  let := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)

public theorem cast_ne_zero_of_odd_prime_char_two {F : Type*} [Field F]
    [CharP F 2] {p : ℕ} [Fact p.Prime] (hp : Odd p) : (p : F) ≠ 0 := by
  rw [ne_eq, CharP.cast_eq_zero_iff F 2]
  exact hp.not_two_dvd_nat

namespace ThreeCoverLocalRanks

private theorem exists_character_basis {E K V : Type*} [Field E] [Group K]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [IsMulCommutative K] [IsAlgClosed E]
    (sigma : Representation E K V)
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

variable {E F K V : Type*} [Field E] [Field F] [Group K]

private theorem card_le_prime_sq_of_faithful_generalLinear
    [Finite K] [IsMulCommutative K] {p : ℕ} [Fact p.Prime]
    (rho : K →* GL (Fin 3) F) (hfaith : Function.Injective rho)
    (hpF : (p : F) ≠ 0) (hpow : ∀ k : K, k ^ p = 1)
    (hdet : ∀ k, Matrix.GeneralLinearGroup.det (rho k) = 1) :
    Nat.card K ≤ p ^ 2 := by
  classical
  let E := AlgebraicClosure F
  let f : GL (Fin 3) F →* GL (Fin 3) E :=
    Matrix.GeneralLinearGroup.map (algebraMap F E)
  have hf : Function.Injective f := by
    intro a b h
    apply Units.ext
    ext i j
    apply (algebraMap F E).injective
    exact congrArg (fun c : GL (Fin 3) E => c i j) h
  let sigma : Representation E K (Fin 3 → E) :=
    (Representation.generalLinearNatural 3).comp (f.comp rho)
  have hsigma : Function.Injective sigma :=
    (Representation.generalLinearNatural_injective 3).comp (hf.comp hfaith)
  have hK : IsPGroup p K := fun k => ⟨1, by simpa using hpow k⟩
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  have horderF : (Nat.card K : F) ≠ 0 := by
    rw [hn, Nat.cast_pow]
    exact pow_ne_zero n hpF
  have horder : (Nat.card K : E) ≠ 0 := by
    intro h
    apply horderF
    apply (algebraMap F E).injective
    simpa using h
  obtain ⟨b, w, hw⟩ := exists_character_basis sigma horder
    (by simp only [Module.finrank_pi, Fintype.card_fin])
  have hmat (k : K) : LinearMap.toMatrix b b (sigma k) =
      Matrix.diagonal (fun i => ((w i).val k : E)) := by
    ext i j
    simp only [LinearMap.toMatrix_apply, hw, Units.smul_def, map_smul,
      Finsupp.smul_apply, Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst j; simp
    · simp [Matrix.diagonal, hij, Ne.symm hij]
  have hprod (k : K) : (((w 0).val k : E) * ((w 1).val k : E)) *
      ((w 2).val k : E) = 1 := by
    have he : LinearMap.det (sigma k) = 1 := by
      change LinearMap.det (Matrix.toLin' ((f (rho k)).val)) = 1
      rw [LinearMap.det_toLin']
      change Matrix.det ((algebraMap F E).mapMatrix (rho k).val) = 1
      rw [← RingHom.map_det]
      have hd : (rho k).val.det = 1 := congrArg Units.val (hdet k)
      rw [hd, map_one]
    rw [← LinearMap.det_toMatrix b, hmat, Matrix.det_diagonal,
      Fin.prod_univ_three] at he
    exact he
  let chi (i : Fin 3) : K →* rootsOfUnity p E :=
    (w i).val.codRestrict (rootsOfUnity p E) (fun k => by
      rw [mem_rootsOfUnity, ← map_pow, hpow, map_one])
  let f' := (chi 0).prod (chi 1)
  have hf' : Function.Injective f' := by
    apply (injective_iff_map_eq_one f').mpr
    intro k hk
    have h0 : ((w 0).val k : E) = 1 :=
      congrArg (fun z : rootsOfUnity p E × rootsOfUnity p E => (z.1.val : E)) hk
    have h1 : ((w 1).val k : E) = 1 :=
      congrArg (fun z : rootsOfUnity p E × rootsOfUnity p E => (z.2.val : E)) hk
    have h2 : ((w 2).val k : E) = 1 := by
      simpa only [h0, h1, one_mul] using hprod k
    have hi : ∀ i, ((w i).val k : E) = 1 := by
      intro i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    have hk1 : k = 1 := hsigma (by
      apply b.ext
      intro i
      have hi' : (w i).val k = 1 := by
        apply Units.ext
        exact hi i
      rw [hw]
      rw [hi']
      simp)
    exact hfaith (by rw [hk1, map_one])
  have hh := Nat.card_le_card_of_injective f' hf'
  rw [Nat.card_prod] at hh
  have hr := card_rootsOfUnity E p
  nlinarith

public theorem special_odd_prime_rank_le_two
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hpF : (p : F) ≠ 0) : primeRank p SL(3,F) ≤ 2 := by
  apply (primeRank_le_iff_elementary_card_le SL(3,F)).mpr
  intro A hA
  let := hA
  exact card_le_prime_sq_of_faithful_generalLinear
    (Matrix.SpecialLinearGroup.toGL.comp A.subtype)
    (Matrix.SpecialLinearGroup.toGL_injective.comp A.subtype_injective)
    hpF (fun a => by
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p A) a)
    (fun a => by exact Matrix.SpecialLinearGroup.coeToGL_det (A.subtype a))

public theorem unitary_odd_prime_rank_le_two
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {p : ℕ} [Fact p.Prime] (hpF : (p : F) ≠ 0) :
    primeRank p J.specialSubgroup ≤ 2 := by
  apply (primeRank_le_iff_elementary_card_le J.specialSubgroup).mpr
  intro A hA
  let := hA
  exact card_le_prime_sq_of_faithful_generalLinear
    (J.specialSubgroup.subtype.comp A.subtype)
    (fun a b h => A.subtype_injective (Subtype.ext h)) hpF
    (fun a => by
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p A) a)
    (fun a => by
      have h := ((J.mem_specialSubgroup_iff (A.subtype a).val).mp
        (A.subtype a).property).2
      exact h)

public theorem projective_linear_odd_prime_rank_le_two
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hp3 : p ≠ 3) (hpF : (p : F) ≠ 0) :
    primeRank p PSL(3,F) ≤ 2 := by
  have hcop3 : Nat.Coprime p 3 := by
    apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    intro h
    have : p = 3 := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
      (by decide : Nat.Prime 3)).mp h
    exact hp3 this
  have hker : Nat.Coprime p (Nat.card (Matrix.PSL3.projection F).ker) := by
    apply hcop3.of_dvd_right
    rw [Matrix.PSL3.card_projectionKernel]
    exact Nat.gcd_dvd_left 3 (Nat.card F - 1)
  rw [← primeRank_eq_of_surjective_of_coprime p (Matrix.PSL3.projection F)
    (Matrix.PSL3.projection_surjective F) hker]
  exact special_odd_prime_rank_le_two hpF

public theorem projective_unitary_odd_prime_rank_le_two
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) (hpF : (p : F) ≠ 0) :
    primeRank p (ProjectiveSpecialUnitaryMatrixGroup J) ≤ 2 := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have h3 : IsPGroup 3 J.specialToProjective.ker := fun x =>
    ⟨1, by simpa using J.specialToProjective_ker_cube x⟩
  obtain ⟨n, hn⟩ := h3.exists_card_eq
  have hcop : Nat.Coprime p (Nat.card J.specialToProjective.ker) := by
    rw [hn]
    exact (by
      apply (by decide : Nat.Prime 3).coprime_pow_of_not_dvd (m := n)
      intro h
      exact hp3 ((Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3)
        (Fact.out : p.Prime)).mp h).symm)
  rw [← primeRank_eq_of_surjective_of_coprime p J.specialToProjective
    J.specialToProjective_surjective hcop]
  exact unitary_odd_prime_rank_le_two J hpF

end ThreeCoverLocalRanks

namespace ThreeCoverLocalRanks

public theorem binary_linear_special_threeRank_eq_two
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : Even n) :
    primeRank 3 SL(3,F) = 2 := by
  let : CharP F 2 := char_two_of_card_pow_two hcard
  apply le_antisymm
  · exact special_odd_prime_rank_le_two (F := F) (by
      rw [ne_eq, CharP.cast_eq_zero_iff F 2]
      norm_num)
  · exact Theory.SpecificGroups.SignedThreeCubicRank.linear_special hcard hn

public theorem binary_unitary_special_threeRank_eq_two
    {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {n : ℕ} (hnpos : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) (hn : Odd n) :
    primeRank 3 J.specialSubgroup = 2 := by
  let : CharP F 2 := char_two_of_card_pow_two (n := n * 2) (by
    simpa only [pow_mul, Nat.mul_comm] using hcard)
  apply le_antisymm
  · exact unitary_odd_prime_rank_le_two J (by
      rw [ne_eq, CharP.cast_eq_zero_iff F 2]
      norm_num)
  · exact Theory.SpecificGroups.SignedThreeCubicRank.unitary_special
      J hnpos hcard hconj hn

end ThreeCoverLocalRanks

namespace ThreeCoverLocalRanks

/-- If an odd prime divides the norm-one torus order, the actual special
unitary group has the two independent torus directions.  The field order and
the Frobenius exponent are kept in the statement so this is also the witness
used after transporting a stored Hermitian form. -/
public theorem binary_unitary_special_primeRank_ge_two
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n s : ℕ} (hn : 0 < n) (hs : s.Prime) (hdiv : s ∣ 2 ^ n + 1)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    2 ≤ primeRank s J.specialSubgroup := by
  let : Fact s.Prime := ⟨hs⟩
  have hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ n := by
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  obtain ⟨P, hP⟩ :=
    BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis 3 J (2 ^ n)
      hcard hfixed
  let P' : UnitaryThree.OddTorusNormalizer.OrthogonalFrame J := ⟨P, hP⟩
  let T := UnitaryThree.OddTorusNormalizer.specialFrameTorus J P'
  have hcyc : 1 ≤ primeRank s (Multiplicative (ZMod (2 ^ n + 1))) := by
    have hne : primeRank s (Multiplicative (ZMod (2 ^ n + 1))) ≠ 0 := by
      intro hz
      apply (PrimeRank.eq_zero_iff_not_dvd_card.mp hz)
      simpa only [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] using hdiv
    exact Nat.one_le_iff_ne_zero.mpr hne
  have hprod : 2 ≤ primeRank s
      (Multiplicative (ZMod (2 ^ n + 1)) ×
        Multiplicative (ZMod (2 ^ n + 1))) := by
    rw [primeRank_prod_eq_add s]
    omega
  have htorus : 2 ≤ primeRank s T := by
    rw [primeRank_equiv s
      (UnitaryThree.OddTorusNormalizer.specialFrameTorusEquivCyclic
        J P' (2 ^ n) hcard hfixed)]
    exact hprod
  have hinc : 2 ≤ primeRank s J.specialSubgroup := by
    exact htorus.trans (Theory.GroupTheory.primeRank_le_of_injective s
      T.subtype T.subtype_injective)
  exact hinc

end ThreeCoverLocalRanks

end Theory.SpecificGroups.Classical
