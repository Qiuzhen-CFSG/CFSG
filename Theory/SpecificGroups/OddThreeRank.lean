module

public import Theory.Representation.CubicTorsionDegreeThree
public import Theory.GroupTheory.CentralCoprimePrimeLift
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.QuasithinBasic
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison

/-!
# Two-rank in odd-characteristic groups of degree three

An elementary abelian two-group acting faithfully in determinant-one degree
three has order at most four: after scalar extension its simultaneous weights
are signs, and the first two determine the third. The special groups embed
in the matrix group. Their projective images have the same bound because
an elementary two-subgroup lifts through the central odd-order kernel.

This proves the inner-rank contribution used in Aschbacher–Smith,
G.7.3(1), printed p.348 (PDF p.359). The character-basis argument adapts the
cubic-torsion proof in `Theory.Representation.CubicTorsionDegreeThree`.
-/

noncomputable section
public section

open Subgroup Matrix Module Representation
open scoped MatrixGroups
open Theory.GroupTheory BenderSuzuki.MatrixGroups

namespace Theory.SpecificGroups.OddThreeRank

private theorem exists_character_basis {E K V : Type*} [Field E] [Group K]
    [AddCommGroup V] [Module E V] [IsMulCommutative K] [FiniteDimensional E V]
    [Finite K] [IsAlgClosed E] (sigma : Representation E K V)
    (horder : (Nat.card K : E) ≠ 0) (hdim : Module.finrank E V = 3) :
    ∃ (b : Basis (Fin 3) E V) (w : Fin 3 → sigma.CharacterWeight),
      ∀ k i, sigma k (b i) = (w i).val k • b i := by
  classical
  let W : sigma.CharacterWeight → Submodule E V :=
    fun chi => sigma.characterWeightSpace chi.val
  have hind : iSupIndep W :=
    (sigma.characterWeightSpace_independent horder).comp Subtype.val_injective
  have hi := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind
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

/-- A faithful elementary abelian two-subgroup in a special three-dimensional
matrix group has order at most four. -/
theorem elementary_card_le_four
    {F K : Type*} [Field F] [Group K] [Finite K] [IsMulCommutative K]
    (rho : K →* GL (Fin 3) F) (hfaith : Function.Injective rho)
    (hchar : (2 : F) ≠ 0) (hcube : ∀ k : K, k ^ 2 = 1)
    (hdet : ∀ k, Matrix.GeneralLinearGroup.det (rho k) = 1) : Nat.card K ≤ 4 := by
  classical
  let E := AlgebraicClosure F
  let f : GL (Fin 3) F →* GL (Fin 3) E := Matrix.GeneralLinearGroup.map (algebraMap F E)
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
  have hK : IsPGroup 2 K := fun k => ⟨1, by simpa using hcube k⟩
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  have horder : (Nat.card K : F) ≠ 0 := by
    rw [hn, Nat.cast_pow]
    exact pow_ne_zero n hchar
  have horder' : (Nat.card K : E) ≠ 0 := by
    intro h
    apply horder
    apply (algebraMap F E).injective
    simpa using h
  obtain ⟨b, w, hw⟩ := exists_character_basis sigma horder'
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
      change LinearMap.det (Matrix.toLin' (f (rho k)).val) = 1
      rw [LinearMap.det_toLin']
      change Matrix.det ((algebraMap F E).mapMatrix (rho k).val) = 1
      rw [← RingHom.map_det]
      have hd : (rho k).val.det = 1 := congrArg Units.val (hdet k)
      rw [hd, map_one]
    rw [← LinearMap.det_toMatrix b, hmat, Matrix.det_diagonal, Fin.prod_univ_three] at he
    exact he
  let chi (i : Fin 3) : K →* rootsOfUnity 2 E :=
    (w i).val.codRestrict (rootsOfUnity 2 E) (fun k => by
      rw [mem_rootsOfUnity, ← map_pow, hcube k, map_one])
  let f' := (chi 0).prod (chi 1)
  have hf' : Function.Injective f' := by
    apply (injective_iff_map_eq_one f').mpr
    intro k hk
    have h0 : ((w 0).val k : E) = 1 :=
      congrArg (fun z : rootsOfUnity 2 E × rootsOfUnity 2 E => (z.1.val : E)) hk
    have h1 : ((w 1).val k : E) = 1 :=
      congrArg (fun z : rootsOfUnity 2 E × rootsOfUnity 2 E => (z.2.val : E)) hk
    have h2 : ((w 2).val k : E) = 1 := by
      simpa only [h0, h1, one_mul] using hprod k
    have hi : ∀ i, ((w i).val k : E) = 1 := by
      intro i
      fin_cases i <;> assumption
    have hs : sigma k = 1 := by
      apply b.ext
      intro i
      change sigma k (b i) = b i
      rw [hw]
      have hscl : ((w i).val k : E) = 1 := hi i
      exact (congrArg (fun c : E => c • b i) hscl).trans (one_smul E (b i))
    apply hfaith
    apply hf
    apply Representation.generalLinearNatural_injective 3
    simpa [sigma] using hs
  have hh := Nat.card_le_card_of_injective f' hf'
  rw [Nat.card_prod] at hh
  have hr := card_rootsOfUnity E 2
  exact hh.trans (Nat.mul_le_mul hr hr) |>.trans (by norm_num)

theorem special_primeRank_two_le
    {F S : Type*} [Field F] [Finite F] [Group S] [Finite S]
    (e : S ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (hchar : (2 : F) ≠ 0) : primeRank 2 S ≤ 2 := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  rw [primeRank_equiv 2 e]
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro A hA
  let rho : A →* GL (Fin 3) F := Matrix.SpecialLinearGroup.toGL.comp A.subtype
  have hfaith : Function.Injective rho := by
    exact Matrix.SpecialLinearGroup.toGL_injective.comp A.subtype_injective
  have hdet (x : A) : Matrix.GeneralLinearGroup.det (rho x) = 1 := by
    change Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL x.val) = 1
    exact Matrix.SpecialLinearGroup.coeToGL_det x.val
  have hpow (x : A) : x ^ 2 = 1 := by
    simpa using (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      hA.exponent_dvd_p x)
  exact elementary_card_le_four rho hfaith hchar hpow hdet

private theorem projective_primeRank_two_le_of_central_lift
    {R P : Type*} [Group R] [Finite R] [Group P] [Finite P]
    (f : R →* P) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ center R) (hker : Nat.Coprime 2 (Nat.card f.ker))
    (hr : primeRank 2 R ≤ 2) : primeRank 2 P ≤ 2 := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply (primeRank_le_iff_elementary_card_le P).mpr
  intro B hB
  let _ : IsElementaryAbelian 2 B := hB
  obtain ⟨A, hA, hmap, _, _, hinj⟩ :=
    Subgroup.exists_prime_lift_of_central_coprime f hf hcentral hker B
      (IsElementaryAbelian.isPGroup 2 B)
  let fA := f.comp A.subtype
  let g : A →* B := fA.codRestrict B (fun x => by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem f x.property)
  have hgsurj : Function.Surjective g := by
    intro y
    have hy : (y : P) ∈ A.map f := hmap.symm ▸ y.property
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  let _ : IsElementaryAbelian 2 A := {
    toIsMulCommutative := by
      exact IsMulCommutative.of_comm (fun x y => by
        apply hinj
        simpa [g, fA] using hB.toIsMulCommutative.is_comm.comm (g x) (g y))
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply hinj
      change fA (x ^ 2) = fA 1
      simpa [g, fA] using congrArg Subtype.val
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 B) (g x)) }
  have hcardA : Nat.card A ≤ 2 ^ 2 :=
    (primeRank_le_iff_elementary_card_le R).mp hr A inferInstance
  exact (Nat.card_le_card_of_surjective g hgsurj).trans hcardA

theorem hermitian_special_primeRank_two_le
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    (hchar : (2 : E) ≠ 0) : primeRank 2 J.specialSubgroup ≤ 2 := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro A hA
  let rho : A →* GL (Fin 3) E := J.specialSubgroup.subtype.comp A.subtype
  have hfaith : Function.Injective rho :=
    J.specialSubgroup.subtype_injective.comp A.subtype_injective
  have hdet (x : A) : Matrix.GeneralLinearGroup.det (rho x) = 1 := by
    change Matrix.GeneralLinearGroup.det (x.val : GL (Fin 3) E) = 1
    exact x.val.property.2
  have hpow (x : A) : x ^ 2 = 1 := by
    simpa using (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      hA.exponent_dvd_p x)
  exact elementary_card_le_four rho hfaith hchar hpow hdet

theorem two_ne_zero_of_odd_card {F : Type*} [Field F] [Finite F]
    {p k : ℕ} (ho : Odd p) (hcard : Nat.card F = p ^ k) :
    (2 : F) ≠ 0 := by
  intro h
  let _ : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h
  let _ := Fintype.ofFinite F
  have he := FiniteField.even_card_of_char_two (F := F) (ringChar.eq F 2)
  have hc : Fintype.card F = p ^ k := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  rw [hc] at he
  exact (Nat.not_even_iff_odd.mpr (Odd.pow ho)) (Nat.even_iff.mpr he)

theorem psl3_primeRank_two_le {F : Type*} [Field F] [Finite F]
    {p : ℕ} (_hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p) :
    primeRank 2 (PSL(3,F)) ≤ 2 := by
  have hchar := two_ne_zero_of_odd_card ho (k := 1) (by simpa using hF)
  apply projective_primeRank_two_le_of_central_lift (PSL3.projection F)
    (PSL3.projection_surjective F) (by rw [PSL3.projection_ker])
    (by simpa only [PSL3.projection_ker] using
      (Matrix.SL3.odd_card_center F).coprime_two_left)
  exact special_primeRank_two_le (MulEquiv.refl _) hchar

theorem psu3_primeRank_two_le
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {p : ℕ} (_hp : p.Prime) (ho : Odd p) (hcard : Nat.card E = p ^ 2)
    (_hconj : ∀ x : E, J.conj x = x ^ p) :
    primeRank 2 (ProjectiveSpecialUnitaryMatrixGroup J) ≤ 2 := by
  have hchar := two_ne_zero_of_odd_card ho hcard
  let _ : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  apply projective_primeRank_two_le_of_central_lift J.specialToProjective
    J.specialToProjective_surjective J.specialToProjective_ker_le_center
    (by simpa only using
      (J.odd_card_specialToProjective_ker).coprime_two_left)
  exact hermitian_special_primeRank_two_le J hchar

end Theory.SpecificGroups.OddThreeRank
