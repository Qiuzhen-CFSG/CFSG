module
public import Theory.Representation.CubicTorsionDegreeThree
public import Theory.GroupTheory.PrimeRankElementary

/-!
# Two-rank of odd-characteristic determinant-one degree four groups

Simultaneous sign weights embed a faithful elementary two-group in three
copies of the two roots of unity: the determinant determines the fourth
weight. This bound feeds the central cyclic quotient estimates for the odd
Theorem B rows in Aschbacher–Smith 4.4.3, printed p.622.
-/

noncomputable section
public section
open Subgroup Matrix Module Representation
open scoped MatrixGroups
namespace Theory.SpecificGroups.OddFourRank
private theorem exists_character_basis {E K V : Type*} [Field E] [Group K]
    [AddCommGroup V] [Module E V] [IsMulCommutative K] [FiniteDimensional E V]
    [Finite K] [IsAlgClosed E] (sigma : Representation E K V)
    (horder : (Nat.card K : E) ≠ 0) (hdim : Module.finrank E V = 4) :
    ∃ (b : Basis (Fin 4) E V) (w : Fin 4 → sigma.CharacterWeight),
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

/-- A faithful elementary abelian two-subgroup in a special four-dimensional
matrix group has order at most eight. -/
theorem elementary_card_le_eight
    {F K : Type*} [Field F] [Group K] [Finite K] [IsMulCommutative K]
    (rho : K →* GL (Fin 4) F) (hfaith : Function.Injective rho)
    (hchar : (2 : F) ≠ 0) (hcube : ∀ k : K, k ^ 2 = 1)
    (hdet : ∀ k, Matrix.GeneralLinearGroup.det (rho k) = 1) : Nat.card K ≤ 8 := by
  classical
  let E := AlgebraicClosure F
  let f : GL (Fin 4) F →* GL (Fin 4) E := Matrix.GeneralLinearGroup.map (algebraMap F E)
  have hf : Function.Injective f := by
    intro a b h
    apply Units.ext
    ext i j
    apply (algebraMap F E).injective
    exact congrArg (fun c : GL (Fin 4) E => c i j) h
  let sigma : Representation E K (Fin 4 → E) :=
    (Representation.generalLinearNatural 4).comp (f.comp rho)
  have hsigma : Function.Injective sigma :=
    (Representation.generalLinearNatural_injective 4).comp (hf.comp hfaith)
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
      ((w 2).val k : E) * ((w 3).val k : E) = 1 := by
    have he : LinearMap.det (sigma k) = 1 := by
      change LinearMap.det (Matrix.toLin' (f (rho k)).val) = 1
      rw [LinearMap.det_toLin']
      change Matrix.det ((algebraMap F E).mapMatrix (rho k).val) = 1
      rw [← RingHom.map_det]
      have hd : (rho k).val.det = 1 := congrArg Units.val (hdet k)
      rw [hd, map_one]
    rw [← LinearMap.det_toMatrix b, hmat, Matrix.det_diagonal, Fin.prod_univ_four] at he
    exact he
  let chi (i : Fin 4) : K →* rootsOfUnity 2 E :=
    (w i).val.codRestrict (rootsOfUnity 2 E) (fun k => by
      rw [mem_rootsOfUnity, ← map_pow, hcube k, map_one])
  let f' := ((chi 0).prod (chi 1)).prod (chi 2)
  have hf' : Function.Injective f' := by
    apply (injective_iff_map_eq_one f').mpr
    intro k hk
    have h0 : ((w 0).val k : E) = 1 :=
      congrArg (fun z : (rootsOfUnity 2 E × rootsOfUnity 2 E) × rootsOfUnity 2 E => (z.1.1.val : E)) hk
    have h1 : ((w 1).val k : E) = 1 :=
      congrArg (fun z : (rootsOfUnity 2 E × rootsOfUnity 2 E) × rootsOfUnity 2 E => (z.1.2.val : E)) hk
    have h2 : ((w 2).val k : E) = 1 :=
      congrArg (fun z : (rootsOfUnity 2 E × rootsOfUnity 2 E) × rootsOfUnity 2 E => (z.2.val : E)) hk
    have h3 : ((w 3).val k : E) = 1 := by
      simpa only [h0, h1, h2, one_mul] using hprod k
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
    apply Representation.generalLinearNatural_injective 4
    simpa [sigma] using hs
  have hh := Nat.card_le_card_of_injective f' hf'
  simp only [Nat.card_prod] at hh
  have hr := card_rootsOfUnity E 2
  exact hh.trans (Nat.mul_le_mul (Nat.mul_le_mul hr hr) hr) |>.trans (by norm_num)

/-- Every finite group faithfully represented in determinant-one degree four
has two-rank at most three in odd characteristic. -/
theorem twoRank_le_three {F S : Type*} [Field F] [Group S] [Finite S]
    (ρ : S →* GL (Fin 4) F) (hρ : Function.Injective ρ)
    (h2 : (2 : F) ≠ 0) (hdet : ∀ s, Matrix.GeneralLinearGroup.det (ρ s) = 1) :
    primeRank 2 S ≤ 3 := by
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro A hA
  let : IsElementaryAbelian 2 A := hA
  exact elementary_card_le_eight (ρ.comp A.subtype) (hρ.comp A.subtype_injective) h2
    (fun a => Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) a) (fun a => hdet a.val)
end Theory.SpecificGroups.OddFourRank
