module

public import Theory.Representation.AbelianAllWeights
public import Theory.Representation.GeneralLinearNatural
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.GroupTheory.PGroup

/-!
# Cubic torsion in determinant-one groups of degree three

Commuting operators of exponent three in characteristic different from three
are semisimple. Over the algebraic closure, collect bases of their simultaneous
character spaces. The determinant-one equation says that the three character
values have product one. The first two values therefore give a faithful map
into two groups of cube roots of unity, each of order at most three.

For matrices over an arbitrary field, the entrywise embedding into its
algebraic closure preserves both faithfulness and the actual determinant.
The character-basis construction follows the private construction in
`Theory/Representation/NoncyclicDegreeThree.lean` using the all-weights API.

Source: the abelian weight argument underlying Aschbacher–Smith, A.3.21(c),
printed pp.55–56 of `refs/quasithin.pdf`.
-/

public section

open Module
open scoped IsMulCommutative
namespace Representation
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


/-- A faithful determinant-one action of exponent three in dimension three has
at most nine elements. The order assumption supplies semisimplicity. -/
theorem card_le_nine_of_cube_det_one (sigma : Representation E K V)
    (horder : (Nat.card K : E) ≠ 0) (hdim : Module.finrank E V = 3)
    (hfaith : Function.Injective sigma) (hcube : ∀ k : K, k ^ 3 = 1)
    (hdet : ∀ k, LinearMap.det (sigma k) = 1) : Nat.card K ≤ 9 := by
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
  let chi (i : Fin 3) : K →* rootsOfUnity 3 E :=
    (w i).val.codRestrict (rootsOfUnity 3 E) (fun k => by
      rw [mem_rootsOfUnity, ← map_pow, hcube, map_one])
  let f := (chi 0).prod (chi 1)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro k hk
    have h0 : ((w 0).val k : E) = 1 :=
      congrArg (fun z : rootsOfUnity 3 E × rootsOfUnity 3 E => (z.1.val : E)) hk
    have h1 : ((w 1).val k : E) = 1 :=
      congrArg (fun z : rootsOfUnity 3 E × rootsOfUnity 3 E => (z.2.val : E)) hk
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
  have hr := card_rootsOfUnity E 3
  nlinarith

end Representation

namespace Representation

/-- A finite abelian group of cube-one determinant-one matrices of degree three
has order at most nine in characteristic different from three. -/
theorem card_le_nine_of_faithful_generalLinear_cube_det_one
    {F K : Type*} [Field F] [Group K] [Finite K] [IsMulCommutative K]
    (rho : K →* GL (Fin 3) F) (hfaith : Function.Injective rho)
    (hthree : (3 : F) ≠ 0) (hcube : ∀ k : K, k ^ 3 = 1)
    (hdet : ∀ k, Matrix.GeneralLinearGroup.det (rho k) = 1) : Nat.card K ≤ 9 := by
  let E := AlgebraicClosure F
  let f : GL (Fin 3) F →* GL (Fin 3) E := Matrix.GeneralLinearGroup.map (algebraMap F E)
  have hf : Function.Injective f := by
    intro a b h
    apply Units.ext
    ext i j
    apply (algebraMap F E).injective
    exact congrArg (fun c : GL (Fin 3) E => c i j) h
  let sigma : Representation E K (Fin 3 → E) := (generalLinearNatural 3).comp (f.comp rho)
  have hsigma : Function.Injective sigma :=
    (generalLinearNatural_injective 3).comp (hf.comp hfaith)
  have hK : IsPGroup 3 K := fun k => ⟨1, by simpa using hcube k⟩
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  have horder : (Nat.card K : F) ≠ 0 := by
    rw [hn, Nat.cast_pow]
    exact pow_ne_zero n hthree
  have horder' : (Nat.card K : E) ≠ 0 := by
    intro h
    apply horder
    apply (algebraMap F E).injective
    simpa using h
  apply card_le_nine_of_cube_det_one sigma horder'
    (by simp only [Module.finrank_pi, Fintype.card_fin]) hsigma hcube
  intro k
  change LinearMap.det (Matrix.toLin' ((f (rho k)).val)) = 1
  rw [LinearMap.det_toLin']
  change Matrix.det ((algebraMap F E).mapMatrix (rho k).val) = 1
  rw [← RingHom.map_det]
  have hd : (rho k).val.det = 1 := congrArg Units.val (hdet k)
  rw [hd, map_one]

end Representation
