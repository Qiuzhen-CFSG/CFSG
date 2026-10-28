module

public import Theory.Representation.AbelianAllWeights
public import Theory.Representation.GeneralLinearNatural
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.PGroup
public import Theory.GroupTheory.PrimeRankElementary
public import BenderSuzuki.MatrixGroups.Unitary
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.RingTheory.RootsOfUnity.Basic


/-!
# Three-rank of arbitrary ternary orthogonal matrix groups

A commuting group of cubic torsion preserving a nondegenerate bilinear form
and having determinant one in dimension three has at most three elements.
Over an algebraic closure, choose a simultaneous character basis. A nonzero
pairing between the first basis vector and another forces their characters
to be inverse. If that vector pairs with itself, its character has both
square and cube one, hence is trivial. In either case, the determinant-one
identity makes one of the three characters faithful. Its values lie in the
three cube roots of unity.

Entrywise scalar extension preserves the actual matrix action, determinant
and Gram matrix. Applying the resulting bound to every elementary abelian
three-subgroup gives the bound for `primeRank`, via its proved elementary
abelian characterization. The form is arbitrary; neither a standard Gram
matrix nor an identification with PSL₂ is assumed. In particular, the final
bound applies to the full determinant-one isometry carrier `J.specialSubgroup`.

The character-basis argument follows the construction in
`Theory/Representation/CubicTorsionDegreeThree.lean` and
`Theory/Representation/NoncyclicDegreeThree.lean`.
Source: the odd-prime linear-three inspection in Aschbacher–Smith, E.6.18,
printed p.252 (PDF p.263), with the models from Theorem C, printed p.33,
in `refs/quasithin.pdf`.
-/

public section

open Module
open scoped IsMulCommutative
namespace ClassicalOrthogonal.TernaryThreeRank
variable {E K V : Type*} [Field E] [Group K]
  [AddCommGroup V] [Module E V] [IsMulCommutative K]
  [FiniteDimensional E V] [IsAlgClosed E]
open Representation

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


omit [IsAlgClosed E] in
private theorem three_entries_eq_one (v : Fin 3 → E)
    (hp : v 0 * v 1 * v 2 = 1) (i j : Fin 3) (hij : i ≠ j)
    (hi : v i = 1) (hj : v j = 1) : ∀ a, v a = 1 := by
  fin_cases i <;> fin_cases j <;> simp_all <;> intro a <;> fin_cases a <;> simp_all

/-- A faithful determinant-one ternary representation of cubic torsion
preserving a nondegenerate bilinear form has at most three elements. -/
theorem card_le_three_of_cube_det_one_bilin (sigma : Representation E K V)
    (horder : (Nat.card K : E) ≠ 0) (hdim : Module.finrank E V = 3)
    (hfaith : Function.Injective sigma) (hcube : ∀ k : K, k ^ 3 = 1)
    (hdet : ∀ k, LinearMap.det (sigma k) = 1)
    (B : LinearMap.BilinForm E V) (hB : B.Nondegenerate)
    (hpres : ∀ k v u, B (sigma k v) (sigma k u) = B v u) : Nat.card K ≤ 3 := by
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
  obtain ⟨j, hj⟩ : ∃ j, B (b 0) (b j) ≠ 0 := by
    by_contra! hh
    apply b.ne_zero 0
    apply hB.1
    have he : B (b 0) = 0 := b.ext (by simpa using hh)
    intro v
    exact congrArg (fun f : V →ₗ[E] E => f v) he
  have hpair (k : K) : ((w 0).val k : E) * ((w j).val k : E) = 1 := by
    apply mul_right_cancel₀ hj
    have he := hpres k (b 0) (b j)
    simpa only [hw, Units.smul_def, map_smul, LinearMap.smul_apply, smul_eq_mul,
      mul_left_comm, mul_assoc, one_mul] using he
  let i : Fin 3 := if j = 0 then 1 else 0
  let chi : K →* rootsOfUnity 3 E :=
    (w i).val.codRestrict (rootsOfUnity 3 E) (fun k => by
      rw [mem_rootsOfUnity, ← map_pow, hcube, map_one])
  have hchi : Function.Injective chi := by
    apply (injective_iff_map_eq_one chi).mpr
    intro k hk
    have hi : ((w i).val k : E) = 1 :=
      congrArg (fun z : rootsOfUnity 3 E => (z.val : E)) hk
    have hall : ∀ a, ((w a).val k : E) = 1 := by
      by_cases hj0 : j = 0
      · have h0sq : ((w 0).val k : E) ^ 2 = 1 := by
          simpa only [hj0, pow_two] using hpair k
        have h0cube : ((w 0).val k : E) ^ 3 = 1 := by
          have he := congrArg (fun u : Eˣ => (u : E)) ((w 0).val.map_pow k 3)
          simpa [hcube] using he.symm
        have h0 : ((w 0).val k : E) = 1 := by
          simpa only [pow_succ, h0sq, one_mul] using h0cube
        have h1 : ((w 1).val k : E) = 1 := by simpa [i, hj0] using hi
        exact three_entries_eq_one _ (hprod k) 0 1 (by decide) h0 h1
      · have h0 : ((w 0).val k : E) = 1 := by simpa [i, hj0] using hi
        have hj1 : ((w j).val k : E) = 1 := by simpa only [h0, one_mul] using hpair k
        exact three_entries_eq_one _ (hprod k) 0 j (Ne.symm hj0) h0 hj1
    apply hfaith
    rw [map_one]
    apply b.ext
    intro a
    simp only [hw, Units.smul_def, hall, one_smul, Module.End.one_apply]
  exact (Nat.card_le_card_of_injective chi hchi).trans (card_rootsOfUnity E 3)

end ClassicalOrthogonal.TernaryThreeRank

namespace ClassicalOrthogonal.TernaryThreeRank

/-- The bilinear character bound descends from the algebraic closure to
actual invertible matrices over any field in which three is nonzero. -/
theorem card_le_three_of_faithful_generalLinear_cube_orthogonal
    {F K : Type*} [Field F] [Group K] [Finite K] [IsMulCommutative K]
    (rho : K →* GL (Fin 3) F) (hfaith : Function.Injective rho)
    (hthree : (3 : F) ≠ 0) (hcube : ∀ k : K, k ^ 3 = 1)
    (hdet : ∀ k, Matrix.GeneralLinearGroup.det (rho k) = 1)
    (Q : Matrix (Fin 3) (Fin 3) F) (hQ : Q.det ≠ 0)
    (hpres : ∀ k, (rho k).val.transpose * Q * (rho k).val = Q) : Nat.card K ≤ 3 := by
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
  let Q' : Matrix (Fin 3) (Fin 3) E := (algebraMap F E).mapMatrix Q
  have hQ' : Q'.det ≠ 0 := by
    change ((algebraMap F E).mapMatrix Q).det ≠ 0
    rw [← RingHom.map_det]
    exact (map_ne_zero (algebraMap F E)).mpr hQ
  refine card_le_three_of_cube_det_one_bilin sigma horder'
    (by simp only [Module.finrank_pi, Fintype.card_fin]) hsigma hcube
    ?_ Q'.toBilin' (LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' Q' hQ') ?_
  · intro k
    change LinearMap.det (Matrix.toLin' ((f (rho k)).val)) = 1
    rw [LinearMap.det_toLin']
    change Matrix.det ((algebraMap F E).mapMatrix (rho k).val) = 1
    rw [← RingHom.map_det]
    have hd : (rho k).val.det = 1 := congrArg Units.val (hdet k)
    rw [hd, map_one]
  · intro k v u
    have hpres' : (f (rho k)).val.transpose * Q' * (f (rho k)).val = Q' := by
      have he := congrArg (algebraMap F E).mapMatrix (hpres k)
      change ((rho k).val.map (algebraMap F E)).transpose * Q.map (algebraMap F E) *
        (rho k).val.map (algebraMap F E) = Q.map (algebraMap F E)
      simpa only [map_mul, RingHom.mapMatrix_apply, Matrix.transpose_map] using he
    have he := Matrix.toBilin'_comp Q' (f (rho k)).val (f (rho k)).val
    rw [hpres'] at he
    exact congrArg (fun B : LinearMap.BilinForm E (Fin 3 → E) => B v u) he

end ClassicalOrthogonal.TernaryThreeRank

namespace BenderSuzuki.MatrixGroups.HermitianForm

/-- The full special isometry group of an arbitrary nondegenerate ternary
form has three-rank at most one in characteristic different from three. -/
theorem primeRank_three_specialSubgroup_le_one_of_three_ne_zero
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hconj : J.conj = 1) (hthree : (3 : F) ≠ 0) : primeRank 3 J.specialSubgroup ≤ 1 := by
  apply (primeRank_le_iff_elementary_card_le J.specialSubgroup).mpr
  intro A hA
  let := hA
  let rho : A →* GL (Fin 3) F := J.specialSubgroup.subtype.comp A.subtype
  have hrho : Function.Injective rho := Subtype.val_injective.comp Subtype.val_injective
  have hcube : ∀ a : A, a ^ 3 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 3 A)
  have ht (M : Matrix (Fin 3) (Fin 3) F) : J.conjTranspose M = M.transpose := by
    ext i j
    change J.conj (M j i) = M j i
    rw [hconj]
    rfl
  have hm (a : A) := (J.mem_specialSubgroup_iff a.val.val).mp a.val.property
  simpa only [pow_one] using
    ClassicalOrthogonal.TernaryThreeRank.card_le_three_of_faithful_generalLinear_cube_orthogonal
      rho hrho hthree hcube (fun a => (hm a).2) J.form J.form_nondegenerate (fun a => by
        have he := (hm a).1
        simpa only [ht, rho, MonoidHom.comp_apply, Subgroup.subtype_apply] using he)

/-- The prime-field ternary orthogonal bound used in the odd linear-three
involution inspection. The source's oddness hypothesis is retained. -/
theorem primeRank_three_specialSubgroup_le_one
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {p : ℕ} (hp : p.Prime) (_ho : Odd p) (hp3 : p ≠ 3) (hF : Nat.card F = p)
    (hconj : J.conj = 1) : primeRank 3 J.specialSubgroup ≤ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact J.primeRank_three_specialSubgroup_le_one_of_three_ne_zero hconj
    (CharP.cast_ne_zero_of_ne_of_prime F (by decide) hp3)

end BenderSuzuki.MatrixGroups.HermitianForm
