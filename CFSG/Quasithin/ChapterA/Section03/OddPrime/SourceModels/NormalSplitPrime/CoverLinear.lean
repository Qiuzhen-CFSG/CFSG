module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverInner
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.SpecificGroups.SU3.CentralCubeLocalRelocation.ScalarRoot
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank.MatrixWitnesses
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Mathlib.FieldTheory.KummerExtension
public import Theory.LinearAlgebra.SplitSeparableEigenbasis
public import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Excluding inner outside cubics on the actual SL₃ cover

A determinant-one matrix with scalar cube z has a cube root of z in the
coefficient field. For a nonidentity central cube, z itself is a primitive
cube root of unity. Hence X³−z splits with distinct roots. Its coprime
kernel decomposition gives an eigenbasis for the original matrix. The
diagonal cubic and scalar cubic in that basis form an elementary nine
inside the centralizer of this particular implementer.

Together with CoverInner's order-nine extraction, this contradicts the
ambient rank bound for an outside cubic acting inner. The statement holds
for every finite coefficient field, and never replaces SL₃ by PSL₃.
CoverSieve applies it to the actual two-core component and outside actor.
Source: Aschbacher–Smith A.3.18, printed p.52; the scalar-root argument and
split-kernel basis construction reuse the indicated intrinsic modules.
-/

@[expose] public noncomputable section
open Subgroup Matrix Theory.GroupTheory Polynomial
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverInner

/-- A determinant-one ternary matrix with nontrivial central cube has an
actual eigenbasis over its original coefficient field. -/
theorem linear_eigenbasis {F : Type*} [Field F] (y : SL(3,F))
    (hc : y ^ 3 ∈ center SL(3,F)) (hne : y ^ 3 ≠ 1) :
    ∃ (P : GL (Fin 3) F) (d : Fin 3 → F),
      P.val * Matrix.diagonal d * P⁻¹.val = y.val := by
  classical
  obtain ⟨z,hz,hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hz3 : z^3=1 := by simpa using hz
  have hz1 : z ≠ 1 := by
    intro he
    apply hne
    apply Subtype.ext
    rw [←hscalar,he]
    simp
  have hz0 : z ≠ 0 := by intro he; simp [he] at hz3
  have hprim : IsPrimitiveRoot z 3 := IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hz3 hz1)
  have hcube : y.val ^ 3 = Matrix.scalar (Fin 3) z := hscalar.symm
  obtain ⟨a,ha⟩ := Matrix.exists_cube_root_of_det_one_cube_scalar y.val y.property z hcube
  have ha0 : a ≠ 0 := by intro he; rw [he,zero_pow (by decide)] at ha; exact hz0 ha.symm
  let p : F[X] := X^3-C z
  have hs : p.Splits := X_pow_sub_C_splits_of_isPrimitiveRoot hprim ha
  have hp : p.Separable := by
    rw [show p = ∏ i ∈ Finset.range 3, (X-C (z^i*a)) from
      X_pow_sub_C_eq_prod hprim (by decide) ha]
    apply separable_prod_X_sub_C_iff'.mpr
    intro i hi j hj he
    exact hprim.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
      (mul_right_cancel₀ ha0 he)
  let f := Matrix.toLin' y.val
  have heval : aeval f p = 0 := by
    have he : aeval y.val p = 0 := by
      simp only [p,map_sub,map_pow,aeval_X,aeval_C]
      rw [hcube]
      simp [Matrix.algebraMap_eq_diagonal,Matrix.scalar_apply]
    change aeval (Matrix.toLinAlgEquiv' (R := F) y.val) p = 0
    rw [aeval_algHom_apply,he,map_zero]
  obtain ⟨b,μ,hb⟩ := Module.End.exists_eigenbasis_of_split_separable_annihilator f p (monic_X_pow_sub_C _ (by decide)) hs hp heval
  have hdim : Module.finrank F (Fin 3 → F)=3 := by simp
  let b' := b.reindex (finCongr hdim)
  let d : Fin 3 → F := fun i => μ ((finCongr hdim).symm i)
  have hd : LinearMap.toMatrix b' b' f = Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [LinearMap.toMatrix_apply,b',d,Module.Basis.reindex_apply,hb]
    · simp [LinearMap.toMatrix_apply,b',d,Module.Basis.reindex_apply,hb,
        hij]
  let s := Pi.basisFun F (Fin 3)
  let P : GL (Fin 3) F := ⟨s.toMatrix b',b'.toMatrix s,
    s.toMatrix_mul_toMatrix_flip b',b'.toMatrix_mul_toMatrix_flip s⟩
  refine ⟨P,d,?_⟩
  change s.toMatrix b' * Matrix.diagonal d * b'.toMatrix s = y.val
  rw [←hd,basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  simp [s,f,LinearMap.toMatrix_eq_toMatrix']


/-- The two actual cubic torus directions commute with the given matrix.
This is a fixed centralizer rank statement, before any projective quotient. -/
theorem linear_centralizer_rank {F : Type*} [Field F] [Finite F] (y : SL(3,F))
    (hc : y ^ 3 ∈ center SL(3,F)) (hne : y ^ 3 ≠ 1) :
    2 ≤ primeRank 3 (centralizer ({y} : Set SL(3,F))) := by
  classical
  obtain ⟨z,hz,hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hz3 : z^3=1 := by simpa using hz
  have hz1 : z ≠ 1 := by
    intro he
    apply hne
    apply Subtype.ext
    rw [←hscalar,he]
    simp
  obtain ⟨P,d,hP⟩ := linear_eigenbasis y hc hne
  let e := Matrix.PSL3.OuterSolvable.linearConjSL F P⁻¹
  let y' := e y
  have hy' : y'.val = Matrix.diagonal d := by
    have hh := congrArg Units.val (Matrix.PSL3.OuterSolvable.linearConjSL_toGL F P⁻¹ y)
    change y'.val = P⁻¹.val * y.val * P.val at hh
    rw [hh,←hP]
    have hcancel : P⁻¹.val * P.val = 1 := congrArg Units.val (inv_mul_cancel P)
    rw [←mul_assoc,←mul_assoc,hcancel,one_mul,mul_assoc,hcancel,mul_one]
  let D := Theory.SpecificGroups.SignedThreeCubicRank.diagonal z hz3
  let Z := Theory.SpecificGroups.SignedThreeCubicRank.scalar z hz3
  have hD : D ∈ centralizer ({y'} : Set SL(3,F)) := by
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    change D.val * y'.val = y'.val * D.val
    rw [hy']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D,Theory.SpecificGroups.SignedThreeCubicRank.diagonal,
        Matrix.mul_diagonal,Matrix.diagonal_mul,mul_comm]
  have hZ : Z ∈ centralizer ({y'} : Set SL(3,F)) := by
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    change Z.val * y'.val = y'.val * Z.val
    ext i j
    simp [Z,Theory.SpecificGroups.SignedThreeCubicRank.scalar,Matrix.mul_diagonal,
      Matrix.diagonal_mul,mul_comm]
  let f := SpecialLinearGroup.toGL.comp (centralizer ({y'} : Set SL(3,F))).subtype
  have hh := Theory.SpecificGroups.SignedThreeCubicRank.special_rank z hz3 hz1 f
    (SpecialLinearGroup.toGL_injective.comp Subtype.val_injective) ⟨D,hD⟩ ⟨Z,hZ⟩ rfl rfl
  rwa [← primeRank_congr 3 (CentralizerSmallKernelTransport.centralizerEquiv e y)] at hh

/-- No outside cubic can act inner on an actual SL₃ cover in rank two. -/
theorem not_inner_of_linear_cover {G F : Type*} [Group G] [Finite G]
    [Field F] [Finite F] (K : Subgroup G) [K.Normal]
    (hz : Nat.card (center K) = 3) (hrK : 1 < primeRank 3 K)
    (hr : primeRank 3 G ≤ 2) (e : K ≃* SL(3,F))
    (x : G) (hx : orderOf x = 3) (hxK : x ∉ K) :
    (MulAut.conjNormal x : MulAut K) ∉ MulAut.innerSubgroup K := by
  intro hi
  obtain ⟨y,_,_,hyc,hy3,hbound⟩ := exists_nine_implementer K hz hrK hr x hx hxK hi
  have hc : (e y)^3 ∈ center SL(3,F) := by
    apply mem_center_iff.mpr
    intro w
    obtain ⟨v,rfl⟩ := e.surjective w
    simpa only [map_mul,map_pow] using congrArg e (mem_center_iff.mp hyc v)
  have hn : (e y)^3 ≠ 1 := by
    intro he
    apply hy3
    apply e.injective
    rwa [map_pow,map_one]
  have hh := linear_centralizer_rank (e y) hc hn
  rw [←primeRank_congr 3 (CentralizerSmallKernelTransport.centralizerEquiv e y)] at hh
  omega

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverInner
