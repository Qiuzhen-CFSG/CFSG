module

public import Theory.AlgebraicGroup.Bor1.Differential
public import Theory.AlgebraicGroup.CoordinateRing.FiniteTranslate
public import Theory.AlgebraicGroup.Jordan.Conjugation
public import Theory.AlgebraicGroup.Representations.Semisimple
public import Theory.AlgebraicGroup.Tori.DiagonalizableClosedSubgroupSemisimple

/-!
# Semisimplicity of tangent conjugation

A semisimple point of an algebraic group acts semisimply by conjugation on the
identity tangent space.  To transfer semisimplicity from the coordinate ring,
we choose a finite two-sided-translation-stable coordinate subspace containing
the affine coordinates.  Its conjugation restriction is semisimple, hence so
is its dual.  Restriction embeds identity-point derivations equivariantly into
that dual, because the chosen subspace contains every coordinate function.

Consequently every point of a diagonalizable closed subgroup induces a
semisimple tangent conjugation operator.  This supplies the representation
input used in the fixed-tangent argument for Bor1, Chapter 3, Proposition 9.6,
whose source appears in `refs/KGroup/Bor1/Chapter3.tex:733`, without using
Borel or maximal-torus results.
-/

universe u v w

namespace Theory.AlgebraicGroup

open Bor1

variable {k : Type u} [Field k] [IsAlgClosed k]

private lemma isSemisimple_dualMap
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (T : Module.End k V) (hT : Module.End.IsSemisimple T) :
    Module.End.IsSemisimple T.dualMap := by
  classical
  let Td : Module.End k (Module.Dual k V) := T.dualMap
  obtain ⟨b, mu, hb⟩ :=
    Module.End.IsSemisimple.exists_fin_eigenbasis T hT
  have heigen : ∀ i, Td (b.dualBasis i) = mu i • b.dualBasis i := by
    intro i
    apply LinearMap.ext_on b.span_eq
    rintro _ ⟨j, rfl⟩
    by_cases hji : j = i
    · subst j
      simp [Td, LinearMap.dualMap_apply, hb]
    · simp [Td, LinearMap.dualMap_apply, hb, Ne.symm hji]
  let eigenvalues : Finset k := Finset.univ.image mu
  let p : Polynomial k :=
    ∏ a ∈ eigenvalues, (Polynomial.X - Polynomial.C a)
  have hpsep : p.Separable := by
    apply Polynomial.separable_prod_X_sub_C_iff'.2
    intro x _hx y _hy hxy
    exact hxy
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hpsep.squarefree
  apply LinearMap.ext_on b.dualBasis.span_eq
  rintro _ ⟨i, rfl⟩
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul (heigen i)]
  have hmem : mu i ∈ eigenvalues := by
    simp [eigenvalues]
  have heval : p.eval (mu i) = 0 := by
    dsimp [p]
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero hmem (by simp)
  simp [heval]

omit [IsAlgClosed k] in
private lemma isSemisimple_of_injective_semiconj
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (T : Module.End k V) (U : Module.End k W) (L : V →ₗ[k] W)
    (hL : Function.Injective L) (hTU : L.comp T = U.comp L)
    (hU : Module.End.IsSemisimple U) : Module.End.IsSemisimple T := by
  let R : Submodule k W := LinearMap.range L
  have hR : R ∈ U.invtSubmodule := by
    rintro _ ⟨x, rfl⟩
    exact ⟨T x, LinearMap.congr_fun hTU x⟩
  let UR : Module.End k R := U.restrict hR
  have hUR : Module.End.IsSemisimple UR := hU.restrict hR
  let e : V ≃ₗ[k] R := LinearEquiv.ofInjective L hL
  have he : e.toLinearMap.comp T = UR.comp e.toLinearMap := by
    ext x
    exact LinearMap.congr_fun hTU x
  exact (e.isSemisimple_iff T UR he).mpr hUR

/-- A semisimple group point acts semisimply by conjugation on the tangent
space at the identity. -/
public theorem IsSemisimpleElement.identityTangentConjugationLinearMap_isSemisimple
    {G : Variety k} [AlgebraicGroup G] {g : Variety.Point G}
    (hg : IsSemisimpleElement G g) :
    Module.End.IsSemisimple (identityTangentConjugationLinearMap G g) := by
  classical
  let q : G.Coordinates → G.PolynomialFunction := fun i =>
    Variety.PolynomialFunction.ofPolynomial G (MvPolynomial.X i)
  let t : Finset G.PolynomialFunction := Finset.univ.image q
  have hexists :=
    AlgebraicGroup.exists_finite_twoSidedTranslate_stableSubmodule G t
  let P := Classical.choose hexists
  have hPspec := Classical.choose_spec hexists
  have hPfg : P.FG := hPspec.1
  have htP : (↑t : Set G.PolynomialFunction) ⊆ P := hPspec.2.1
  have hleftP := hPspec.2.2.1
  have hrightP := hPspec.2.2.2
  let _ : Module.Finite k P := Module.Finite.iff_fg.mpr hPfg
  let T : Module.End k G.PolynomialFunction :=
    (AlgebraicGroup.conjugationByMorphism G g).pullbackAlgHom.toLinearMap
  have hTapply (p : G.PolynomialFunction) :
      T p = leftTranslationPullback G g
        (rightTranslationPullback G g⁻¹ p) := by
    apply Variety.PolynomialFunction.ext
    intro x
    rfl
  have hTP : P ∈ T.invtSubmodule := by
    intro p hp
    change T p ∈ P
    rw [hTapply]
    exact hleftP g _ (hrightP g⁻¹ p hp)
  have hTsem : Module.End.IsSemisimple (T.restrict hTP) := by
    have hconj := conjugationBy_semisimpleElement_isSemisimple g hg
    exact hconj P hTP inferInstance
  have hdual : Module.End.IsSemisimple (T.restrict hTP).dualMap :=
    isSemisimple_dualMap (T.restrict hTP) hTsem
  let L : IdentityPointDerivation G →ₗ[k] Module.Dual k P :=
    { toFun := fun D => D.toLinearMap.comp P.subtype
      map_add' := by
        intro D E
        ext p
        rfl
      map_smul' := by
        intro c D
        ext p
        rfl }
  have hL : Function.Injective L := by
    intro D E hDE
    apply coordinateTangentMap_injective G
    funext i
    have hqi : q i ∈ P := by
      apply htP
      simp [t]
    have h := LinearMap.congr_fun hDE ⟨q i, hqi⟩
    exact h
  have hsemiconj :
      L.comp (identityTangentConjugationLinearMap G g) =
        (T.restrict hTP).dualMap.comp L := by
    ext D p
    exact identityTangentConjugationLinearMap_apply G g D p
  exact isSemisimple_of_injective_semiconj
    (identityTangentConjugationLinearMap G g)
    (T.restrict hTP).dualMap L hL hsemiconj hdual

/-- Every point of a diagonalizable closed subgroup induces a semisimple
conjugation operator on the ambient identity tangent space. -/
public theorem IsDiagonalizableClosedSubgroup.identityTangentConjugationLinearMap_isSemisimple
    {G : Variety k} [AlgebraicGroup G] (S : ClosedSubgroup G)
    (hS : IsDiagonalizableClosedSubgroup S) :
    ∀ s : Variety.Point S.carrierVariety,
      Module.End.IsSemisimple
        (identityTangentConjugationLinearMap G (S.includePoint s)) := by
  intro s
  apply IsSemisimpleElement.identityTangentConjugationLinearMap_isSemisimple
  exact morphism_preserves_semisimpleElement S.inclusion s (hS.all_semisimple s)

end Theory.AlgebraicGroup
