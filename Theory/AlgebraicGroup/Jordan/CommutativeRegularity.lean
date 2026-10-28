module

public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Theory.AlgebraicGroup.Jordan.Components
public import Theory.AlgebraicGroup.RightTranslation.Representation

/-!
# Regularity of the commutative Jordan projection

For a commutative algebraic group over an algebraically closed field, this module proves that
the pointwise semisimple component in the Jordan decomposition varies regularly.

The proof works on the faithful finite-dimensional coordinate right-translation module.
Commuting translations have a simultaneous generalized-eigenspace basis. Genuine common
eigenvectors then realize the corresponding weights as regular matrix coefficients, so the
canonical semisimple projection has regular coordinate functions. This is the geometric input
for the closed-subgroup and direct-product result in `Jordan.Commutative`.

This follows the diagonal-projection argument of Bor1, Chapter 1, Theorem 4.7, while avoiding
maximal-torus theory.
-/

universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

open _root_.Module.End

variable {k : Type u} [Field k] [IsAlgClosed k]

private lemma exists_common_eigenvector_of_commuting_family
    {I V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [Nontrivial V] (f : I → Module.End k V)
    (hcomm : Pairwise fun i j => Commute (f i) (f j)) :
    ∃ (eigenvalue : I → k) (v : V), v ≠ 0 ∧
      ∀ i, f i v = eigenvalue i • v := by
  generalize hdim : Module.finrank k V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
      choose eigenvalue heigen using fun i => Module.End.exists_eigenvalue (f i)
      by_cases hall : ∀ i, (f i).eigenspace (eigenvalue i) = ⊤
      · obtain ⟨v, hv⟩ := exists_ne (0 : V)
        refine ⟨eigenvalue, v, hv, ?_⟩
        intro i
        exact Module.End.mem_eigenspace_iff.mp (by rw [hall i]; trivial)
      · obtain ⟨i, hi⟩ := not_forall.mp hall
        let E : Submodule k V := (f i).eigenspace (eigenvalue i)
        have hEne : E ≠ ⊥ := heigen i
        letI : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hEne
        have hEfinrank : Module.finrank k E < n := by
          rw [← hdim]
          exact Submodule.finrank_lt hi
        have hstable (j : I) : Set.MapsTo (f j) E E := by
          dsimp [E]
          by_cases hij : i = j
          · subst j
            exact Module.End.mapsTo_genEigenspace_of_comm
              (Commute.refl _) (eigenvalue i) 1
          · exact Module.End.mapsTo_genEigenspace_of_comm
              (hcomm hij) (eigenvalue i) 1
        let fE : I → Module.End k E := fun j => (f j).restrict (hstable j)
        have hcommE : Pairwise fun a b => Commute (fE a) (fE b) := by
          intro a b hab
          apply LinearMap.ext
          intro x
          apply Subtype.ext
          exact LinearMap.congr_fun (hcomm hab).eq x.1
        obtain ⟨eigenvalueE, v, hv, hveigen⟩ :=
          ih (Module.finrank k E) hEfinrank fE hcommE rfl
        refine ⟨eigenvalueE, (v : V), ?_, ?_⟩
        · exact fun hvzero => hv (Subtype.ext hvzero)
        · intro j
          exact congrArg Subtype.val (hveigen j)

private lemma exists_common_eigenvector_in_jointMaxGenEigenspace
    {I V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : I → Module.End k V) (hcomm : ∀ i j, Commute (f i) (f j))
    (weight : I → k)
    (hne : (⨅ i, (f i).maxGenEigenspace (weight i)) ≠ ⊥) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, f i v = weight i • v := by
  let W : Submodule k V := ⨅ i, (f i).maxGenEigenspace (weight i)
  let _ : Module.Finite k W :=
    Module.Finite.of_injective W.subtype W.injective_subtype
  letI : Module.Free k W := Module.Free.of_divisionRing k W
  letI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
  have hstable (i : I) : Set.MapsTo (f i) W W := by
    intro x hx
    change x ∈ ⨅ j, (f j).maxGenEigenspace (weight j) at hx
    change f i x ∈ ⨅ j, (f j).maxGenEigenspace (weight j)
    rw [Submodule.mem_iInf] at hx ⊢
    intro j
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) (weight j) (hx j)
  let fW : I → Module.End k W := fun i => (f i).restrict (hstable i)
  have hcommW : Pairwise fun i j => Commute (fW i) (fW j) := by
    intro i j _
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (hcomm i j).eq x.1
  obtain ⟨eigenvalue, v, hv, hveigen⟩ :=
    exists_common_eigenvector_of_commuting_family fW hcommW
  have heq (i : I) : eigenvalue i = weight i := by
    by_contra hneigen
    have hvWeight : (v : V) ∈ (f i).maxGenEigenspace (weight i) :=
      (by
        have hall : ∀ j, (v : V) ∈ (f j).maxGenEigenspace (weight j) := by
          simpa only [W, Submodule.mem_iInf] using v.property
        exact hall i)
    have hvEigen : (v : V) ∈ (f i).maxGenEigenspace (eigenvalue i) := by
      apply Module.End.eigenspace_le_maxGenEigenspace
      exact Module.End.mem_eigenspace_iff.mpr (congrArg Subtype.val (hveigen i))
    have hvzero : (v : V) = 0 := by
      rw [← Submodule.mem_bot (R := k),
        ← (Module.End.disjoint_genEigenspace (f i) hneigen ⊤ ⊤).eq_bot]
      exact ⟨hvEigen, hvWeight⟩
    exact hv (Subtype.ext hvzero)
  refine ⟨(v : V), fun hvzero => hv (Subtype.ext hvzero), ?_⟩
  intro i
  have hi := congrArg Subtype.val (hveigen i)
  change f i (v : V) = eigenvalue i • (v : V) at hi
  rw [heq i] at hi
  exact hi

omit [IsAlgClosed k] in
private lemma finiteDimensional_isLocallyFinite
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (T : Module.End k V) :
    Theory.AlgebraicGroup.Module.End.IsLocallyFinite T := by
  intro x
  exact ⟨⊤, inferInstance, fun _ _ => Submodule.mem_top, Submodule.mem_top⟩

private lemma locallyFinite_semisimplePart_apply_of_mem_maxGenEigenspace
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {T : Module.End k V}
    (hT : Theory.AlgebraicGroup.Module.End.IsLocallyFinite T)
    (mu : k) (x : V)
    (hx : x ∈ T.maxGenEigenspace mu) :
    hT.semisimplePart x = mu • x := by
  let P : Submodule k V := ⊤
  have hP : P ∈ T.invtSubmodule := fun _ _ => Submodule.mem_top
  let d := Theory.AlgebraicGroup.Module.End.invariantJordanDecomposition T P hP
  have hxP : (⟨x, Submodule.mem_top⟩ : P) ∈
      (show Module.End k P from T.restrict (p := P) (q := P) hP).maxGenEigenspace mu := by
    rw [Module.End.mem_maxGenEigenspace] at hx ⊢
    obtain ⟨n, hn⟩ := hx
    refine ⟨n, ?_⟩
    have hsubP : P ∈ (T - mu • 1 : Module.End k V).invtSubmodule := by
      intro y _
      exact Submodule.mem_top
    have hre :
        (T.restrict (p := P) (q := P) hP - mu • 1 : Module.End k P) =
          (T - mu • 1 : Module.End k V).restrict
            (p := P) (q := P) hsubP := by
      ext y
      rfl
    rw [hre, Module.End.pow_restrict n hsubP]
    apply Subtype.ext
    exact hn
  have hs := d.toJordanPair.semisimplePart_apply_of_mem_maxGenEigenspace
    mu (⟨x, Submodule.mem_top⟩ : P) hxP
  have hcanonical := hT.semisimpleValue_eq P hP x Submodule.mem_top
  change hT.semisimplePart x = mu • x
  rw [hT.semisimplePart_apply, hcanonical]
  exact congrArg Subtype.val hs

omit [IsAlgClosed k] in
private lemma coordinateTranslation_isLocallyFinite
    (G : Variety k) [AlgebraicGroup G] (g : Variety.Point G) :
    Theory.AlgebraicGroup.Module.End.IsLocallyFinite
      (rightTranslationOnCoordinateSubmodule G g) := by
  let _ : Module.Finite k (coordinateTranslationSubmodule G) :=
    coordinateTranslationSubmodule_finite G
  exact finiteDimensional_isLocallyFinite
    (rightTranslationOnCoordinateSubmodule G g)

private noncomputable def coordinateTranslationSemisimplePart
    (G : Variety k) [AlgebraicGroup G] (g : Variety.Point G) :
    Module.End k (coordinateTranslationSubmodule G) :=
  (coordinateTranslation_isLocallyFinite G g).semisimplePart

private lemma coordinateTranslationSemisimplePart_eq
    (G : Variety k) [AlgebraicGroup G] (g : Variety.Point G) :
    coordinateTranslationSemisimplePart G g =
      (coordinateTranslation_isLocallyFinite G g).semisimplePart := by
  rfl

private lemma exists_coordinateTranslationBasis_semisimplePart_diagonal
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) :
    ∃ (b : Module.Basis
        (Fin (Module.finrank k (coordinateTranslationSubmodule G))) k
        (coordinateTranslationSubmodule G))
      (weight : Fin (Module.finrank k (coordinateTranslationSubmodule G)) →
        Variety.Point G → k),
      (∀ g i,
        coordinateTranslationSemisimplePart G g (b i) =
          weight i g • b i) ∧
      ∀ i g, b i ∈
        (rightTranslationOnCoordinateSubmodule G g).maxGenEigenspace
          (weight i g) := by
  classical
  let _ : Module.Finite k (coordinateTranslationSubmodule G) :=
    coordinateTranslationSubmodule_finite G
  rw [isMulCommutative_iff] at hcomm
  let R : Variety.Point G → Module.End k (coordinateTranslationSubmodule G) :=
    rightTranslationOnCoordinateSubmodule G
  have hRcomm : Pairwise fun g h => Commute (R g) (R h) := by
    intro g h _
    change R g * R h = R h * R g
    rw [← rightTranslationOnCoordinateSubmodule_mul,
      ← rightTranslationOnCoordinateSubmodule_mul, hcomm g h]
  have hmaps : ∀ g h mu,
      Set.MapsTo (R g) ((R h).maxGenEigenspace mu)
        ((R h).maxGenEigenspace mu) := by
    intro g h mu
    by_cases hgh : h = g
    · subst h
      exact Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) mu
    · exact Module.End.mapsTo_maxGenEigenspace_of_comm (hRcomm hgh) mu
  have htop : ⨆ weight : Variety.Point G → k,
      ⨅ g, (R g).maxGenEigenspace (weight g) = ⊤ := by
    exact Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo R hmaps
      (fun g => Module.End.iSup_maxGenEigenspace_eq_top (R g))
  have hindep : iSupIndep fun weight : Variety.Point G → k =>
      ⨅ g, (R g).maxGenEigenspace (weight g) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo R hmaps
  let hInternal := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    hindep htop
  let W (weight : Variety.Point G → k) :
      Submodule k (coordinateTranslationSubmodule G) :=
    ⨅ g, (R g).maxGenEigenspace (weight g)
  let bW (weight : Variety.Point G → k) :
      Module.Basis (Fin (Module.finrank k (W weight))) k (W weight) := by
    letI : Module.Free k (W weight) := Module.Free.of_divisionRing k (W weight)
    let _ : Module.Finite k (W weight) :=
      Module.Finite.of_injective (W weight).subtype (W weight).injective_subtype
    exact Module.finBasis k (W weight)
  let I := (weight : Variety.Point G → k) ×
    Fin (Module.finrank k (W weight))
  let v : Module.Basis I k (coordinateTranslationSubmodule G) :=
    hInternal.collectedBasis bW
  letI : Fintype I := FiniteDimensional.fintypeBasisIndex v
  have hcard : Fintype.card I =
      Module.finrank k (coordinateTranslationSubmodule G) :=
    (Module.finrank_eq_card_basis v).symm
  let e : I ≃ Fin (Module.finrank k (coordinateTranslationSubmodule G)) :=
    Fintype.equivFinOfCardEq hcard
  let b := v.reindex e
  let weight : Fin (Module.finrank k (coordinateTranslationSubmodule G)) →
      Variety.Point G → k := fun i => (e.symm i).1
  have hmem (i) (g) : v (e.symm i) ∈
      (R g).maxGenEigenspace ((e.symm i).1 g) :=
    (by
      have hall : ∀ h, v (e.symm i) ∈
          (R h).maxGenEigenspace ((e.symm i).1 h) := by
        simpa only [Submodule.mem_iInf] using
          (hInternal.collectedBasis_mem
            bW (e.symm i))
      exact hall g)
  refine ⟨b, weight, ?_, ?_⟩
  · intro g i
    rw [coordinateTranslationSemisimplePart_eq]
    change (coordinateTranslation_isLocallyFinite G g).semisimplePart (b i) =
      weight i g • b i
    simpa only [b, weight, Module.Basis.reindex_apply] using
      locallyFinite_semisimplePart_apply_of_mem_maxGenEigenspace
        (coordinateTranslation_isLocallyFinite G g)
        ((e.symm i).1 g) (v (e.symm i)) (hmem i g)
  · intro i g
    simpa only [b, weight, Module.Basis.reindex_apply] using hmem i g

private lemma coordinateTranslationSemisimplePart_eq_jordan
    (G : Variety k) [AlgebraicGroup G] (g : Variety.Point G) :
    coordinateTranslationSemisimplePart G g =
      rightTranslationOnCoordinateSubmodule G
        (jordanDecomposition g).semisimplePart := by
  let W := coordinateTranslationSubmodule G
  let R : Module.End k W := rightTranslationOnCoordinateSubmodule G g
  let S : Module.End k (Variety.PolynomialFunction G) :=
    rightTranslationPullback G g
  let L : W →ₗ[k] Variety.PolynomialFunction G := W.subtype
  have hinter : L.comp R = S.comp L := by
    apply LinearMap.ext
    intro f
    exact rightTranslationOnCoordinateSubmodule_apply G g f
  have hsemi := (coordinateTranslation_isLocallyFinite G g).semisimplePart_semiconj
    (rightTranslationPullback_locallyFinite G g) L hinter
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  have hf := LinearMap.congr_fun hsemi f
  change L (coordinateTranslationSemisimplePart G g f) =
    Theory.AlgebraicGroup.Module.End.IsLocallyFinite.semisimplePart
      (rightTranslationPullback_locallyFinite G g) (L f) at hf
  rw [(jordanDecomposition g).semisimplePart_pullback] at hf
  exact hf

private noncomputable def coordinateTranslationGeneralMatrixCoefficient
    (G : Variety k) [AlgebraicGroup G]
    (b : Module.Basis
      (Fin (Module.finrank k (coordinateTranslationSubmodule G))) k
      (coordinateTranslationSubmodule G))
    (K : Module.Dual k (coordinateTranslationSubmodule G))
    (v : coordinateTranslationSubmodule G) : G.PolynomialFunction :=
  ∑ j, b.repr v j •
    ∑ i, K (b i) • coordinateTranslationMatrixCoefficient G b i j

omit [IsAlgClosed k] in
private lemma coordinateTranslationGeneralMatrixCoefficient_apply
    (G : Variety k) [AlgebraicGroup G]
    (b : Module.Basis
      (Fin (Module.finrank k (coordinateTranslationSubmodule G))) k
      (coordinateTranslationSubmodule G))
    (K : Module.Dual k (coordinateTranslationSubmodule G))
    (v : coordinateTranslationSubmodule G) (g : Variety.Point G) :
    coordinateTranslationGeneralMatrixCoefficient G b K v g =
      K (rightTranslationOnCoordinateSubmodule G g v) := by
  let _ : Module.Finite k (coordinateTranslationSubmodule G) :=
    coordinateTranslationSubmodule_finite G
  have hK (x : coordinateTranslationSubmodule G) :
      ∑ i, K (b i) * b.repr x i = K x := by
    calc
      ∑ i, K (b i) * b.repr x i =
          ∑ i, b.repr x i * K (b i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_comm]
      _ = K (∑ i, b.repr x i • b i) := by
        rw [map_sum]
        simp [smul_eq_mul]
      _ = K x := by rw [b.sum_repr]
  have hsum (j) :
      (∑ i, K (b i) • coordinateTranslationMatrixCoefficient G b i j) g =
        ∑ i, K (b i) * coordinateTranslationMatrixCoefficient G b i j g := by
    change polynomialFunctionEvalAddHom G g
      (∑ i, K (b i) • coordinateTranslationMatrixCoefficient G b i j) = _
    rw [map_sum]
    simp [polynomialFunction_smul_apply]
  change polynomialFunctionEvalAddHom G g
    (∑ j, b.repr v j •
      ∑ i, K (b i) • coordinateTranslationMatrixCoefficient G b i j) = _
  rw [map_sum]
  simp_rw [polynomialFunctionEvalAddHom_apply,
    polynomialFunction_smul_apply, hsum]
  simp_rw [coordinateTranslationMatrixCoefficient_apply, hK]
  calc
    ∑ j, b.repr v j * K (rightTranslationOnCoordinateSubmodule G g (b j)) =
        K (∑ j, b.repr v j • rightTranslationOnCoordinateSubmodule G g (b j)) := by
      rw [map_sum]
      simp [smul_eq_mul]
    _ = K (rightTranslationOnCoordinateSubmodule G g
        (∑ j, b.repr v j • b j)) := by
      congr 1
      rw [map_sum]
      simp
    _ = K (rightTranslationOnCoordinateSubmodule G g v) := by
      rw [b.sum_repr]

private lemma exists_coordinateTranslationBasis_regular_weights
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) :
    ∃ (b : Module.Basis
        (Fin (Module.finrank k (coordinateTranslationSubmodule G))) k
        (coordinateTranslationSubmodule G))
      (weight : Fin (Module.finrank k (coordinateTranslationSubmodule G)) →
        Variety.Point G → k),
      (∀ g i, coordinateTranslationSemisimplePart G g (b i) =
        weight i g • b i) ∧
      ∀ i, ∃ q : G.PolynomialFunction, ∀ g, q g = weight i g := by
  classical
  let _ : Module.Finite k (coordinateTranslationSubmodule G) :=
    coordinateTranslationSubmodule_finite G
  obtain ⟨b, weight, hdiagonal, hmaxGen⟩ :=
    exists_coordinateTranslationBasis_semisimplePart_diagonal G hcomm
  refine ⟨b, weight, hdiagonal, ?_⟩
  rw [isMulCommutative_iff] at hcomm
  let R : Variety.Point G → Module.End k (coordinateTranslationSubmodule G) :=
    rightTranslationOnCoordinateSubmodule G
  have hRcomm : ∀ g h, Commute (R g) (R h) := by
    intro g h
    change R g * R h = R h * R g
    rw [← rightTranslationOnCoordinateSubmodule_mul,
      ← rightTranslationOnCoordinateSubmodule_mul, hcomm g h]
  intro i
  have hjointNe : (⨅ g, (R g).maxGenEigenspace (weight i g)) ≠ ⊥ := by
    intro hbot
    have hmem : b i ∈ ⨅ g, (R g).maxGenEigenspace (weight i g) := by
      rw [Submodule.mem_iInf]
      exact hmaxGen i
    rw [hbot] at hmem
    exact (b.ne_zero i) (show b i = 0 by simpa using hmem)
  obtain ⟨v, hv, hveigen⟩ :=
    exists_common_eigenvector_in_jointMaxGenEigenspace R hRcomm (weight i) hjointNe
  obtain ⟨K, hK⟩ := Module.Projective.exists_dual_eq_one k hv
  refine ⟨coordinateTranslationGeneralMatrixCoefficient G b K v, ?_⟩
  intro g
  rw [coordinateTranslationGeneralMatrixCoefficient_apply, hveigen g, map_smul, hK]
  simp

private noncomputable def commutativeSemisimpleComponentVarietyMorphism
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) : Variety.Morphism G G where
  toFun := fun g => (jordanDecomposition g).semisimplePart
  regular := by
    classical
    obtain ⟨b, weight, hdiagonal, hregular⟩ :=
      exists_coordinateTranslationBasis_regular_weights G hcomm
    choose q hq using hregular
    intro c
    let W := coordinateTranslationSubmodule G
    let evaluationOne : Module.Dual k W :=
      polynomialFunctionSubspaceEvaluation G W 1
    let v : W := coordinateTranslationCoordinateVector G c
    let f : G.PolynomialFunction :=
      ∑ i, (b.repr v i * evaluationOne (b i)) • q i
    rcases f.representedBy with ⟨p, hp⟩
    refine ⟨p, fun g => ?_⟩
    rw [← hp g]
    calc
      (jordanDecomposition g).semisimplePart.val c =
          evaluationOne
            (rightTranslationOnCoordinateSubmodule G
              (jordanDecomposition g).semisimplePart v) := by
        change (jordanDecomposition g).semisimplePart.val c =
          (rightTranslationOnCoordinateSubmodule G
            (jordanDecomposition g).semisimplePart v).val 1
        rw [rightTranslationOnCoordinateSubmodule_apply,
          rightTranslationPullback_apply, one_mul]
        simp [v, coordinateTranslationCoordinateVector,
          coordinatePolynomialFunction, Variety.PolynomialFunction.ofPolynomial,
          Variety.PolynomialFunction.toFun, evalPolynomial]
      _ = evaluationOne (coordinateTranslationSemisimplePart G g v) := by
        rw [coordinateTranslationSemisimplePart_eq_jordan]
      _ = evaluationOne
          (coordinateTranslationSemisimplePart G g
            (∑ i, b.repr v i • b i)) := by rw [b.sum_repr]
      _ = ∑ i, (b.repr v i * evaluationOne (b i)) * weight i g := by
        rw [map_sum, map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul, map_smul, hdiagonal g i]
        simp [mul_comm, mul_left_comm]
      _ = f g := by
        change _ = polynomialFunctionEvalAddHom G g
          (∑ i, (b.repr v i * evaluationOne (b i)) • q i)
        rw [map_sum]
        simp_rw [polynomialFunctionEvalAddHom_apply,
          polynomialFunction_smul_apply, hq]

/-- In a commutative algebraic group, every coordinate of the semisimple Jordan component is
a polynomial function of the original point. -/
public theorem commutativeSemisimpleComponent_regular
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) :
    ∀ c : G.Coordinates, ∃ p : MvPolynomial G.Coordinates k,
      ∀ g : Variety.Point G,
        (jordanDecomposition g).semisimplePart.val c = evalPolynomial g.val p :=
  (commutativeSemisimpleComponentVarietyMorphism G hcomm).regular


end Theory.AlgebraicGroup
