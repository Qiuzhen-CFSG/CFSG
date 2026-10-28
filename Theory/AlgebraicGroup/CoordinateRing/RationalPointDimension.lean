module

public import Mathlib.FieldTheory.FinTrdeg
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Height of a geometric rational point

For a prime `q` of a finite-type algebra over a field, this module constructs
the point of the scalar extension to the algebraic closure of `q.ResidueField`
and computes the height of its evaluation ideal. The result is stated in
`ℕ∞`, the codomain of `Ideal.height`, so that it can be used directly in local
cotangent-dimension estimates.

The proof follows the local dimension step of the Stacks Project, Tag 00TT.
Flatness of scalar extension first separates the height of `q` from the height
in the fibre. Quotient and localization equivalences reduce the latter to the
kernel of `L ⊗[k] K → L`. A finite transcendence basis presents `K` as a
finite extension of a rational function field. Going up, going down, and
height additivity preserve the evaluation height across that finite extension;
localizing a polynomial ring then identifies the remaining height with the
cardinality of the transcendence basis.
-/

open scoped TensorProduct

universe u v w x

private lemma mvPolynomial_maximal_height
    {F : Type w} [Field F] (n : ℕ)
    (m : Ideal (MvPolynomial (Fin n) F)) [m.IsMaximal] :
    m.height = n := by
  induction n with
  | zero =>
      let e := MvPolynomial.isEmptyRingEquiv F (Fin 0)
      have hm : (m.map e).IsMaximal := inferInstance
      have hbot : m.map e = (⊥ : Ideal F) :=
        (Ideal.bot_isMaximal.eq_of_le hm.ne_top bot_le).symm
      rw [← e.height_map m, hbot, Ideal.height_bot]
      rfl
  | succ n ih =>
      let e := MvPolynomial.finSuccEquiv F n
      let M : Ideal (Polynomial (MvPolynomial (Fin n) F)) := m.map e
      have hM : M.IsMaximal := inferInstance
      let p : Ideal (MvPolynomial (Fin n) F) := M.comap Polynomial.C
      have hp : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing M
      have hover : M.LiesOver p := ⟨rfl⟩
      rw [← e.height_map m]
      change M.height = ↑(n + 1)
      rw [Polynomial.height_eq_height_add_one p M, ih p]
      simp

private lemma mvPolynomial_fintype_maximal_height
    {F : Type w} {I : Type v} [Field F] [Fintype I]
    (m : Ideal (MvPolynomial I F)) [m.IsMaximal] :
    m.height = Fintype.card I := by
  let e := MvPolynomial.renameEquiv F (Fintype.equivFin I)
  rw [← e.height_map m]
  exact mvPolynomial_maximal_height (Fintype.card I) (m.map e)

private noncomputable def tensorEval
    (k : Type u) (K : Type v) (L : Type w)
    [CommRing k] [CommRing K] [CommRing L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] :
    L ⊗[k] K →ₐ[L] L :=
  Algebra.TensorProduct.lift (AlgHom.id L L) (IsScalarTower.toAlgHom k K L)
    fun _ _ ↦ .all _ _

@[simp]
private theorem tensorEval_tmul
    (k : Type u) (K : Type v) (L : Type w)
    [CommRing k] [CommRing K] [CommRing L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    (l : L) (x : K) :
    tensorEval k K L (l ⊗ₜ[k] x) = l * algebraMap K L x := by
  simp [tensorEval]

private lemma tensorFieldEval_height_of_finite
    (k : Type u) (F : Type v) (K : Type w) (L : Type x)
    [Field k] [Field F] [Field K] [Field L]
    [Algebra k F] [Algebra k K] [Algebra k L] [Algebra F K] [Algebra F L]
    [Algebra K L] [IsScalarTower k F K] [IsScalarTower k F L]
    [IsScalarTower k K L] [IsScalarTower F K L] [Module.Finite F K]
    [IsNoetherianRing (L ⊗[k] F)] :
    (RingHom.ker (tensorEval k K L)).height =
      (RingHom.ker (tensorEval k F L)).height := by
  let evK : L ⊗[k] K →ₐ[L] L := tensorEval k K L
  let pK : Ideal (L ⊗[k] K) := RingHom.ker evK
  have hevK_surj : Function.Surjective evK := by
    intro x
    exact ⟨x ⊗ₜ[k] (1 : K), by simp [evK, tensorEval]⟩
  let : pK.IsMaximal := RingHom.ker_isMaximal_of_surjective evK hevK_surj
  let h : L ⊗[k] F →ₐ[k] L ⊗[k] K :=
    Algebra.TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k F K)
  let p₀ : Ideal (L ⊗[k] F) := pK.comap h
  have hhfinite : h.toRingHom.Finite := by
    dsimp [h]
    exact RingHom.Finite.tensorProductMap
      (f := AlgHom.id k L) (RingEquiv.refl L).finite
      (g := IsScalarTower.toAlgHom k F K)
      (RingHom.finite_algebraMap.mpr inferInstance)
  have hhflat : h.toRingHom.Flat := by
    dsimp [h]
    exact RingHom.Flat.tensorProductMap
      (f := AlgHom.id k L) (g := IsScalarTower.toAlgHom k F K)
      (RingHom.Flat.of_isField (Field.toIsField L) _)
      (RingHom.Flat.of_isField (Field.toIsField F) _)
  let : Algebra (L ⊗[k] F) (L ⊗[k] K) := h.toRingHom.toAlgebra
  let : Module.Finite (L ⊗[k] F) (L ⊗[k] K) :=
    RingHom.finite_algebraMap.mp hhfinite
  let : Module.Flat (L ⊗[k] F) (L ⊗[k] K) :=
    RingHom.flat_algebraMap_iff.mp hhflat
  let : p₀.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal pK
  have hover : pK.LiesOver p₀ := ⟨rfl⟩
  let : IsNoetherianRing (L ⊗[k] K) :=
    IsNoetherianRing.of_finite (L ⊗[k] F) (L ⊗[k] K)
  have hmin : pK ∈
      (p₀.map (algebraMap (L ⊗[k] F) (L ⊗[k] K))).minimalPrimes :=
    Ideal.IsIntegral.mem_minimalPrimes_map_under pK
  have hqmin : pK.map (Ideal.Quotient.mk
      (p₀.map (algebraMap (L ⊗[k] F) (L ⊗[k] K)))) ∈
      minimalPrimes ((L ⊗[k] K) ⧸
        p₀.map (algebraMap (L ⊗[k] F) (L ⊗[k] K))) := by
    rw [@Ideal.minimalPrimes_eq_comap (L ⊗[k] K) _
      (p₀.map (algebraMap (L ⊗[k] F) (L ⊗[k] K)))] at hmin
    rcases hmin with ⟨Q, hQ, hQpK⟩
    have heq : Q = pK.map (Ideal.Quotient.mk
        (p₀.map (algebraMap (L ⊗[k] F) (L ⊗[k] K)))) := by
      apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      rw [hQpK, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
      symm
      apply sup_eq_left.mpr
      have hI : p₀.map (algebraMap (L ⊗[k] F) (L ⊗[k] K)) ≤ pK :=
        Ideal.map_le_iff_le_comap.mpr le_rfl
      change RingHom.ker (Ideal.Quotient.mk
        (p₀.map (algebraMap (L ⊗[k] F) (L ⊗[k] K)))) ≤ pK
      rwa [Ideal.mk_ker]
    simpa [heq] using hQ
  have hrelative :
      (pK.map (Ideal.Quotient.mk <| p₀.map
        (algebraMap (L ⊗[k] F) (L ⊗[k] K)))).height = 0 := by
    apply Ideal.height_eq_zero_iff.mpr
    exact hqmin
  have hpKheight : pK.height = p₀.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p₀ pK,
      hrelative, add_zero]
  have heval : ((tensorEval k K L).restrictScalars k).comp h =
      (tensorEval k F L).restrictScalars k := by
    apply Algebra.TensorProduct.ext
    · ext
      simp [h, tensorEval]
    · ext
      simp [h, tensorEval]
      exact (IsScalarTower.algebraMap_apply F K L _).symm
  have hp₀eq : p₀ = RingHom.ker (tensorEval k F L) := by
    dsimp [p₀, pK, evK]
    change Ideal.comap h.toRingHom (RingHom.ker (tensorEval k K L).toRingHom) =
      RingHom.ker (tensorEval k F L).toRingHom
    rw [RingHom.comap_ker]
    exact congrArg RingHom.ker (congrArg AlgHom.toRingHom heval)
  change pK.height = _
  rw [hpKheight, hp₀eq]

private lemma tensorFieldEval_height_finite_extension
    (k : Type u) (K L : Type v) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra.EssFiniteType k K] :
    (RingHom.ker (tensorEval k K L)).height =
      Cardinal.toNat (Algebra.trdeg k K) := by
  let : FinTrdeg k K := inferInstance
  obtain ⟨t, ht⟩ := exists_finset_isTranscendenceBasis k K
  let F := IntermediateField.adjoin k (Set.range ((↑) : t → K))
  have hFK : Algebra.IsAlgebraic F K := by
    dsimp [F]
    exact ht.isAlgebraic_field
  let : Algebra.IsAlgebraic F K := hFK
  let : Algebra.EssFiniteType F K := Algebra.EssFiniteType.of_comp k F K
  let : Module.Finite F K := Algebra.finite_of_essFiniteType_of_isAlgebraic
  let P := MvPolynomial t k
  let Q := FractionRing P
  let eF : Q ≃ₐ[k] F := ht.1.aevalEquivField
  let qToK : Q →ₐ[k] K := (IsScalarTower.toAlgHom k F K).comp eF.toAlgHom
  have hqfinite : qToK.toRingHom.Finite := by
    dsimp [qToK]
    exact RingHom.Finite.comp (RingHom.finite_algebraMap.mpr inferInstance)
      eF.toRingEquiv.finite
  let : Algebra Q K := qToK.toRingHom.toAlgebra
  let : IsScalarTower k Q K :=
    IsScalarTower.of_algebraMap_eq' qToK.comp_algebraMap.symm
  let : Module.Finite Q K := RingHom.finite_algebraMap.mp hqfinite
  let qToL : Q →ₐ[k] L := (IsScalarTower.toAlgHom k K L).comp qToK
  let : Algebra Q L := qToL.toRingHom.toAlgebra
  let : IsScalarTower k Q L :=
    IsScalarTower.of_algebraMap_eq' qToL.comp_algebraMap.symm
  let : IsScalarTower Q K L := IsScalarTower.of_algebraMap_eq' (by
    ext x
    rfl)
  let M : Submonoid P := nonZeroDivisors P
  let h : L ⊗[k] P →ₐ[L] L ⊗[k] Q :=
    Algebra.TensorProduct.lTensor L (IsScalarTower.toAlgHom k P Q)
  let : Algebra (L ⊗[k] P) (L ⊗[k] Q) := h.toRingHom.toAlgebra
  let : IsScalarTower L (L ⊗[k] P) (L ⊗[k] Q) :=
    IsScalarTower.of_algebraMap_eq' h.comp_algebraMap.symm
  let : IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := k) (A := L)))
      (L ⊗[k] Q) :=
    IsLocalization.tensorProduct_tensorProduct_right k L M Q (by
      change h.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom = _
      apply RingHom.ext
      intro x
      simp [h])
  let ePoly := MvPolynomial.algebraTensorAlgEquiv (σ := t) k L
  let : IsNoetherianRing (L ⊗[k] P) := by
    dsimp [P]
    exact isNoetherianRing_of_ringEquiv _ ePoly.symm.toRingEquiv
  let : IsNoetherianRing (L ⊗[k] Q) :=
    IsLocalization.isNoetherianRing
      (M.map (Algebra.TensorProduct.includeRight (R := k) (A := L))) _ inferInstance
  let evQ : L ⊗[k] Q →ₐ[L] L := tensorEval k Q L
  let pQ : Ideal (L ⊗[k] Q) := RingHom.ker evQ
  have hevQ_surj : Function.Surjective evQ := by
    intro x
    exact ⟨x ⊗ₜ[k] (1 : Q), by simp [evQ, tensorEval]⟩
  let : pQ.IsMaximal := RingHom.ker_isMaximal_of_surjective evQ hevQ_surj
  let evP : L ⊗[k] P →ₐ[L] L := evQ.comp h
  let pP : Ideal (L ⊗[k] P) := RingHom.ker evP
  have hevP_surj : Function.Surjective evP := by
    intro x
    exact ⟨x ⊗ₜ[k] (1 : P), by simp [evP, evQ, h, tensorEval]⟩
  let : pP.IsMaximal := RingHom.ker_isMaximal_of_surjective evP hevP_surj
  have hpunder : pQ.under (L ⊗[k] P) = pP := by
    change pQ.comap h = pP
    dsimp [pQ, pP, evP]
    ext x
    rfl
  have hpPheight : pP.height = Fintype.card t := by
    rw [← ePoly.toRingEquiv.height_map pP]
    exact mvPolynomial_fintype_maximal_height (pP.map ePoly)
  have hpQheight : pQ.height = Fintype.card t := by
    calc
      pQ.height = (pQ.under (L ⊗[k] P)).height :=
        (IsLocalization.height_under
          (M.map (Algebra.TensorProduct.includeRight (R := k) (A := L))) pQ).symm
      _ = pP.height := congrArg Ideal.height hpunder
      _ = Fintype.card t := hpPheight
  have hcard : Fintype.card t = Cardinal.toNat (Algebra.trdeg k K) := by
    rw [← ht.cardinalMk_eq_trdeg]
    simp
  calc
    (RingHom.ker (tensorEval k K L)).height =
        (RingHom.ker (tensorEval k Q L)).height :=
      tensorFieldEval_height_of_finite k Q K L
    _ = pQ.height := rfl
    _ = Fintype.card t := hpQheight
    _ = Cardinal.toNat (Algebra.trdeg k K) :=
      congrArg ((↑) : ℕ → ℕ∞) hcard

namespace Theory.AlgebraicGroup

/-- Evaluation at the geometric point over `q` after extending scalars to the
algebraic closure of its residue field. -/
@[expose]
public noncomputable def rationalPointBaseChangeEval
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    (q : Ideal S) [q.IsPrime] :
    AlgebraicClosure q.ResidueField ⊗[k] S →ₐ[AlgebraicClosure q.ResidueField]
      AlgebraicClosure q.ResidueField :=
  Algebra.TensorProduct.lift (AlgHom.id _ _)
    ((IsScalarTower.toAlgHom k q.ResidueField (AlgebraicClosure q.ResidueField)).comp
      (IsScalarTower.toAlgHom k S q.ResidueField))
    fun _ _ ↦ .all _ _

@[simp]
public theorem rationalPointBaseChangeEval_tmul
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    (q : Ideal S) [q.IsPrime]
    (x : AlgebraicClosure q.ResidueField) (s : S) :
    rationalPointBaseChangeEval k S q (x ⊗ₜ[k] s) =
      x * algebraMap q.ResidueField (AlgebraicClosure q.ResidueField)
        (algebraMap S q.ResidueField s) := by
  simp [rationalPointBaseChangeEval]

/-- The maximal ideal defined by the geometric point over `q` has height equal
to the height of `q` plus the transcendence degree of its residue field. -/
public theorem rationalPointBaseChangeEval_ker_height
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : Ideal S) [q.IsPrime] :
    (RingHom.ker (rationalPointBaseChangeEval k S q)).height =
      q.height + Cardinal.toNat (Algebra.trdeg k q.ResidueField) := by
  let L := AlgebraicClosure q.ResidueField
  let ev : L ⊗[k] S →ₐ[L] L := rationalPointBaseChangeEval k S q
  let m : Ideal (L ⊗[k] S) := RingHom.ker ev
  have hev_surj : Function.Surjective ev := by
    intro x
    exact ⟨x ⊗ₜ[k] (1 : S), by simp [ev, L]⟩
  let : m.IsMaximal := RingHom.ker_isMaximal_of_surjective ev hev_surj
  let : Algebra S (L ⊗[k] S) := Algebra.TensorProduct.rightAlgebra
  let : Module S (L ⊗[k] S) := Algebra.toModule
  have halgebraMap : algebraMap S (L ⊗[k] S) =
      Algebra.TensorProduct.includeRight.toRingHom := rfl
  have hunder : m.under S = q := by
    apply Ideal.ext
    intro s
    rw [Ideal.mem_under, halgebraMap, RingHom.mem_ker]
    simp [ev, L]
  have : m.LiesOver q := ⟨hunder.symm⟩
  let e : L ⊗[k] S ≃ₗ[S] S ⊗[k] L :=
    (Algebra.TensorProduct.commRight k S L).symm.toLinearEquiv
  let : Module.Flat S (L ⊗[k] S) := Module.Flat.of_linearEquiv e
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  let : IsNoetherianRing (L ⊗[k] S) :=
    Algebra.FiniteType.isNoetherianRing L (L ⊗[k] S)
  let J : Ideal (L ⊗[k] S) := q.map (algebraMap S (L ⊗[k] S))
  let mr : Ideal ((L ⊗[k] S) ⧸ J) := m.map (Ideal.Quotient.mk J)
  have hJm : J ≤ m := by
    dsimp [J]
    apply Ideal.map_le_iff_le_comap.mpr
    change q ≤ m.under S
    rw [hunder]
  let : mr.IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by simpa [Ideal.mk_ker] using hJm)
  have hmheight : m.height = q.height + mr.height :=
    Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q m
  let D := S ⧸ q
  let eQ : L ⊗[k] D ≃ₐ[L] (L ⊗[k] S) ⧸ J :=
    Algebra.TensorProduct.tensorQuotientEquiv
      (R := k) L S L q
  let evQuot : (L ⊗[k] S) ⧸ J →ₐ[L] L :=
    Ideal.Quotient.liftₐ J ev fun a ha ↦ by
      change ev a = 0
      exact hJm ha
  have hevQuot_ker : RingHom.ker evQuot = mr := by
    dsimp [evQuot, mr, m]
    change RingHom.ker (Ideal.Quotient.lift J ev.toRingHom _) =
      (RingHom.ker ev.toRingHom).map (Ideal.Quotient.mk J)
    exact Ideal.ker_quotient_lift ev.toRingHom hJm
  let evD : L ⊗[k] D →ₐ[L] L := tensorEval k D L
  have hevD : evQuot.comp eQ.toAlgHom = evD := by
    apply Algebra.TensorProduct.ext
    · rfl
    · apply DFunLike.ext
      intro d
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective d
      have heQ : eQ (1 ⊗ₜ[k] Ideal.Quotient.mk q s) =
          Ideal.Quotient.mk J (1 ⊗ₜ[k] s) := by
        exact Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul
          (R := k) L S L q (1 : L) s
      change evQuot (eQ (1 ⊗ₜ[k] Ideal.Quotient.mk q s)) =
        evD (1 ⊗ₜ[k] Ideal.Quotient.mk q s)
      rw [heQ]
      change (Ideal.Quotient.lift J ev.toRingHom _) (Ideal.Quotient.mk J (1 ⊗ₜ[k] s)) = _
      rw [Ideal.Quotient.lift_mk]
      simp [evD, ev, L, tensorEval]
      rw [IsScalarTower.algebraMap_apply D q.ResidueField L]
      rfl
  let pD : Ideal (L ⊗[k] D) := RingHom.ker evD
  have hevD_surj : Function.Surjective evD := by
    intro x
    exact ⟨x ⊗ₜ[k] (1 : D), by simp [evD, tensorEval]⟩
  let : pD.IsMaximal := RingHom.ker_isMaximal_of_surjective evD hevD_surj
  have hpDmap : pD.map eQ = mr := by
    rw [← hevQuot_ker]
    have hker : (RingHom.ker evQuot).comap eQ = pD := by
      dsimp [pD]
      change Ideal.comap eQ.toRingHom (RingHom.ker evQuot.toRingHom) =
        RingHom.ker evD.toRingHom
      rw [RingHom.comap_ker]
      exact congrArg RingHom.ker (congrArg AlgHom.toRingHom hevD)
    rw [← hker]
    exact Ideal.map_comap_of_surjective eQ eQ.surjective _
  have hpDheight : pD.height = mr.height := by
    rw [← hpDmap]
    exact eQ.toRingEquiv.height_map pD |>.symm
  let hD : L ⊗[k] D →ₐ[L] L ⊗[k] q.ResidueField :=
    Algebra.TensorProduct.lTensor L (IsScalarTower.toAlgHom k D q.ResidueField)
  let : Algebra (L ⊗[k] D) (L ⊗[k] q.ResidueField) :=
    hD.toRingHom.toAlgebra
  let : IsScalarTower L (L ⊗[k] D) (L ⊗[k] q.ResidueField) :=
    IsScalarTower.of_algebraMap_eq' hD.comp_algebraMap.symm
  let MD : Submonoid D := nonZeroDivisors D
  let : IsLocalization
      (MD.map (Algebra.TensorProduct.includeRight (R := k) (A := L)))
      (L ⊗[k] q.ResidueField) :=
    IsLocalization.tensorProduct_tensorProduct_right k L MD q.ResidueField (by
      change hD.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom = _
      apply RingHom.ext
      intro x
      simp [hD])
  let evK : L ⊗[k] q.ResidueField →ₐ[L] L := tensorEval k q.ResidueField L
  let pK : Ideal (L ⊗[k] q.ResidueField) := RingHom.ker evK
  have hevDK : evK.comp hD = evD := by
    apply Algebra.TensorProduct.ext
    · rfl
    · ext
      simp [evK, evD, hD, tensorEval]
      exact (IsScalarTower.algebraMap_apply D q.ResidueField L _).symm
  have hpKunder : pK.under (L ⊗[k] D) = pD := by
    change pK.comap hD = pD
    dsimp [pK, pD]
    change Ideal.comap hD.toRingHom (RingHom.ker evK.toRingHom) =
      RingHom.ker evD.toRingHom
    rw [RingHom.comap_ker]
    exact congrArg RingHom.ker (congrArg AlgHom.toRingHom hevDK)
  have hpKheight : pK.height = pD.height := by
    rw [← hpKunder]
    exact (IsLocalization.height_under
      (MD.map (Algebra.TensorProduct.includeRight (R := k) (A := L))) pK).symm
  let : Algebra.FiniteType k D := inferInstance
  let : Algebra.EssFiniteType D q.ResidueField :=
    Algebra.EssFiniteType.of_isLocalization (S := q.ResidueField) MD
  let : Algebra.EssFiniteType k q.ResidueField :=
    Algebra.EssFiniteType.comp k D q.ResidueField
  have hpKformula : pK.height =
      Cardinal.toNat (Algebra.trdeg k q.ResidueField) := by
    exact tensorFieldEval_height_finite_extension k q.ResidueField L
  change m.height = _
  rw [hmheight, ← hpDheight, ← hpKheight, hpKformula]

/-- The rational-point height formula after the coercion used by local
cotangent-dimension inequalities. -/
public theorem rationalPointBaseChangeEval_ker_height_withBot
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : Ideal S) [q.IsPrime] :
    ((RingHom.ker (rationalPointBaseChangeEval k S q)).height : WithBot ℕ∞) =
      q.height + Cardinal.toNat (Algebra.trdeg k q.ResidueField) := by
  rw [rationalPointBaseChangeEval_ker_height]
  simp

end Theory.AlgebraicGroup
