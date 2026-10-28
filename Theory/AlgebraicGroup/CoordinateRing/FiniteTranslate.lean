module

public import Theory.AlgebraicGroup.CoordinateRing.Basic

universe u

/-! Finite-dimensional control of a regular two-variable family. -/

namespace Theory.AlgebraicGroup

section

open scoped TensorProduct

variable {k : Type u} [Field k]

/-- Fixing the second argument of a two-variable regular family produces
functions contained in one finitely generated subspace. -/
public lemma Variety.Morphism.secondSlices_mem_finiteSubmodule
    {G P H : Variety k}
    (F : Variety.Morphism (Variety.prod G P) H)
    (q : Variety.PolynomialFunction H) :
    ∃ W : Submodule k (Variety.PolynomialFunction G), W.FG ∧
      ∀ y : Variety.Point P,
        (F.comp ((Variety.Morphism.id G).pair
          (Variety.Morphism.const G P y))).pullbackAlgHom q ∈ W := by
  let p := F.pullbackAlgHom q
  let t := (polynomialFunction_prod_algEquiv G P).symm p
  rcases TensorProduct.exists_sum_tmul_eq t with ⟨n, a, b, ht⟩
  let W : Submodule k (Variety.PolynomialFunction G) :=
    Submodule.span k (Set.range a)
  have hWfg : W.FG := Submodule.fg_span (Set.finite_range a)
  refine ⟨W, hWfg, ?_⟩
  intro y
  have hp : polynomialFunctionTensor G P (∑ i, a i ⊗ₜ[k] b i) = p := by
    rw [← ht]
    exact (polynomialFunction_prod_algEquiv G P).apply_symm_apply p
  have heq :
      (F.comp ((Variety.Morphism.id G).pair
        (Variety.Morphism.const G P y))).pullbackAlgHom q =
        ∑ i, (b i y) • a i := by
    apply Variety.PolynomialFunction.ext
    intro x
    have hpx := congrArg
      (fun r : Variety.PolynomialFunction (Variety.prod G P) =>
        r ((Variety.prodPointEquiv G P).symm (x, y))) hp
    change q (F.toFun ((Variety.prodPointEquiv G P).symm (x, y))) =
      (∑ i, (b i y) • a i) x
    have hsum : ∑ i, a i x * b i y =
        q (F.toFun ((Variety.prodPointEquiv G P).symm (x, y))) := by
      change polynomialFunctionTensor G P (∑ i, a i ⊗ₜ[k] b i)
          ((Variety.prodPointEquiv G P).symm (x, y)) =
        q (F.toFun ((Variety.prodPointEquiv G P).symm (x, y))) at hpx
      rw [map_sum] at hpx
      rw [show (∑ i, polynomialFunctionTensor G P (a i ⊗ₜ[k] b i))
          ((Variety.prodPointEquiv G P).symm (x, y)) =
        ∑ i, polynomialFunctionTensor G P (a i ⊗ₜ[k] b i)
          ((Variety.prodPointEquiv G P).symm (x, y)) by
          exact map_sum (polynomialFunctionEvalAddHom (Variety.prod G P)
            ((Variety.prodPointEquiv G P).symm (x, y)))
            (fun i => polynomialFunctionTensor G P (a i ⊗ₜ[k] b i))
            Finset.univ] at hpx
      simpa only [polynomialFunctionTensor_tmul,
        polynomialFunctionLeft_apply, polynomialFunctionRight_apply,
        polynomialFunction_mul_apply, Equiv.apply_symm_apply] using hpx
    rw [← hsum]
    rw [show (∑ i, (b i y) • a i) x =
      ∑ i, ((b i y) • a i) x by
        exact map_sum (polynomialFunctionEvalAddHom G x)
          (fun i => (b i y) • a i) Finset.univ]
    simp only [polynomialFunction_smul_apply]
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  rw [heq]
  apply Submodule.sum_mem
  intro i hi
  exact W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)

end

/-! Finite-dimensional control of all two-sided translates of one coordinate. -/

section

variable {k : Type u} [Field k]

public lemma exists_finite_twoSidedTranslate_submodule
    (G : Variety k) [AlgebraicGroup G]
    (f : Variety.PolynomialFunction G) :
    ∃ W : Submodule k (Variety.PolynomialFunction G), W.FG ∧
      ∀ a b : Variety.Point G,
        (AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom
          ((AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom f) ∈ W := by
  let x := Variety.Morphism.fst G (Variety.prod G G)
  let params := Variety.Morphism.snd G (Variety.prod G G)
  let a := (Variety.Morphism.fst G G).comp params
  let b := (Variety.Morphism.snd G G).comp params
  let ax := (AlgebraicGroup.mulMorphism G).comp (a.pair x)
  let F := (AlgebraicGroup.mulMorphism G).comp (ax.pair b)
  obtain ⟨W, hW, hslice⟩ := F.secondSlices_mem_finiteSubmodule f
  refine ⟨W, hW, ?_⟩
  intro ga gb
  let p : Variety.Point (Variety.prod G G) :=
    (Variety.prodPointEquiv G G).symm (ga, gb)
  have hp := hslice p
  convert hp using 1
  apply Variety.PolynomialFunction.ext
  intro gx
  change f (ga * gx * gb) =
    f (F.toFun ((Variety.prodPointEquiv G (Variety.prod G G)).symm (gx, p)))
  simp [F, ax, a, b, x, params, p, Variety.Morphism.comp,
    Variety.Morphism.pair, Variety.Morphism.fst, Variety.Morphism.snd,
    AlgebraicGroup.mulMorphism, Variety.prodPointEquiv]

end

section
variable {k : Type u} [Field k]

public lemma exists_finite_twoSidedTranslate_stableSubmodule
    (G : Variety k) [AlgebraicGroup G]
    (t : Finset (Variety.PolynomialFunction G)) :
    ∃ W : Submodule k (Variety.PolynomialFunction G), W.FG ∧
      (↑t : Set (Variety.PolynomialFunction G)) ⊆ W ∧
      (∀ a q, q ∈ W →
        (AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom q ∈ W) ∧
      (∀ b q, q ∈ W →
        (AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom q ∈ W) := by
  let S : Set (Variety.PolynomialFunction G) :=
    {q | ∃ f ∈ t, ∃ a b : Variety.Point G,
      q = (AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom
        ((AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom f)}
  let W := Submodule.span k S
  choose U hUfg hU using fun i : t =>
    AlgebraicGroup.exists_finite_twoSidedTranslate_submodule G i.1
  let upper : Submodule k (Variety.PolynomialFunction G) := ⨆ i : t, U i
  have hupperfg : upper.FG := by
    apply Submodule.fg_iSup
    intro i
    exact hUfg i
  have hWle : W ≤ upper := by
    apply Submodule.span_le.mpr
    intro q hq
    rcases hq with ⟨f, hf, a, b, rfl⟩
    let i : t := ⟨f, hf⟩
    exact Submodule.mem_iSup_of_mem i (hU i a b)
  have hWfg : W.FG := hupperfg.of_le hWle
  refine ⟨W, hWfg, ?_, ?_, ?_⟩
  · intro f hf
    apply Submodule.subset_span
    refine ⟨f, hf, 1, 1, ?_⟩
    apply Variety.PolynomialFunction.ext
    intro x
    change f x = f ((AlgebraicGroup.rightMulMorphism G 1).toFun
      ((AlgebraicGroup.leftMulMorphism G 1).toFun x))
    rw [AlgebraicGroup.leftMulMorphism_apply,
      AlgebraicGroup.rightMulMorphism_apply, one_mul, mul_one]
  · intro a q hq
    let T := (AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom.toLinearMap
    refine Submodule.span_induction (p := fun q _ => T q ∈ W) ?_ ?_ ?_ ?_ hq
    · intro q hq
      rcases hq with ⟨f, hf, c, d, rfl⟩
      apply Submodule.subset_span
      refine ⟨f, hf, c * a, d, ?_⟩
      apply Variety.PolynomialFunction.ext
      intro x
      change f ((AlgebraicGroup.rightMulMorphism G d).toFun
        ((AlgebraicGroup.leftMulMorphism G c).toFun
          ((AlgebraicGroup.leftMulMorphism G a).toFun x))) =
        f ((AlgebraicGroup.rightMulMorphism G d).toFun
          ((AlgebraicGroup.leftMulMorphism G (c * a)).toFun x))
      simp only [AlgebraicGroup.leftMulMorphism_apply,
        AlgebraicGroup.rightMulMorphism_apply, mul_assoc]
    · exact W.zero_mem
    · intro x y hx hy hTx hTy
      exact W.add_mem hTx hTy
    · intro r x hx hTx
      rw [T.map_smul]
      exact W.smul_mem r hTx
  · intro b q hq
    let T := (AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom.toLinearMap
    refine Submodule.span_induction (p := fun q _ => T q ∈ W) ?_ ?_ ?_ ?_ hq
    · intro q hq
      rcases hq with ⟨f, hf, c, d, rfl⟩
      apply Submodule.subset_span
      refine ⟨f, hf, c, b * d, ?_⟩
      apply Variety.PolynomialFunction.ext
      intro x
      change f ((AlgebraicGroup.rightMulMorphism G d).toFun
        ((AlgebraicGroup.leftMulMorphism G c).toFun
          ((AlgebraicGroup.rightMulMorphism G b).toFun x))) =
        f ((AlgebraicGroup.rightMulMorphism G (b * d)).toFun
          ((AlgebraicGroup.leftMulMorphism G c).toFun x))
      simp only [AlgebraicGroup.leftMulMorphism_apply,
        AlgebraicGroup.rightMulMorphism_apply, mul_assoc]
    · exact W.zero_mem
    · intro x y hx hy hTx hTy
      exact W.add_mem hTx hTy
    · intro r x hx hTx
      rw [T.map_smul]
      exact W.smul_mem r hTx

end

section
variable {k : Type u} [Field k]

public lemma exists_finite_translate_antipode_stableSubmodule
    (G : Variety k) [AlgebraicGroup G]
    (t : Finset (Variety.PolynomialFunction G)) :
    ∃ W : Submodule k (Variety.PolynomialFunction G), W.FG ∧
      (↑t : Set (Variety.PolynomialFunction G)) ⊆ W ∧
      (∀ a q, q ∈ W →
        (AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom q ∈ W) ∧
      (∀ b q, q ∈ W →
        (AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom q ∈ W) ∧
      (∀ q, q ∈ W → AlgebraicGroup.coordinateAntipode G q ∈ W) := by
  obtain ⟨V, hVfg, htV, hleftV, hrightV⟩ :=
    AlgebraicGroup.exists_finite_twoSidedTranslate_stableSubmodule G t
  let S := (AlgebraicGroup.coordinateAntipode G).toLinearMap
  let W := V ⊔ V.map S
  have hSinvolutive : ∀ q, S (S q) = q := by
    intro q
    apply Variety.PolynomialFunction.ext
    intro x
    change q ((x⁻¹)⁻¹) = q x
    simp
  have hSleft : ∀ a q,
      S ((AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom q) =
        (AlgebraicGroup.rightMulMorphism G a⁻¹).pullbackAlgHom (S q) := by
    intro a q
    apply Variety.PolynomialFunction.ext
    intro x
    change q (a * x⁻¹) = q ((x * a⁻¹)⁻¹)
    rw [mul_inv_rev, inv_inv]
  have hSright : ∀ b q,
      S ((AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom q) =
        (AlgebraicGroup.leftMulMorphism G b⁻¹).pullbackAlgHom (S q) := by
    intro b q
    apply Variety.PolynomialFunction.ext
    intro x
    change q (x⁻¹ * b) = q ((b⁻¹ * x)⁻¹)
    rw [mul_inv_rev, inv_inv]
  have hWfg : W.FG := hVfg.sup (Submodule.FG.map S hVfg)
  refine ⟨W, hWfg, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact Submodule.mem_sup_left (htV hq)
  · intro a q hq
    rcases Submodule.mem_sup.mp hq with ⟨x, hx, y, hy, rfl⟩
    rcases Submodule.mem_map.mp hy with ⟨z, hz, rfl⟩
    rw [map_add]
    apply Submodule.add_mem_sup
    · exact hleftV a x hx
    · apply Submodule.mem_map.mpr
      refine ⟨(AlgebraicGroup.rightMulMorphism G a⁻¹).pullbackAlgHom z,
        hrightV a⁻¹ z hz, ?_⟩
      rw [hSright, inv_inv]
  · intro b q hq
    rcases Submodule.mem_sup.mp hq with ⟨x, hx, y, hy, rfl⟩
    rcases Submodule.mem_map.mp hy with ⟨z, hz, rfl⟩
    rw [map_add]
    apply Submodule.add_mem_sup
    · exact hrightV b x hx
    · apply Submodule.mem_map.mpr
      refine ⟨(AlgebraicGroup.leftMulMorphism G b⁻¹).pullbackAlgHom z,
        hleftV b⁻¹ z hz, ?_⟩
      rw [hSleft, inv_inv]
  · intro q hq
    rcases Submodule.mem_sup.mp hq with ⟨x, hx, y, hy, rfl⟩
    rcases Submodule.mem_map.mp hy with ⟨z, hz, rfl⟩
    change S (x + S z) ∈ W
    rw [map_add, hSinvolutive, add_comm]
    exact Submodule.add_mem_sup hz (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)

end

section
variable {k : Type u} [Field k]

public lemma exists_finiteType_translate_antipode_stableSubalgebra
    (G : Variety k) [AlgebraicGroup G]
    (t : Finset (Variety.PolynomialFunction G)) :
    ∃ C : Subalgebra k (Variety.PolynomialFunction G),
      Algebra.FiniteType k C ∧
      (↑t : Set (Variety.PolynomialFunction G)) ⊆ C ∧
      (∀ a q, q ∈ C →
        (AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom q ∈ C) ∧
      (∀ b q, q ∈ C →
        (AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom q ∈ C) ∧
      (∀ q, q ∈ C → AlgebraicGroup.coordinateAntipode G q ∈ C) := by
  obtain ⟨W, hWfg, htW, hleftW, hrightW, hantipodeW⟩ :=
    AlgebraicGroup.exists_finite_translate_antipode_stableSubmodule G t
  obtain ⟨s, hsfinite, hsW⟩ := Submodule.fg_def.mp hWfg
  let C := Algebra.adjoin k s
  have hWleC : W ≤ C.toSubmodule := by
    rw [← hsW]
    exact Submodule.span_le.mpr (fun q hq => Algebra.subset_adjoin hq)
  refine ⟨C, Algebra.FiniteType.adjoin_of_finite hsfinite, ?_, ?_, ?_, ?_⟩
  · exact fun q hq => hWleC (htW hq)
  · intro a q hq
    induction hq using Algebra.adjoin_induction with
    | mem q hqs =>
        exact hWleC (hleftW a q (hsW ▸ Submodule.subset_span hqs))
    | algebraMap r =>
        rw [(AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom.commutes]
        exact C.algebraMap_mem r
    | add x y hx hy hTx hTy =>
        simpa only [map_add] using C.add_mem hTx hTy
    | mul x y hx hy hTx hTy =>
        simpa only [map_mul] using C.mul_mem hTx hTy
  · intro b q hq
    induction hq using Algebra.adjoin_induction with
    | mem q hqs =>
        exact hWleC (hrightW b q (hsW ▸ Submodule.subset_span hqs))
    | algebraMap r =>
        rw [(AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom.commutes]
        exact C.algebraMap_mem r
    | add x y hx hy hTx hTy =>
        simpa only [map_add] using C.add_mem hTx hTy
    | mul x y hx hy hTx hTy =>
        simpa only [map_mul] using C.mul_mem hTx hTy
  · intro q hq
    induction hq using Algebra.adjoin_induction with
    | mem q hqs =>
        exact hWleC (hantipodeW q (hsW ▸ Submodule.subset_span hqs))
    | algebraMap r =>
        rw [(AlgebraicGroup.coordinateAntipode G).commutes]
        exact C.algebraMap_mem r
    | add x y hx hy hTx hTy =>
        simpa only [map_add] using C.add_mem hTx hTy
    | mul x y hx hy hTx hTy =>
        simpa only [map_mul] using C.mul_mem hTx hTy

end
end Theory.AlgebraicGroup

/-! Point evaluation restricted to a linear subspace of polynomial functions. -/
