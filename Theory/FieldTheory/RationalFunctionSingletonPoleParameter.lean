module

public import Theory.FieldTheory.RationalFunctionProjectivePoles

/-!
# A polynomial parameter from one projective pole

For a transcendental rational function whose reduced denominator has exactly one
projective pole, this module constructs a coordinate in which the pole is the
point at infinity.  The denominator then has no affine zero over the
algebraically closed ground field, hence is constant and the transformed
function is a polynomial in `X`.  A fractional-linear coordinate is built
explicitly as `a + X⁻¹`; its transcendence, generation of the full rational
function field, and inverse coordinate are proved before transporting the
polynomial membership back through the resulting algebra automorphism.  This
is the one-place branch of Borel, *Linear Algebraic Groups*, Theorem 10.9
(`refs/KGroup/Bor1/Chapter3.tex`), and remains at the field-theory layer.
-/

universe u

open IntermediateField Polynomial
open scoped OnePoint Pointwise

namespace RatFunc

variable {k : Type u} [Field k]

noncomputable section

local instance : DecidableEq k := Classical.decEq k

private lemma denom_const_of_support_eq_infty (f : RatFunc k)
    [IsAlgClosed k] (hs : f.projectivePoleSupport = {OnePoint.infty}) :
    ∃ c : k, f.denom = (Polynomial.C c : k[X]) := by
  have hdeg : f.denom.natDegree = 0 := by
    by_contra hdeg
    have hpos : 0 < f.denom.natDegree := Nat.pos_of_ne_zero hdeg
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root f.denom
      (Polynomial.natDegree_pos_iff_degree_pos.mp hpos).ne'
    have hmem : (a : OnePoint k) ∈ f.projectivePoleSupport :=
      (mem_projectivePoleSupport_coe_iff f a).2 ha
    rw [hs] at hmem
    exact OnePoint.coe_ne_infty a hmem
  exact ⟨f.denom.coeff 0, eq_C_of_natDegree_eq_zero hdeg⟩

private lemma mem_adjoin_X_of_denom_const (f : RatFunc k) (c : k)
    (hc : f.denom = (Polynomial.C c : k[X])) :
    f ∈ Algebra.adjoin k {(RatFunc.X : RatFunc k)} := by
  let A := Algebra.adjoin k {(RatFunc.X : RatFunc k)}
  have hnum : algebraMap k[X] (RatFunc k) f.num ∈ A := by
    simpa [A, aeval_X_left_eq_algebraMap] using
      (Polynomial.aeval_mem_adjoin_singleton k (RatFunc.X : RatFunc k) (p := f.num))
  have hscalar : algebraMap k (RatFunc k) c⁻¹ ∈ A := A.algebraMap_mem _
  have hmul : algebraMap k[X] (RatFunc k) f.num *
      algebraMap k (RatFunc k) c⁻¹ ∈ A := A.mul_mem hnum hscalar
  rw [← f.num_div_denom, hc]
  simpa [div_eq_mul_inv, mul_comm] using hmul

private lemma parameter_sigma (a : k) :
    ∃ sigma : RatFunc k ≃ₐ[k] RatFunc k, ∃ s : RatFunc k,
      sigma (RatFunc.X : RatFunc k) = C a + (RatFunc.X : RatFunc k)⁻¹ ∧
      sigma s = RatFunc.X ∧ Transcendental k s ∧
      IntermediateField.adjoin k {s} = ⊤ := by
  let r : RatFunc k := C a + (RatFunc.X : RatFunc k)⁻¹
  have hx : (RatFunc.X : RatFunc k) ≠ 0 := RatFunc.X_ne_zero
  have hrat : (r - C a)⁻¹ = (RatFunc.X : RatFunc k) := by
    dsimp [r]
    field_simp
    ring
  have hr : ¬ ∃ c : k, r = C c := by
    rintro ⟨c, hc⟩
    have hconst : (RatFunc.X : RatFunc k) = C ((c - a)⁻¹) := by
      rw [← hrat, hc]
      rw [← map_sub, map_inv₀]
    have halg : IsAlgebraic k (C ((c - a)⁻¹) : RatFunc k) := by
      change IsAlgebraic k ((algebraMap k (RatFunc k)) ((c - a)⁻¹ : k))
      exact isAlgebraic_algebraMap ((c - a)⁻¹ : k)
    apply (RatFunc.transcendental_X : Transcendental k (RatFunc.X : RatFunc k))
    simpa [hconst] using halg
  have htr : Transcendental k r := RatFunc.transcendental_of_ne_C r hr
  let φ : k[X] →ₐ[k] RatFunc k := Polynomial.aeval r
  have hφinj : Function.Injective φ := transcendental_iff_injective.mp htr
  let hN : nonZeroDivisors k[X] ≤ Submonoid.comap φ (nonZeroDivisors (RatFunc k)) :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφinj
  let τ : RatFunc k →ₐ[k] RatFunc k := RatFunc.liftAlgHom φ hN
  have hτX : τ (RatFunc.X : RatFunc k) = r := by
    change τ ((algebraMap k[X] (RatFunc k)) Polynomial.X) = r
    rw [RatFunc.liftAlgHom_apply]
    simp [φ]
  have hgen : IntermediateField.adjoin k {r} = ⊤ := by
    apply top_unique
    rw [← RatFunc.adjoin_X, IntermediateField.adjoin_simple_le_iff]
    have hm : r - C a ∈ IntermediateField.adjoin k {r} := by
      exact (IntermediateField.adjoin k {r}).sub_mem
        (IntermediateField.subset_adjoin k {r} (Set.mem_singleton r))
        (by simpa using
          (IntermediateField.algebraMap_mem (IntermediateField.adjoin k {r}) a))
    have hi := (IntermediateField.adjoin k {r}).inv_mem hm
    simpa [hrat] using hi
  have hτinj : Function.Injective τ := RatFunc.liftAlgHom_injective φ hφinj
  have hτsurj : Function.Surjective τ := by
    rw [← AlgHom.fieldRange_eq_top]
    apply top_unique
    rw [← hgen, IntermediateField.adjoin_simple_le_iff]
    rw [AlgHom.mem_fieldRange]
    exact ⟨RatFunc.X, hτX⟩
  let sigma : RatFunc k ≃ₐ[k] RatFunc k := AlgEquiv.ofBijective τ ⟨hτinj, hτsurj⟩
  have hsigma : sigma (RatFunc.X : RatFunc k) = r := by
    change τ (RatFunc.X : RatFunc k) = r
    exact hτX
  let s : RatFunc k := ((RatFunc.X : RatFunc k) - C a)⁻¹
  have hsigma_s : sigma s = (RatFunc.X : RatFunc k) := by
    dsimp [s]
    have hC : sigma (C a) = (C a : RatFunc k) := by
      change sigma ((algebraMap k (RatFunc k)) a) = (algebraMap k (RatFunc k)) a
      exact sigma.commutes a
    rw [map_inv₀, map_sub, hsigma, hC]
    exact hrat
  have hsigma_symm : sigma.symm (RatFunc.X : RatFunc k) = s := by
    apply sigma.injective
    simp [hsigma_s]
  have htr_s : Transcendental k s := by
    rw [← hsigma_symm, transcendental_iff_injective]
    intro p q hpq
    apply (transcendental_iff_injective.mp
      (RatFunc.transcendental_X : Transcendental k (RatFunc.X : RatFunc k)))
    have h := congrArg sigma hpq
    simpa [Polynomial.aeval_algHom_apply] using h
  have hgen_s : IntermediateField.adjoin k {s} = ⊤ := by
    apply top_unique
    rw [← RatFunc.adjoin_X, IntermediateField.adjoin_simple_le_iff]
    let E := IntermediateField.adjoin k {s}
    have hi : s⁻¹ ∈ E := E.inv_mem
      (IntermediateField.subset_adjoin k {s} (Set.mem_singleton s))
    have ha : C a ∈ E := by simpa using (E.algebraMap_mem a)
    have hxs : (RatFunc.X : RatFunc k) = C a + s⁻¹ := by
      dsimp [s]
      simp
    rw [hxs]
    exact E.add_mem ha hi
  exact ⟨sigma, s, hsigma, hsigma_s, htr_s, hgen_s⟩

/-- A transcendental rational function with one projective pole is polynomial
in a transcendental generator of the rational function field. -/
public theorem exists_one_place_parameter_of_projectivePoleSupport_ncard_eq_one
    [IsAlgClosed k] (t : RatFunc k) (ht : Transcendental k t)
    (hone : t.projectivePoleSupport.ncard = 1) :
    ∃ s : RatFunc k, Transcendental k s ∧
      IntermediateField.adjoin k {s} = ⊤ ∧ t ∈ Algebra.adjoin k {s} := by
  have hnotconst : ¬ ∃ c : k, t = C c := by
    rintro ⟨c, rfl⟩
    apply ht
    change IsAlgebraic k ((algebraMap k (RatFunc k)) c)
    exact isAlgebraic_algebraMap c
  obtain ⟨p, hp_mem⟩ := projectivePoleSupport_nonempty hnotconst
  obtain ⟨q, hq⟩ := Set.ncard_eq_one.mp hone
  have hpq : p = q := by
    rw [hq] at hp_mem
    exact Set.mem_singleton_iff.mp hp_mem
  subst q
  have hp := hq
  cases p with
  | infty =>
      obtain ⟨c, hc⟩ := denom_const_of_support_eq_infty t hp
      exact ⟨RatFunc.X, RatFunc.transcendental_X, RatFunc.adjoin_X,
        mem_adjoin_X_of_denom_const t c hc⟩
  | coe a =>
      obtain ⟨sigma, s, hsigma, hsigma_s, htr_s, hgen_s⟩ := parameter_sigma a
      let A : Matrix (Fin 2) (Fin 2) k := !![a, 1; 1, 0]
      have hA : Matrix.det A ≠ 0 := by
        simp [A, Matrix.det_fin_two]
      let g : GL (Fin 2) k := Matrix.GeneralLinearGroup.mkOfDetNeZero A hA
      have hmobius : sigma (RatFunc.X : RatFunc k) =
          (C (g 0 0) * RatFunc.X + C (g 0 1)) /
            (C (g 1 0) * RatFunc.X + C (g 1 1)) := by
        calc
          sigma (RatFunc.X : RatFunc k) = C a + (RatFunc.X : RatFunc k)⁻¹ := hsigma
          _ = (C (g 0 0) * RatFunc.X + C (g 0 1)) /
              (C (g 1 0) * RatFunc.X + C (g 1 1)) := by
                simp [g, A]
                field_simp [RatFunc.X_ne_zero]
      have hact : ∀ x : OnePoint k,
          projectiveLinearAction g x = (a : OnePoint k) ↔
            x = OnePoint.infty := by
        intro x
        rw [projectiveLinearAction_eq_smul]
        cases x with
        | infty => simp [OnePoint.smul_infty_eq_ite, g, A]
        | coe z =>
            by_cases hz : z = 0
            · subst z
              simp [OnePoint.smul_some_eq_ite, g, A]
            · simp [OnePoint.smul_some_eq_ite, g, A, hz]
              intro heq
              field_simp [hz] at heq
              exact (one_ne_zero : (1 : k) ≠ 0) (by
                calc
                  (1 : k) = (a * z + 1) - a * z := by ring
                  _ = 0 := sub_eq_zero.mpr heq)
      have hcov := projectivePoleSupport_algEquiv sigma t g hmobius
      have hsupport : (sigma t).projectivePoleSupport = {OnePoint.infty} := by
        ext x
        rw [hcov]
        rw [hp]
        simp only [Set.mem_preimage]
        simpa only [Set.mem_singleton_iff] using hact x
      obtain ⟨c, hc⟩ := denom_const_of_support_eq_infty (sigma t) hsupport
      have hpoly : sigma t ∈ Algebra.adjoin k {(RatFunc.X : RatFunc k)} :=
        mem_adjoin_X_of_denom_const (sigma t) c hc
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hpoly
      obtain ⟨q, hq⟩ := hpoly
      refine ⟨s, htr_s, hgen_s, ?_⟩
      have hts : t = Polynomial.aeval s q := by
        apply sigma.injective
        calc
          sigma t = Polynomial.aeval (RatFunc.X : RatFunc k) q := hq.symm
          _ = sigma (Polynomial.aeval s q) := by
            rw [← hsigma_s]
            exact Polynomial.aeval_algHom_apply sigma s q
      rw [hts]
      exact Polynomial.aeval_mem_adjoin_singleton k s

end

end RatFunc
