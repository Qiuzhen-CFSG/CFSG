module

public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.RatFunc.Luroth

/-!
# Rational function fields and purely inseparable extensions

A field extension `K / k` is a rational function field in one variable when
one transcendental element generates `K` as an intermediate field.  The main
result shows that this property passes from `F` to a finite purely inseparable
extension `L / F` when the base field `k` is algebraically closed.

The proof follows the algebraic argument after Borel, *Linear Algebraic
Groups*, Corollary 11.6 (`refs/KGroup/Bor1/Chapter4.tex`).  At the exponent of
`L / F`, the iterated Frobenius embeds `L` into `F`.  Its action on `k` is
semilinear rather than linear, but Frobenius is an automorphism of the perfect
field `k`; consequently the image still contains exactly the constants from
`k`.  A rational generator identifies `F` with `k(X)`, making the Frobenius
image a nonconstant intermediate field of `RatFunc k`.  Luroth's theorem makes
that image singly generated, and injectivity of Frobenius pulls the generator
and the generation statement back to `L`.
-/

universe u v w

open IntermediateField

namespace Theory

/-- A one-variable rational function field extension. -/
@[expose] public def IsRationalFunctionField
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] : Prop :=
  ∃ z : K, Transcendental k z ∧ IntermediateField.adjoin k {z} = ⊤

private noncomputable def rationalEquiv
    {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
    (hF : IsRationalFunctionField k F) : RatFunc k ≃ₐ[k] F :=
  let t := Classical.choose hF
  let ht := (Classical.choose_spec hF).1
  let hgen := (Classical.choose_spec hF).2
  ((RatFunc.algEquivOfTranscendental t ht).trans
      (IntermediateField.equivOfEq hgen)).trans
    (IntermediateField.topEquiv : (⊤ : IntermediateField k F) ≃ₐ[k] F)

/-- The image of an intermediate field under a ring homomorphism whose image
contains the chosen copy of the base field. -/
private def ringHomImage
    {k : Type u} {K : Type v} {R : Type w}
    [Field k] [Field K] [Field R] [Algebra k K] [Algebra k R]
    (rho : K →+* R)
    (hbase : ∀ a : k, ∃ b : k, rho (algebraMap k K b) = algebraMap k R a)
    (M : IntermediateField k K) : IntermediateField k R :=
{ M.toSubfield.map rho with
  algebraMap_mem' a := by
    obtain ⟨b, hb⟩ := hbase a
    rw [← hb]
    exact Subfield.mem_map.mpr ⟨algebraMap k K b, M.algebraMap_mem b, rfl⟩ }

private theorem mem_ringHomImage
    {k : Type u} {K : Type v} {R : Type w}
    [Field k] [Field K] [Field R] [Algebra k K] [Algebra k R]
    (rho : K →+* R)
    (hbase : ∀ a : k, ∃ b : k, rho (algebraMap k K b) = algebraMap k R a)
    (M : IntermediateField k K) (y : R) :
    y ∈ ringHomImage rho hbase M ↔ ∃ x ∈ M, rho x = y :=
  Subfield.mem_map

/-- A finite purely inseparable extension of a one-variable rational function
field over an algebraically closed field is again a rational function field. -/
public theorem IsRationalFunctionField.of_finite_purelyInseparable
    (k : Type u) (F : Type v) (L : Type w) (p : ℕ)
    [Field k] [Field F] [Field L]
    [IsAlgClosed k] [CharP k p] [Fact p.Prime]
    [Algebra k F] [Algebra k L] [Algebra F L] [IsScalarTower k F L]
    [FiniteDimensional F L] [IsPurelyInseparable F L]
    (hF : IsRationalFunctionField k F) :
    IsRationalFunctionField k L := by
  let n := IsPurelyInseparable.exponent F L
  let _ : ExpChar F p :=
    expChar_of_injective_algebraMap (algebraMap k F).injective p
  let phi : L →+* F :=
    IsPurelyInseparable.iterateFrobenius F L p (le_refl n)
  let e : RatFunc k ≃ₐ[k] F := rationalEquiv hF
  let rho : L →+* RatFunc k := e.symm.toRingEquiv.toRingHom.comp phi
  have hbase : ∀ a : k, ∃ b : k,
      rho (algebraMap k L b) = algebraMap k (RatFunc k) a := by
    intro a
    let b := (iterateFrobeniusEquiv k p n).symm a
    refine ⟨b, ?_⟩
    change e.symm (phi (algebraMap k L b)) = algebraMap k (RatFunc k) a
    calc
      e.symm (phi (algebraMap k L b)) =
          e.symm (phi (algebraMap F L (algebraMap k F b))) := by
            rw [IsScalarTower.algebraMap_apply k F L]
      _ = e.symm ((algebraMap k F b) ^ p ^ n) := by
        congr 1
        simpa [phi, n] using
          IsPurelyInseparable.iterateFrobenius_algebraMap L p
            (le_refl (IsPurelyInseparable.exponent F L)) (algebraMap k F b)
      _ = algebraMap k (RatFunc k) (b ^ p ^ n) := by
        rw [← map_pow, e.symm.commutes]
      _ = algebraMap k (RatFunc k) a := congrArg (algebraMap k (RatFunc k))
        ((iterateFrobeniusEquiv k p n).apply_symm_apply a)
  let E : IntermediateField k (RatFunc k) := ringHomImage rho hbase ⊤
  let t := Classical.choose hF
  have ht : Transcendental k t := (Classical.choose_spec hF).1
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpow : Transcendental k (t ^ p ^ n) := ht.pow (pow_pos hp n)
  have hrho_t : Transcendental k (rho (algebraMap F L t)) := by
    have heq : rho (algebraMap F L t) = e.symm (t ^ p ^ n) := by
      change e.symm (phi (algebraMap F L t)) = e.symm (t ^ p ^ n)
      congr 1
      simpa [phi, n] using
        IsPurelyInseparable.iterateFrobenius_algebraMap L p
          (le_refl (IsPurelyInseparable.exponent F L)) t
    rw [heq]
    intro halg
    exact hpow ((isAlgebraic_algHom_iff e.symm.toAlgHom e.symm.injective).mp halg)
  have hE : E ≠ ⊥ := by
    intro hbot
    have hmem : rho (algebraMap F L t) ∈ E :=
      (mem_ringHomImage rho hbase ⊤ _).mpr
        ⟨algebraMap F L t, IntermediateField.mem_top, rfl⟩
    rw [hbot, IntermediateField.mem_bot] at hmem
    obtain ⟨a, ha⟩ := hmem
    exact hrho_t (ha ▸ isAlgebraic_algebraMap a)
  let g : RatFunc k := RatFunc.Luroth.generator E
  have hg : Transcendental k g := RatFunc.Luroth.transcendental_generator hE
  have hgmem : g ∈ E := RatFunc.Luroth.generator_mem
  obtain ⟨z, -, hz⟩ := (mem_ringHomImage rho hbase ⊤ g).mp hgmem
  refine ⟨z, ?_, ?_⟩
  · intro hzalg
    have hzpow : IsAlgebraic k (z ^ p ^ n) := hzalg.pow _
    have hphi : IsAlgebraic k (phi z) := by
      rw [← isAlgebraic_algebraMap_iff (algebraMap F L).injective]
      rw [IsPurelyInseparable.algebraMap_iterateFrobenius]
      exact hzpow
    have hrho : IsAlgebraic k (rho z) := hphi.algHom e.symm.toAlgHom
    exact hg (hz ▸ hrho)
  · apply top_unique
    intro x _
    let M : IntermediateField k L := IntermediateField.adjoin k {z}
    have hME : ringHomImage rho hbase M = E := by
      apply le_antisymm
      · intro y hy
        obtain ⟨a, -, rfl⟩ := (mem_ringHomImage rho hbase M y).mp hy
        exact (mem_ringHomImage rho hbase ⊤ _).mpr
          ⟨a, IntermediateField.mem_top, rfl⟩
      · rw [RatFunc.Luroth.eq_adjoin_generator (E := E)]
        rw [IntermediateField.adjoin_le_iff]
        intro y hy
        simp only [Set.mem_singleton_iff] at hy
        subst y
        exact (mem_ringHomImage rho hbase M g).mpr
          ⟨z, IntermediateField.subset_adjoin k {z} (Set.mem_singleton z), hz⟩
    have hrhox : rho x ∈ ringHomImage rho hbase M := by
      rw [hME]
      exact (mem_ringHomImage rho hbase ⊤ _).mpr
        ⟨x, IntermediateField.mem_top, rfl⟩
    obtain ⟨y, hyM, hy⟩ := (mem_ringHomImage rho hbase M _).mp hrhox
    have hyx : y = x := rho.injective hy
    exact hyx ▸ hyM

end Theory
