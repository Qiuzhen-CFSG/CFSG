module
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.MinimalOrbit.DimensionBridge

/-!
# Affine dimension from the dimensions of open fibre pieces

For finite-type domains over an algebraically closed field, if every nonempty
open in each closed fibre has dimension `d`, then the source dimension equals
the target dimension plus `d`. A nonempty open inside each irreducible component
first gives its dimension; passage through quotient spectra then supplies the
component hypothesis of the transcendence-degree formula in `FiberAlgebra`.
The quotient rings may be nonreduced.

This is the affine-chart dimension step needed for Borel, *Linear Algebraic
Groups*, §11.1 (`refs/KGroup/Bor1/Chapter4.tex`). The premise is verified for
rational orbit fibres in `HomogeneousDimension`. `AffineFormula` compares
quotient spectra with actual scheme fibres, and `NonAffineFormula` performs
the restriction to affine charts.
-/

open TopologicalSpace Topology Cardinal
universe u
namespace Theory.AlgebraicGroup.Variety.Geometric.MinimalOrbit

private theorem component_dimension_of_nonemptyOpen
    {T : Type u} [TopologicalSpace T] [NoetherianSpace T] (d : WithBot ℕ∞)
    (hopen : ∀ U : Opens T, (U : Set T).Nonempty → topologicalKrullDim U = d)
    {Z : Set T} (hZ : Z ∈ irreducibleComponents T) :
    topologicalKrullDim Z = d := by
  have hne : (Set.univ : Set T).Nonempty := hZ.1.nonempty.mono (Set.subset_univ _)
  have htotal : topologicalKrullDim T = d :=
    (Homeomorph.Set.univ T).isHomeomorph.topologicalKrullDim_eq.symm.trans (hopen ⊤ hne)
  apply le_antisymm ((topologicalKrullDim_subspace_le T Z).trans_eq htotal)
  obtain ⟨U, hU, hUne, hUZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  rw [← hopen ⟨U, hU⟩ hUne]
  exact (IsEmbedding.inclusion hUZ).isInducing.topologicalKrullDim_le

private theorem minimalPrime_quotient_dimension_of_nonemptyOpen
    {R : Type u} [CommRing R] [IsNoetherianRing R] (d : WithBot ℕ∞)
    (hopen : ∀ U : Opens (PrimeSpectrum R), (U : Set (PrimeSpectrum R)).Nonempty →
      topologicalKrullDim U = d)
    (q : Ideal R) (hq : q ∈ minimalPrimes R) : ringKrullDim (R ⧸ q) = d := by
  let : q.IsPrime := hq.isPrime
  have hZ : PrimeSpectrum.zeroLocus (q : Set R) ∈ irreducibleComponents (PrimeSpectrum R) := by
    rw [PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents, hq.isPrime.radical]
    exact hq
  have heq := (PrimeSpectrum.isEmbedding_comap_of_surjective _ _
    (Ideal.Quotient.mk_surjective (I := q))).toHomeomorph.isHomeomorph.topologicalKrullDim_eq
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker] at heq
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, heq]
  exact component_dimension_of_nonemptyOpen d hopen hZ

/-- Uniform dimension of nonempty open fibre pieces gives the affine dimension formula. -/
public theorem ringKrullDim_eq_add_of_constant_fiber_open_dimension
    {k B A : Type u} [Field k] [IsAlgClosed k]
    [CommRing B] [IsDomain B] [CommRing A] [IsDomain A]
    [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A]
    [Algebra.FiniteType k B] [Algebra.FiniteType k A] [FaithfulSMul B A]
    (d : ℕ)
    (hfiber : ∀ M : Ideal A, M.IsMaximal →
      ∀ U : Opens (PrimeSpectrum (A ⧸ (M.under B).map (algebraMap B A))),
        (U : Set (PrimeSpectrum (A ⧸ (M.under B).map (algebraMap B A)))).Nonempty →
          topologicalKrullDim U = (d : WithBot ℕ∞)) :
    ringKrullDim A = ringKrullDim B + (d : WithBot ℕ∞) := by
  have htr : Algebra.trdeg k A = Algebra.trdeg k B + (d : Cardinal) := by
    apply trdeg_eq_add_of_constant_fiber_components (d : Cardinal) (Cardinal.natCast_lt_aleph0)
    intro M hM q hq hqM
    let J := (M.under B).map (algebraMap B A)
    let : q.IsPrime := hq.isPrime
    have hJq : J ≤ q := hq.le
    obtain ⟨qbar, hqbar, hqbareq⟩ := Ideal.minimalPrimes_eq_comap (I := J) ▸ hq
    let : IsNoetherianRing (A ⧸ J) := Algebra.FiniteType.isNoetherianRing k (A ⧸ J)
    have hdim := minimalPrime_quotient_dimension_of_nonemptyOpen (d : WithBot ℕ∞)
      (hfiber M hM) qbar hqbar
    have hmap : q.map (Ideal.Quotient.mkₐ k J) = qbar := by
      rw [← hqbareq]
      exact Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
    let e : ((A ⧸ J) ⧸ qbar) ≃ₐ[k] A ⧸ q :=
      (Ideal.quotientEquivAlgOfEq k hmap.symm).trans (DoubleQuot.quotQuotEquivQuotOfLEₐ k hJq)
    rw [e.toRingEquiv.ringKrullDim, ringKrullDim_eq_trdeg_toNat (k := k)] at hdim
    have hnat : Cardinal.toNat (Algebra.trdeg k (A ⧸ q)) = d := by exact_mod_cast hdim
    have hfin : Algebra.trdeg k (A ⧸ q) < ℵ₀ := trdeg_lt_aleph0_of_finiteType
    rw [← Cardinal.cast_toNat_of_lt_aleph0 hfin, hnat]
  rw [ringKrullDim_eq_trdeg_toNat (k := k) (A := A),
    ringKrullDim_eq_trdeg_toNat (k := k) (A := B), htr,
    Cardinal.toNat_add (trdeg_lt_aleph0_of_finiteType) (Cardinal.natCast_lt_aleph0)]
  simp

end Theory.AlgebraicGroup.Variety.Geometric.MinimalOrbit
