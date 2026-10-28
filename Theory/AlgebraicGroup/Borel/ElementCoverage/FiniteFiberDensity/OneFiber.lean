module

public import Theory.AlgebraicGroup.Dimension.Fiber
import all Theory.AlgebraicGroup.Dimension.Fiber

/-!
# Dominance from the dimension of one nonempty fibre

For irreducible affine varieties, a fibre whose irreducible closed subsets
have dimension at most `d` forces dominance when the source dimension is
the target dimension plus `d`. The maximal-ideal height inequality is applied
at a chosen point of that fibre, after quotienting out the pullback kernel.
This extends the affine finite-fibre argument to positive-dimensional fibres
and requires a bound at only one point of the target.

Source: Borel, *Linear Algebraic Groups*, §11.9(2),
`refs/KGroup/Bor1/Chapter4.tex`; the height argument extends
`Theory.AlgebraicGroup.Dimension.Fiber`.
-/

open Cardinal Topology
namespace Theory.AlgebraicGroup.BorelElementCoverage

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A single nonempty fibre of the expected dimension forces dominance.
The fibre may be nonreduced and need not be finite. -/
public theorem denseRange_of_one_fiber_dimension_le
    {V W : Variety k} (f : Variety.Morphism V W)
    (hVi : IsIrreducible (Set.univ : Set (Variety.Point V)))
    (hWi : IsIrreducible (Set.univ : Set (Variety.Point W)))
    (d : Cardinal) (hd : d < ℵ₀)
    (hdim : Variety.dimension V = Variety.dimension W + d)
    (g : Variety.Point V)
    (hfiber : ∀ (S : Set (Variety.Point V)) (hS : IsZariskiClosed V S),
      IsIrreducible S → S ⊆ {x | f.toFun x = f.toFun g} →
        Variety.dimension (Variety.closedSubvariety hS) ≤ d) :
    Dense (Set.range f.toFun) := by
  classical
  let A := Variety.PolynomialFunction V
  let B := Variety.PolynomialFunction W
  let : Algebra k A := polynomialFunctionAlgebra V
  let : Algebra k B := polynomialFunctionAlgebra W
  let : IsDomain (coordinateRing V) :=
    isDomain_coordinateRing_of_isIrreducible V hVi
  let : IsDomain A :=
    (coordinateRingAlgEquivPolynomialFunction V).toRingEquiv.isDomain_iff.mp
      inferInstance
  let : IsDomain (coordinateRing W) :=
    isDomain_coordinateRing_of_isIrreducible W hWi
  let : IsDomain B :=
    (coordinateRingAlgEquivPolynomialFunction W).toRingEquiv.isDomain_iff.mp
      inferInstance
  let : Algebra.FiniteType k A := polynomialFunction_finiteType V
  let : Algebra.FiniteType k B := polynomialFunction_finiteType W
  let φ : B →ₐ[k] A := f.pullbackAlgHom
  let P : Ideal B := RingHom.ker φ
  have hPprime : P.IsPrime := RingHom.ker_isPrime (f := φ.toRingHom)
  let : P.IsPrime := hPprime
  let B₀ := B ⧸ P
  let πP : B →ₐ[k] B₀ := Ideal.Quotient.mkₐ k P
  let φ₀ : B₀ →ₐ[k] A := Ideal.kerLiftAlg φ
  let : Algebra B₀ A := φ₀.toRingHom.toAlgebra
  have hφ₀inj : Function.Injective φ₀ := Ideal.kerLiftAlg_injective φ
  let : FaithfulSMul B₀ A :=
    (faithfulSMul_iff_algebraMap_injective B₀ A).mpr hφ₀inj
  let : IsScalarTower k B₀ A := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap k A r =
      Ideal.kerLiftAlg φ (Ideal.Quotient.mk P (algebraMap k B r))
    rw [Ideal.kerLiftAlg_mk φ]
    exact (φ.commutes r).symm
  let : Algebra.FiniteType k B₀ :=
    Algebra.FiniteType.of_surjective πP Ideal.Quotient.mk_surjective
  let : Algebra.FiniteType B₀ A :=
    Algebra.FiniteType.of_restrictScalars_finiteType k B₀ A
  let M : Ideal A := (V.pointPrime g).asIdeal
  let NY : Ideal B := (W.pointPrime (f.toFun g)).asIdeal
  have hP_le_NY : P ≤ NY := by
    change RingHom.ker f.pullbackAlgHom ≤
      (W.pointPrime (f.toFun g)).asIdeal
    rw [f.pointPrime_image g]
    intro b hb
    change f.pullbackRingHom b = 0 at hb
    change f.pullbackRingHom b ∈ (V.pointPrime g).asIdeal
    rw [hb]
    exact (V.pointPrime g).asIdeal.zero_mem
  let N : Ideal B₀ := NY.map πP
  have hMmax : M.IsMaximal := V.pointPrime_isMaximal g
  have hNYmax : NY.IsMaximal := W.pointPrime_isMaximal (f.toFun g)
  have hNmax : N.IsMaximal := by
    dsimp only [N]
    apply Ideal.IsMaximal.map_of_surjective_of_ker_le
      Ideal.Quotient.mk_surjective
    change RingHom.ker (Ideal.Quotient.mk P) ≤ NY
    rw [Ideal.mk_ker]
    exact hP_le_NY
  let : M.IsMaximal := hMmax
  let : M.IsPrime := hMmax.isPrime
  let : N.IsMaximal := hNmax
  let : N.IsPrime := hNmax.isPrime
  have hφcomp : φ₀.toRingHom.comp πP.toRingHom = φ.toRingHom := by
    apply RingHom.ext
    intro b
    exact Ideal.kerLiftAlg_mk φ b
  have hMN : M.under B₀ = N := by
    apply Ideal.comap_injective_of_surjective πP.toRingHom
      Ideal.Quotient.mk_surjective
    rw [Ideal.comap_comap]
    change M.comap (φ₀.toRingHom.comp πP.toRingHom) =
      (NY.map πP.toRingHom).comap πP.toRingHom
    rw [hφcomp, Ideal.comap_map_of_surjective πP.toRingHom
      Ideal.Quotient.mk_surjective]
    rw [← RingHom.ker_eq_comap_bot,
      show RingHom.ker πP.toRingHom = P from Ideal.mk_ker,
      sup_eq_left.mpr hP_le_NY]
    exact congrArg PrimeSpectrum.asIdeal (f.pointPrime_image g).symm
  have hMNlies : M.LiesOver N := ⟨hMN.symm⟩
  let : M.LiesOver N := hMNlies
  let J : Ideal A := N.map (algebraMap B₀ A)
  have hJfiber : J = morphismFiberIdeal f (f.toFun g) := by
    change (NY.map πP.toRingHom).map φ₀.toRingHom =
      NY.map f.pullbackRingHom
    rw [Ideal.map_map, hφcomp]
    rfl
  have hJM : J ≤ M := by
    rw [hJfiber]
    exact (mem_polynomialFunctionIdealZeroSet_iff_le_pointPrime V
      (morphismFiberIdeal f (f.toFun g)) g).mp <| by
        rw [polynomialFunctionIdealZeroSet_morphismFiberIdeal]
        rfl
  let πJ : A →+* A ⧸ J := Ideal.Quotient.mk J
  let Mbar : Ideal (A ⧸ J) := M.map πJ
  have hcomapBotJ : (⊥ : Ideal (A ⧸ J)).comap πJ = J := by
    change RingHom.ker πJ = J
    exact Ideal.mk_ker
  have hMbarmax : Mbar.IsMaximal := by
    dsimp only [Mbar]
    apply Ideal.IsMaximal.map_of_surjective_of_ker_le
      Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker]
    exact hJM
  let : Mbar.IsMaximal := hMbarmax
  let : Mbar.IsPrime := hMbarmax.isPrime
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let : IsNoetherianRing B₀ := Algebra.FiniteType.isNoetherianRing k B₀
  have hfiberheight : Mbar.height ≤ (Cardinal.toNat d : ℕ∞) := by
    apply height_le_of_minimalPrimes_quotient_height_le
    intro qbar hqbar hqbarM
    let : qbar.IsPrime := hqbar.isPrime
    let q0 : Ideal A := qbar.comap πJ
    have hq0prime : q0.IsPrime := Ideal.comap_isPrime πJ qbar
    let : q0.IsPrime := hq0prime
    have hJq0 : J ≤ q0 := by
      change J ≤ qbar.comap πJ
      intro a ha
      change πJ a ∈ qbar
      rw [show πJ a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact qbar.zero_mem
    have hq0M : q0 ≤ M := by
      have hcomapM : (M.map πJ).comap πJ = M := by
        rw [Ideal.comap_map_of_surjective πJ Ideal.Quotient.mk_surjective,
          hcomapBotJ]
        exact sup_eq_left.mpr hJM
      exact (Ideal.comap_mono (f := πJ) hqbarM).trans_eq hcomapM
    have htrq0 : Algebra.trdeg k (A ⧸ q0) ≤ d := by
      rw [← dimension_closedSubvariety_polynomialFunctionIdealZeroSet_of_isPrime V q0]
      apply hfiber _ (polynomialFunctionIdealZeroSet_isZariskiClosed V q0)
        (polynomialFunctionIdealZeroSet_isIrreducible_of_isPrime V q0)
      intro x hx
      rw [← polynomialFunctionIdealZeroSet_morphismFiberIdeal f (f.toFun g),
        ← hJfiber]
      exact fun a ha => hx a (hJq0 ha)
    have hmapq0 : q0.map πJ = qbar :=
      Ideal.map_comap_of_surjective πJ Ideal.Quotient.mk_surjective qbar
    let e0 : ((A ⧸ J) ⧸ qbar) ≃ₐ[k]
        ((A ⧸ J) ⧸ q0.map (Ideal.Quotient.mkₐ k J)) :=
      Ideal.quotientEquivAlgOfEq k hmapq0.symm
    let e1 : ((A ⧸ J) ⧸ q0.map (Ideal.Quotient.mkₐ k J)) ≃ₐ[k]
        A ⧸ q0 := DoubleQuot.quotQuotEquivQuotOfLEₐ k hJq0
    let e := e0.trans e1
    have hqbarMmax :
        (Mbar.map (Ideal.Quotient.mk qbar)).IsMaximal := by
      apply Ideal.IsMaximal.map_of_surjective_of_ker_le
        Ideal.Quotient.mk_surjective
      rw [Ideal.mk_ker]
      exact hqbarM
    let : (Mbar.map (Ideal.Quotient.mk qbar)).IsMaximal := hqbarMmax
    let : Algebra.FiniteType k (A ⧸ J) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k J)
        Ideal.Quotient.mk_surjective
    let : Algebra.FiniteType k ((A ⧸ J) ⧸ qbar) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k qbar)
        Ideal.Quotient.mk_surjective
    rw [domain_maximal_height_eq_trdeg (k := k) ((A ⧸ J) ⧸ qbar)
      (Mbar.map (Ideal.Quotient.mk qbar)), e.trdeg_eq]
    exact_mod_cast (Cardinal.toNat_le_iff_le_of_lt_aleph0
      (trdeg_lt_aleph0_of_finiteType (R := k) (S := A ⧸ q0)) hd).mpr htrq0
  have hheightMain : M.height ≤ N.height + Mbar.height := by
    have h := Ideal.height_le_height_add_of_liesOver N M
    simpa only [J, Mbar, πJ] using h
  have hheightTotal : M.height ≤ N.height + (Cardinal.toNat d : ℕ∞) :=
    hheightMain.trans (add_le_add le_rfl hfiberheight)
  have hNat : Cardinal.toNat (Algebra.trdeg k A) ≤
      Cardinal.toNat (Algebra.trdeg k B₀) + Cardinal.toNat d := by
    have h' : (Cardinal.toNat (Algebra.trdeg k A) : ℕ∞) ≤
        (Cardinal.toNat (Algebra.trdeg k B₀) : ℕ∞) + (Cardinal.toNat d : ℕ∞) := by
      rw [← domain_maximal_height_eq_trdeg A M,
        ← domain_maximal_height_eq_trdeg B₀ N]
      exact hheightTotal
    exact_mod_cast h'
  have hBfin : Algebra.trdeg k B < ℵ₀ := trdeg_lt_aleph0_of_finiteType
  have hB₀fin : Algebra.trdeg k B₀ < ℵ₀ := trdeg_lt_aleph0_of_finiteType
  have htrAB : Algebra.trdeg k A = Algebra.trdeg k B + d := by
    rw [← dimension_eq_trdeg_polynomialFunction_of_isIrreducible V hVi,
      ← dimension_eq_trdeg_polynomialFunction_of_isIrreducible W hWi]
    exact hdim
  rw [htrAB, Cardinal.toNat_add hBfin hd] at hNat
  have htrle : Algebra.trdeg k B ≤ Algebra.trdeg k B₀ :=
    (Cardinal.toNat_le_iff_le_of_lt_aleph0 hBfin hB₀fin).mp
      (Nat.le_of_add_le_add_right hNat)
  have hPbot : P = ⊥ := by
    by_contra hP
    have hstrict : Algebra.trdeg k B₀ < Algebra.trdeg k B :=
      trdeg_quotient_lt_of_ne_bot B P hP
    exact (not_lt_of_ge htrle) hstrict
  apply f.denseRange_of_pullback_injective
  exact (RingHom.injective_iff_ker_eq_bot φ.toRingHom).mpr hPbot

end Theory.AlgebraicGroup.BorelElementCoverage
