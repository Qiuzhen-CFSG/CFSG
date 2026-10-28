module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.NoetherNormalization
public import Theory.AlgebraicGroup.Variety.Complete

set_option linter.style.haveILetI false

/-!
# Dimension of geometric varieties

This module equips the reduced separated finite-type scheme model `Geometric` with its
topological Krull dimension.  Its compactness and Noetherian instances come directly from the
quasi-compact, locally finite-type structure morphism to `Spec k`.  The dimension is finite:
a finite affine cover reduces chains of irreducible closed sets to affine charts, and Noether
normalization bounds each chart by a finite polynomial dimension.

For an irreducible geometric variety, every nonempty open has the same dimension.  On an affine
chart this is the standard localization argument: a nonempty open contains a principal open,
and localizing a finite-type domain at a nonzero element preserves its dimension.  Intersecting
arbitrary affine charts with the chosen open then gives the global result.  Consequently
geometric isomorphisms and open dense restrictions preserve dimension, while a proper closed
subvariety has strictly smaller dimension.  The last assertion is proved directly on finite
chains by appending the ambient irreducible closed set.

The finite irreducible decomposition, finite-union containment, and minimal-closed-set lemmas
are the Noetherian tools used in the orbit-boundary argument of Borovoi, *Linear Algebraic
Groups* (`Bor1`), Proposition 1.8.  This file supplies only the underlying variety theory and
does not import groups, actions, or quotients.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u v

private theorem ringKrullDim_le_of_isIntegral
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R := by
  algebraize [f]
  letI : Algebra.IsIntegral R S := ⟨hf⟩
  exact Order.krullDim_le_of_strictMono
    (PrimeSpectrum.comap f) fun _ _ h ↦ Ideal.IsIntegral.comap_lt_comap h

private theorem ringKrullDim_eq_of_isIntegral_of_injective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim S = ringKrullDim R := by
  apply le_antisymm (ringKrullDim_le_of_isIntegral f hf)
  algebraize [f]
  letI : Algebra.IsIntegral R S := ⟨hf⟩
  rw [ringKrullDim, ringKrullDim]
  refine iSup_le fun l ↦ ?_
  obtain ⟨P, hP⟩ := hf.comap_surjective hinj l.head
  letI : P.asIdeal.LiesOver l.head.asIdeal :=
    ⟨(PrimeSpectrum.ext_iff.mp hP).symm⟩
  obtain ⟨L, hlen, -, -⟩ :=
    Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
  rw [← hlen]
  exact Order.LTSeries.length_le_krullDim L

private theorem trdeg_isFractionRing_eq
    {k A K : Type u} [Field k] [CommRing A] [IsDomain A] [Field K]
    [Algebra k A] [Algebra k K] [Algebra A K] [IsScalarTower k A K]
    [IsFractionRing A K] :
    Algebra.trdeg k K = Algebra.trdeg k A := by
  have hAlg : Algebra.IsAlgebraic A K := by
    rw [Algebra.isAlgebraic_def]
    intro x
    rcases (IsLocalization.mk'_surjective (R := A) (M := nonZeroDivisors A)
        (S := K)) x with ⟨⟨a, s⟩, hx⟩
    refine ⟨Polynomial.C (s.1 : A) * Polynomial.X - Polynomial.C a, ?_, ?_⟩
    · intro hp
      have hs0 : (s.1 : A) ≠ 0 := nonZeroDivisors.coe_ne_zero s
      have hc :
          (Polynomial.C (s.1 : A) * Polynomial.X - Polynomial.C a).coeff 1 = s.1 := by
        simp
      exact hs0 (by rw [← hc]; exact congrArg (fun q : Polynomial A ↦ q.coeff 1) hp)
    · rw [← hx]
      simp only [map_sub, map_mul]
      rw [Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.aeval_C]
      have hmul : algebraMap A K (s.1 : A) * IsLocalization.mk' K a s =
          algebraMap A K a := by
        exact IsLocalization.mk'_spec' (R := A) (M := nonZeroDivisors A) (S := K) a s
      rw [hmul, sub_self]
  letI : Algebra.IsAlgebraic A K := hAlg
  letI : FaithfulSMul k A :=
    (faithfulSMul_iff_algebraMap_injective (R := k) (A := A)).mpr <| by
      rw [injective_iff_map_eq_zero]
      intro a ha
      by_contra h
      have hmul : algebraMap k A (a * a⁻¹) = (0 : A) := by
        rw [map_mul, ha, zero_mul]
      have h1 : (1 : A) = 0 := by
        rw [mul_inv_cancel₀ h] at hmul
        simpa only [map_one] using hmul
      exact one_ne_zero h1
  letI : FaithfulSMul A K :=
    (faithfulSMul_iff_algebraMap_injective (R := A) (A := K)).mpr
      (IsFractionRing.injective A K)
  have htrdeg := trdeg_add_eq (R := k) (S := A) (A := K)
  rw [trdeg_eq_zero (R := A) (A := K), add_zero] at htrdeg
  exact htrdeg.symm

private theorem exists_dimension_eq_nat_and_trdeg
    {k A K : Type u} [Field k] [CommRing A] [IsDomain A] [Field K]
    [Algebra k A] [Algebra k K] [Algebra A K] [IsScalarTower k A K]
    [Algebra.FiniteType k A] [IsFractionRing A K] :
    ∃ n : ℕ, ringKrullDim A = (n : WithBot ℕ∞) ∧
      Algebra.trdeg k K = (n : Cardinal) := by
  obtain ⟨n, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg k A
  let B := MvPolynomial (Fin n) k
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq' <| by
    ext x
    exact (g.commutes x).symm
  letI : Algebra.IsIntegral B A := ⟨hgint⟩
  letI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective (R := B) (A := A)).mpr hginj
  have htrA : Algebra.trdeg k A = Algebra.trdeg k B := by
    rw [← trdeg_add_eq (R := k) (S := B) (A := A),
      trdeg_eq_zero (R := B) (A := A), add_zero]
  have htrB : Algebra.trdeg k B = (n : Cardinal) := by
    rw [MvPolynomial.trdeg_of_isDomain]
    simp
  refine ⟨n, ?_, ?_⟩
  · calc
      ringKrullDim A = ringKrullDim B :=
        ringKrullDim_eq_of_isIntegral_of_injective g.toRingHom hgint hginj
      _ = ringKrullDim k + (n : WithBot ℕ∞) := by
        rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
        simp
      _ = (n : WithBot ℕ∞) := by rw [ringKrullDim_eq_zero_of_field]; simp
  · rw [trdeg_isFractionRing_eq (k := k) (A := A) (K := K)]
    exact htrA.trans htrB

private theorem ringKrullDim_localizationAway_eq
    {k A : Type u} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (f : A) (hf : f ≠ 0) :
    ringKrullDim (Localization.Away f) = ringKrullDim A := by
  let B := Localization.Away f
  let K := FractionRing A
  have hM : Submonoid.powers f ≤ nonZeroDivisors A := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hf)
  letI : Algebra k B := OreLocalization.instAlgebra
  letI : SMul k B := Algebra.toSMul
  letI : MulAction k B := Algebra.toModule.toDistribMulAction.toMulAction
  letI : IsScalarTower k A B := OreLocalization.instIsScalarTower
  letI : Algebra.FinitePresentation A B := IsLocalization.Away.finitePresentation f
  letI : Algebra.FiniteType k B :=
    Algebra.FiniteType.trans (R := k) (S := A) (A := B) inferInstance inferInstance
  letI : Algebra B K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe B K
      (Submonoid.powers f) (nonZeroDivisors A) hM
  letI : IsScalarTower A B K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le B K
      (Submonoid.powers f) (nonZeroDivisors A) hM
  letI : IsFractionRing B K :=
    IsFractionRing.isFractionRing_of_isLocalization
      (Submonoid.powers f) B K hM
  letI : IsDomain B :=
    Function.Injective.isDomain (algebraMap B K) (IsFractionRing.injective B K)
  letI : IsScalarTower k B K := IsScalarTower.to₁₃₄ k A B K
  obtain ⟨n, hn, htn⟩ :=
    exists_dimension_eq_nat_and_trdeg (k := k) (A := A) (K := K)
  obtain ⟨m, hm, htm⟩ :=
    exists_dimension_eq_nat_and_trdeg (k := k) (A := B) (K := K)
  have hnm : n = m := by
    exact_mod_cast htn.symm.trans htm
  rw [hm, hn, hnm]

private theorem primeSpectrum_open_topologicalKrullDim_eq
    {k A : Type u} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (U : Set (PrimeSpectrum A))
    (hU : IsOpen U) (hne : U.Nonempty) :
    topologicalKrullDim U = ringKrullDim A := by
  obtain ⟨x, hx⟩ := hne
  rcases PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx hU with
    ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hfU⟩
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hxf
  have hbasic :
      topologicalKrullDim (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) =
        ringKrullDim A := by
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    calc
      topologicalKrullDim
          (Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away f)))) =
          topologicalKrullDim (PrimeSpectrum (Localization.Away f)) :=
        (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away f) f).isEmbedding
          |>.toHomeomorph |>.symm.isHomeomorph.topologicalKrullDim_eq
      _ = ringKrullDim (Localization.Away f) :=
        PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (Localization.Away f)
      _ = ringKrullDim A :=
        ringKrullDim_localizationAway_eq (k := k) (A := A) f hf
  apply le_antisymm
  · exact (topologicalKrullDim_subspace_le _ _).trans_eq
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A)
  · rw [← hbasic]
    exact (Topology.IsEmbedding.inclusion hfU).isInducing.topologicalKrullDim_le

private theorem ringKrullDim_le_nat_of_finiteType
    {k : Type u} {A : Type v} [Field k] [CommRing A]
    (f : k →+* A) (hf : f.FiniteType) :
    ∃ n : ℕ, ringKrullDim A ≤ (n : WithBot ℕ∞) := by
  algebraize [f]
  letI : Algebra.FiniteType k A := hf
  obtain ⟨n, g, hg⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := k) (S := A)).mp inferInstance
  refine ⟨n, (ringKrullDim_le_of_surjective g.toRingHom hg).trans ?_⟩
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

variable {k : Type u} [Field k]

private theorem affineOpen_topologicalKrullDim_le_nat
    (V : Theory.AlgebraicGroup.Variety.Geometric k)
    (U : V.toScheme.Opens) (hU : IsAffineOpen U) :
    ∃ n : ℕ, topologicalKrullDim U ≤ (n : WithBot ℕ∞) := by
  let e : k ≃+* Γ(Spec (.of k), ⊤) :=
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv
  let f : k →+* Γ(V.toScheme, U) :=
    (V.structureMap.appLE ⊤ U (by simp)).hom.comp e.toRingHom
  have hf : f.FiniteType := by
    apply (V.structureMap.finiteType_appLE (isAffineOpen_top _) hU (by simp)).comp
    exact RingHom.FiniteType.of_surjective _ e.surjective
  obtain ⟨n, hn⟩ := ringKrullDim_le_nat_of_finiteType f hf
  refine ⟨n, ?_⟩
  rw [hU.isoSpec.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
  change topologicalKrullDim (PrimeSpectrum Γ(V.toScheme, U)) ≤ _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact hn

private theorem affineOpen_nonemptyOpen_topologicalKrullDim_eq
    (V : Theory.AlgebraicGroup.Variety.Geometric k)
    [IrreducibleSpace V.toScheme]
    (U : V.toScheme.Opens) (hU : IsAffineOpen U)
    (S : Set U) (hS : IsOpen S) (hSne : S.Nonempty) :
    topologicalKrullDim S = topologicalKrullDim U := by
  letI : IsIntegral V.toScheme :=
    isIntegral_of_irreducibleSpace_of_isReduced V.toScheme
  letI : Nonempty U := ⟨hSne.some⟩
  let e := hU.isoSpec.hom.homeomorph
  let T : Set (PrimeSpectrum Γ(V.toScheme, U)) := e '' S
  have hT : IsOpen T := e.isOpenMap S hS
  have hTne : T.Nonempty := hSne.image e
  let ek : k ≃+* Γ(Spec (.of k), ⊤) :=
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv
  let f : k →+* Γ(V.toScheme, U) :=
    (V.structureMap.appLE ⊤ U (by simp)).hom.comp ek.toRingHom
  have hf : f.FiniteType := by
    apply (V.structureMap.finiteType_appLE (isAffineOpen_top _) hU (by simp)).comp
    exact RingHom.FiniteType.of_surjective _ ek.surjective
  algebraize [f]
  letI : Algebra.FiniteType k Γ(V.toScheme, U) := hf
  calc
    topologicalKrullDim S = topologicalKrullDim T :=
      (e.image S).isHomeomorph.topologicalKrullDim_eq
    _ = ringKrullDim Γ(V.toScheme, U) :=
      primeSpectrum_open_topologicalKrullDim_eq
        (k := k) (A := Γ(V.toScheme, U)) T hT hTne
    _ = topologicalKrullDim (PrimeSpectrum Γ(V.toScheme, U)) :=
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(V.toScheme, U)).symm
    _ = topologicalKrullDim U :=
      e.isHomeomorph.topologicalKrullDim_eq.symm

/-- A geometric variety is compact as a Zariski space. -/
instance compactSpace (V : Theory.AlgebraicGroup.Variety.Geometric k) :
    CompactSpace V.toScheme :=
  QuasiCompact.compactSpace_of_compactSpace V.structureMap

/-- A finite-type geometric variety is locally Noetherian. -/
instance isLocallyNoetherian (V : Theory.AlgebraicGroup.Variety.Geometric k) :
    IsLocallyNoetherian V.toScheme :=
  LocallyOfFiniteType.isLocallyNoetherian V.structureMap

/-- A quasi-compact, locally Noetherian geometric variety is Noetherian. -/
instance isNoetherian (V : Theory.AlgebraicGroup.Variety.Geometric k) :
    IsNoetherian V.toScheme where

/-- Every closed locus is a finite union of irreducible closed loci. -/
theorem exists_finite_irreducibleClosed_cover
    (V : Theory.AlgebraicGroup.Variety.Geometric k)
    {Z : Set V.toScheme} (hZ : IsClosed Z) :
    ∃ S : Set (Set V.toScheme), S.Finite ∧
      (∀ W ∈ S, IsClosed W) ∧
        (∀ W ∈ S, _root_.IsIrreducible W) ∧ Z = ⋃₀ S :=
  NoetherianSpace.exists_finite_set_isClosed_irreducible hZ

/-- An irreducible locus covered by finitely many closed loci lies in one of them. -/
theorem irreducible_subset_sUnion_finset_closed
    (V : Theory.AlgebraicGroup.Variety.Geometric k)
    {Z : Set V.toScheme} (hZ : _root_.IsIrreducible Z)
    (S : Finset (Set V.toScheme)) (hS : ∀ W ∈ S, IsClosed W)
    (hZS : Z ⊆ ⋃₀ (S : Set (Set V.toScheme))) :
    ∃ W ∈ S, Z ⊆ W :=
  isIrreducible_iff_sUnion_isClosed.mp hZ S hS hZS

/-- Every nonempty family of closed loci has an inclusion-minimal member. -/
theorem exists_minimal_closed
    (V : Theory.AlgebraicGroup.Variety.Geometric k)
    (S : Set (Closeds V.toScheme)) (hS : S.Nonempty) :
    ∃ Z ∈ S, ∀ W ∈ S, ¬ W < Z :=
  wellFounded_lt.has_min S hS

/-- The dimension of a geometric variety is the Krull dimension of its Zariski space. -/
noncomputable def dimension
    (V : Theory.AlgebraicGroup.Variety.Geometric k) : WithBot ℕ∞ :=
  topologicalKrullDim V.toScheme

@[simp]
theorem dimension_eq_topologicalKrullDim
    (V : Theory.AlgebraicGroup.Variety.Geometric k) :
    dimension V = topologicalKrullDim V.toScheme := rfl

/-- An irreducible geometric variety and any of its nonempty open loci have equal dimension. -/
theorem dimension_eq_nonemptyOpen
    (V : Theory.AlgebraicGroup.Variety.Geometric k)
    [IrreducibleSpace V.toScheme]
    (U : V.toScheme.Opens)
    (hUne : (U : Set V.toScheme).Nonempty) :
    dimension V = topologicalKrullDim U := by
  apply le_antisymm
  · change Order.krullDim (IrreducibleCloseds V.toScheme) ≤ _
    refine iSup_le fun p ↦ ?_
    obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
    obtain ⟨i, y, hy⟩ := V.toScheme.affineCover.exists_eq x
    let W : V.toScheme.Opens := (V.toScheme.affineCover.f i).opensRange
    have hW : IsAffineOpen W := isAffineOpen_opensRange _
    have hWne : (W : Set V.toScheme).Nonempty := by
      refine ⟨(V.toScheme.affineCover.f i) y, ?_⟩
      rw [Scheme.Hom.coe_opensRange]
      exact Set.mem_range_self y
    have hWU : ((W : Set V.toScheme) ∩ (U : Set V.toScheme)).Nonempty :=
      nonempty_preirreducible_inter W.2 U.2 hWne hUne
    let S : Set W := {z | z.1 ∈ U}
    have hS : IsOpen S := U.2.preimage continuous_subtype_val
    have hSne : S.Nonempty := by
      obtain ⟨z, hzW, hzU⟩ := hWU
      exact ⟨⟨z, hzW⟩, hzU⟩
    have hSW : topologicalKrullDim S = topologicalKrullDim W :=
      affineOpen_nonemptyOpen_topologicalKrullDim_eq V W hW S hS hSne
    let j : S → U := fun z ↦ ⟨z.1.1, z.2⟩
    have hj : Topology.IsEmbedding j := by
      have hbase : Topology.IsEmbedding (fun z : S ↦ (z.1.1 : V.toScheme)) :=
        (show Topology.IsEmbedding (fun z : W ↦ (z.1 : V.toScheme)) from
          Topology.IsEmbedding.subtypeVal).comp
          (show Topology.IsEmbedding (fun z : S ↦ (z.1 : W)) from
            Topology.IsEmbedding.subtypeVal)
      exact hbase.codRestrict U (fun z ↦ z.2)
    let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding
      (V.toScheme.affineCover.f i)
      (Scheme.Hom.isOpenEmbedding (V.toScheme.affineCover.f i))
    have hnonempty (a : Fin (p.length + 1)) :
        ((V.toScheme.affineCover.f i) ⁻¹' (p a : Set V.toScheme)).Nonempty := by
      refine ⟨y, ?_⟩
      change (V.toScheme.affineCover.f i) y ∈ (p a : Set V.toScheme)
      rw [hy]
      exact p.head_le a hx
    let q : LTSeries (IrreducibleCloseds (V.toScheme.affineCover.X i)) :=
      LTSeries.mk p.length
        (fun a ↦ e.symm ⟨p a, hnonempty a⟩)
        (fun _ _ h ↦ e.symm.strictMono (p.strictMono h))
    have hq : (p.length : WithBot ℕ∞) ≤
        topologicalKrullDim (V.toScheme.affineCover.X i) := by
      exact Order.LTSeries.length_le_krullDim q
    calc
      (p.length : WithBot ℕ∞) ≤
          topologicalKrullDim (V.toScheme.affineCover.X i) := hq
      _ = topologicalKrullDim W :=
        (Scheme.Hom.isOpenEmbedding (V.toScheme.affineCover.f i)).isEmbedding.toHomeomorph
          |>.isHomeomorph.topologicalKrullDim_eq
      _ = topologicalKrullDim S := hSW.symm
      _ ≤ topologicalKrullDim U := hj.isInducing.topologicalKrullDim_le
  · exact topologicalKrullDim_subspace_le _ _

/-- Geometric isomorphisms preserve dimension. -/
theorem dimension_eq_of_isIso
    {V W : Theory.AlgebraicGroup.Variety.Geometric k}
    (f : Morphism V W) [IsIso f.hom] :
    dimension V = dimension W :=
  f.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq

/-- A nonempty open subvariety of an irreducible geometric variety has the same dimension. -/
theorem dimension_eq_of_isOpenImmersion
    {U V : Theory.AlgebraicGroup.Variety.Geometric k}
    (f : Morphism U V) [IsOpenImmersion f.hom]
    [IrreducibleSpace V.toScheme] [Nonempty U.toScheme] :
    dimension U = dimension V := by
  letI : IsIntegral V.toScheme :=
    isIntegral_of_irreducibleSpace_of_isReduced V.toScheme
  letI : IsIntegral U.toScheme :=
    isIntegral_of_isOpenImmersion f.hom
  letI : IrreducibleSpace U.toScheme :=
    (Scheme.Hom.isOpenEmbedding f.hom).irreducibleSpace
  have hrangeNe : (f.hom.opensRange : Set V.toScheme).Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty U.toScheme)
    refine ⟨f.hom x, ?_⟩
    rw [Scheme.Hom.coe_opensRange]
    exact Set.mem_range_self x
  calc
    dimension U = topologicalKrullDim U.toScheme := rfl
    _ = topologicalKrullDim (f.hom.opensRange : Set V.toScheme) :=
      (Scheme.Hom.isOpenEmbedding f.hom).isEmbedding.toHomeomorph
        |>.isHomeomorph.topologicalKrullDim_eq
    _ = dimension V := (dimension_eq_nonemptyOpen V f.hom.opensRange hrangeNe).symm

/-- An open dense geometric restriction of an irreducible variety preserves dimension. -/
theorem dimension_eq_of_openDenseImmersion
    {U V : Theory.AlgebraicGroup.Variety.Geometric k}
    (f : Morphism U V) [IsOpenImmersion f.hom]
    [IrreducibleSpace V.toScheme] (hf : DenseRange f.hom) :
    dimension U = dimension V := by
  letI : Nonempty U.toScheme := hf.nonempty
  exact dimension_eq_of_isOpenImmersion f

/-- Every finite-type geometric variety has finite topological Krull dimension. -/
theorem dimension_lt_top (V : Theory.AlgebraicGroup.Variety.Geometric k) :
    dimension V < ⊤ := by
  let 𝒰 := V.toScheme.affineCover.finiteSubcover
  have hbound : ∀ i : 𝒰.I₀,
      ∃ n : ℕ, topologicalKrullDim ((𝒰.f i).opensRange : Set V.toScheme) ≤
        (n : WithBot ℕ∞) := by
    intro i
    exact affineOpen_topologicalKrullDim_le_nat V _ (isAffineOpen_opensRange _)
  choose b hb using hbound
  let B : ℕ := Finset.univ.sup b
  suffices dimension V < ((B + 1 : ℕ) : WithBot ℕ∞) from this.trans_le le_top
  change Order.krullDim (IrreducibleCloseds V.toScheme) < _
  rw [Order.krullDim_lt_coe_iff]
  intro p
  obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
  let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding
    (𝒰.f i) (Scheme.Hom.isOpenEmbedding (𝒰.f i))
  have hnonempty (j : Fin (p.length + 1)) :
      ((𝒰.f i) ⁻¹' (p j : Set V.toScheme)).Nonempty := by
    refine ⟨y, ?_⟩
    change (𝒰.f i) y ∈ (p j : Set V.toScheme)
    rw [hy]
    exact p.head_le j hx
  let q : LTSeries (IrreducibleCloseds (𝒰.X i)) :=
    LTSeries.mk p.length
      (fun j ↦ e.symm ⟨p j, hnonempty j⟩)
      (fun _ _ h ↦ e.symm.strictMono (p.strictMono h))
  have hq : (q.length : WithBot ℕ∞) ≤
      topologicalKrullDim (𝒰.X i) :=
    Order.LTSeries.length_le_krullDim q
  change (p.length : WithBot ℕ∞) ≤ topologicalKrullDim (𝒰.X i) at hq
  have hchart : topologicalKrullDim (𝒰.X i) ≤ (b i : WithBot ℕ∞) := by
    calc
      topologicalKrullDim (𝒰.X i) =
          topologicalKrullDim ((𝒰.f i).opensRange : Set V.toScheme) :=
        (Scheme.Hom.isOpenEmbedding (𝒰.f i)).isEmbedding.toHomeomorph
          |>.isHomeomorph.topologicalKrullDim_eq
      _ ≤ (b i : WithBot ℕ∞) := hb i
  have hi : b i ≤ B := Finset.le_sup (s := Finset.univ) (Finset.mem_univ i)
  have hi' : (b i : WithBot ℕ∞) ≤ (B : WithBot ℕ∞) := by
    exact_mod_cast hi
  have hcast : (p.length : WithBot ℕ∞) ≤ (B : WithBot ℕ∞) := by
    exact hq.trans (hchart.trans hi')
  exact Nat.lt_succ_of_le (by exact_mod_cast hcast)

private theorem topologicalKrullDim_lt_of_isClosedEmbedding
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [IrreducibleSpace Y] (f : X → Y) (hf : Topology.IsClosedEmbedding f)
    (hnot : ¬ Function.Surjective f)
    (hfinite : topologicalKrullDim Y < ⊤) :
    topologicalKrullDim X < topologicalKrullDim Y := by
  let topY : IrreducibleCloseds Y :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩
  letI : Nonempty (IrreducibleCloseds Y) := ⟨topY⟩
  have hYneBot : topologicalKrullDim Y ≠ ⊥ := by
    exact ne_of_gt Order.bot_lt_krullDim
  have hYneTop : topologicalKrullDim Y ≠ ⊤ := ne_of_lt hfinite
  letI : FiniteDimensionalOrder (IrreducibleCloseds Y) :=
    Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mpr
      ⟨hYneBot, hYneTop⟩
  cases isEmpty_or_nonempty X with
  | inl hX =>
      letI : IsEmpty (IrreducibleCloseds X) :=
        ⟨fun C ↦ hX.false C.isIrreducible.nonempty.choose⟩
      have hbot : topologicalKrullDim X = ⊥ := by
        exact Order.krullDim_eq_bot
      rw [hbot]
      exact Order.bot_lt_krullDim
  | inr hX =>
      letI : Nonempty (IrreducibleCloseds X) :=
        ⟨⟨closure ({Classical.choice hX} : Set X),
          isIrreducible_singleton.closure, isClosed_closure⟩⟩
      let mapClosed : IrreducibleCloseds X → IrreducibleCloseds Y :=
        IrreducibleCloseds.map f hf.continuous
      have hmap : StrictMono mapClosed :=
        IrreducibleCloseds.map_strictMono_of_isInducing hf.isInducing
      have hXfinite : topologicalKrullDim X < ⊤ :=
        lt_of_le_of_lt (Order.krullDim_le_of_strictMono mapClosed hmap) hfinite
      have hXneBot : topologicalKrullDim X ≠ ⊥ := by
        exact ne_of_gt Order.bot_lt_krullDim
      letI : FiniteDimensionalOrder (IrreducibleCloseds X) :=
        Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mpr
          ⟨hXneBot, ne_of_lt hXfinite⟩
      let p := LTSeries.longestOf (IrreducibleCloseds X)
      let q := p.map mapClosed fun _ _ h ↦ hmap h
      have hlast : q.last < topY := by
        apply lt_of_le_of_ne
        · intro y _
          trivial
        intro heq
        apply hnot
        rw [← Set.range_eq_univ]
        apply Set.Subset.antisymm (Set.subset_univ _)
        intro y hy
        have hy' : y ∈ (q.last : Set Y) := by simp [topY, heq]
        have hsub : (q.last : Set Y) ⊆ Set.range f := by
          change closure (f '' (p.last : Set X)) ⊆ Set.range f
          exact closure_minimal (Set.image_subset_range f _) hf.isClosed_range
        exact hsub hy'
      let r := q.snoc topY hlast
      have hlen := LTSeries.longestOf_is_longest r
      change p.length + 1 ≤ (LTSeries.longestOf (IrreducibleCloseds Y)).length at hlen
      have hnat : p.length < (LTSeries.longestOf (IrreducibleCloseds Y)).length := by
        apply Nat.lt_of_succ_le
        exact hlen
      rw [topologicalKrullDim, topologicalKrullDim,
        Order.krullDim_eq_length_of_finiteDimensionalOrder,
        Order.krullDim_eq_length_of_finiteDimensionalOrder]
      exact_mod_cast hnat

/-- A proper closed subvariety of an irreducible geometric variety has smaller dimension. -/
theorem closedSubvariety_dimension_lt
    (V : Theory.AlgebraicGroup.Variety.Geometric k)
    (Z : ClosedSubvariety V) [IrreducibleSpace V.toScheme]
    (hproper : ¬ Function.Surjective Z.inclusion.hom) :
    dimension Z.toGeometric < dimension V := by
  exact topologicalKrullDim_lt_of_isClosedEmbedding Z.inclusion.hom
    (IsClosedImmersion.isClosedEmbedding Z.inclusion.hom) hproper (dimension_lt_top V)

/-- A proper closed locus in an irreducible geometric variety has smaller dimension. -/
theorem closed_subset_dimension_lt
    (V : Theory.AlgebraicGroup.Variety.Geometric k)
    [IrreducibleSpace V.toScheme]
    {Z : Set V.toScheme} (hZ : IsClosed Z) (hproper : Z ≠ Set.univ) :
    topologicalKrullDim Z < dimension V := by
  have hnot : ¬ Function.Surjective ((↑) : Z → V.toScheme) := by
    intro hs
    apply hproper
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨z, hz⟩ := hs x
    rw [← hz]
    exact z.2
  exact topologicalKrullDim_lt_of_isClosedEmbedding ((↑) : Z → V.toScheme)
    hZ.isClosedEmbedding_subtypeVal hnot (dimension_lt_top V)

end Theory.AlgebraicGroup.Variety.Geometric
