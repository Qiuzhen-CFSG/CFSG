module

public import Theory.AlgebraicGroup.Variety.ProjectiveLinearAction
public import Theory.AlgebraicGroup.Variety.GeometricDimension
public import Theory.AlgebraicGroup.Dimension.Fiber
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.MinimalOrbit.DimensionBridge
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
/-!
# Dimension of a projective hyperplane section

A nonunit principal equation in a finite-type domain has codimension at most
one, by the principal ideal height theorem and the dimension formula for
maximal ideals. On a projective coordinate chart, a homogeneous linear
polynomial is the literal regular fraction p/Xᵢ. Pulling that fraction back
along a closed immersion proves the dimension estimate for the actual
hyperplane section.

This supplies the dimensional step in Borel, *Linear Algebraic Groups*, §13.5,
used in the rank-one argument of §§13.9 and 13.13. No smoothness, separability,
or group classification is assumed.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HomogeneousLocalization
namespace Theory.AlgebraicGroup.Variety.Geometric
universe u
variable {k : Type u} [Field k] {σ : Type} [Finite σ]
local notation "Gr" => projectiveGrading k σ

omit [Finite σ] in
private theorem hyperplane_ratio_mem_affine_prime
    (p q : MvPolynomial σ k) (hp : p∈Gr 1) (hq : q∈Gr 1)
    (x : (Proj.basicOpen Gr q).toScheme) :
    Away.mk Gr hq 1 p (by simpa using hp) ∈
      ((Proj.basicOpenIsoSpec Gr q hq Nat.zero_lt_one).hom x).asIdeal ↔
      p ∈ x.1.asHomogeneousIdeal := by
  change Away.mk Gr hq 1 p (by simpa using hp) ∈
    ((ProjectiveSpectrum.Proj.toSpec Gr q).base x).asIdeal ↔ _
  exact ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply Gr x _


include k in
omit [Finite σ] in
private theorem principal_quotient_bound {A : Type u} [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (f : A) (hf : ¬IsUnit f) :
    ringKrullDim A ≤ ringKrullDim (A ⧸ Ideal.span {f})+1 := by
  obtain ⟨M,hM,hfM⟩ := Ideal.exists_le_maximal (Ideal.span {f}) (by simpa using hf)
  let : M.IsMaximal := hM
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hheight := domain_maximal_height_eq_trdeg (k := k) A M
  have hdim := MinimalOrbit.ringKrullDim_eq_trdeg_toNat (k := k) (A := A)
  have he : (M.height : WithBot ℕ∞)=ringKrullDim A := by rw [hheight,hdim]; rfl
  rw [←he]
  exact Ideal.height_le_ringKrullDim_quotient_add_one (hfM (Ideal.subset_span (by simp)))

omit [Finite σ] in
/-- An actual local principal equation through a point bounds codimension by one. -/
theorem dimension_le_principal_locus_add_one (X : Geometric k)
    [IrreducibleSpace X.toScheme] (U : X.toScheme.Opens) (hU : IsAffineOpen U)
    (Y : Set X.toScheme) (r : Γ(X.toScheme,U))
    (hY : ∀ x : U, r ∈ (hU.isoSpec.hom x).asIdeal ↔ x.1 ∈ Y)
    (hne : (Y ∩ (U : Set X.toScheme)).Nonempty) :
    dimension X ≤ topologicalKrullDim Y+1 := by
  let : IsIntegral X.toScheme := isIntegral_of_irreducibleSpace_of_isReduced X.toScheme
  obtain ⟨x,hxY,hxU⟩ := hne
  let : Nonempty U := ⟨⟨x,hxU⟩⟩
  let e := hU.isoSpec.hom.homeomorph
  let A := Γ(X.toScheme,U)
  let ek : k ≃+* Γ(Spec (.of k),⊤) :=
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv
  let f : k →+* A := (X.structureMap.appLE ⊤ U (by simp)).hom.comp ek.toRingHom
  have hf : f.FiniteType := by
    apply (X.structureMap.finiteType_appLE (isAffineOpen_top _) hU (by simp)).comp
    exact RingHom.FiniteType.of_surjective _ ek.surjective
  algebraize [f]
  let : Algebra.FiniteType k A := hf
  have hru : ¬IsUnit r := by
    intro hr
    have hm := (hY ⟨x,hxU⟩).mpr hxY
    exact (hU.isoSpec.hom ⟨x,hxU⟩).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hm hr)
  have hbound := principal_quotient_bound (k := k) r hru
  let π := Ideal.Quotient.mk (Ideal.span {r})
  let j : PrimeSpectrum (A ⧸ Ideal.span {r}) → X.toScheme :=
    fun p => (e.symm (PrimeSpectrum.comap π p)).1
  have hjY (p : PrimeSpectrum (A ⧸ Ideal.span {r})) : j p ∈ Y := by
    apply (hY (e.symm (PrimeSpectrum.comap π p))).mp
    change r ∈ (e (e.symm (PrimeSpectrum.comap π p))).asIdeal
    erw [e.apply_symm_apply]
    change π r ∈ p.asIdeal
    have hz : π r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    rw [hz]
    exact p.asIdeal.zero_mem
  have hj : Topology.IsEmbedding j :=
    Topology.IsEmbedding.subtypeVal.comp (e.symm.isEmbedding.comp
      (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ π Ideal.Quotient.mk_surjective).isEmbedding)
  have hdimY : ringKrullDim (A ⧸ Ideal.span {r}) ≤ topologicalKrullDim Y := by
    rw [←PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact (hj.codRestrict Y hjY).isInducing.topologicalKrullDim_le
  calc
    dimension X = topologicalKrullDim U := dimension_eq_nonemptyOpen X U ⟨x,hxU⟩
    _ = ringKrullDim A := e.isHomeomorph.topologicalKrullDim_eq.trans
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A)
    _ ≤ ringKrullDim (A ⧸ Ideal.span {r})+1 := hbound
    _ ≤ topologicalKrullDim Y+1 := add_le_add_left hdimY 1
omit [Finite σ] in
private theorem affine_prime_mem_iff_not_basicOpen {X : Scheme} {U : X.Opens}
    (hU : IsAffineOpen U) (r : Γ(X,U)) (x : U) :
    r ∈ (hU.isoSpec.hom x).asIdeal ↔ x.1 ∉ X.basicOpen r := by
  have h := congrArg (fun W : U.toScheme.Opens => x ∈ W)
    (Scheme.Opens.toSpecΓ_preimage_basicOpen U r)
  change (r ∉ (U.toSpecΓ x).asIdeal) = (x.1 ∈ X.basicOpen r) at h
  rw [IsAffineOpen.isoSpec_hom]
  simpa only [not_not] using not_congr (Eq.to_iff h)

omit [Finite σ] in
private theorem hyperplane_section_vanish_iff
    (p q : MvPolynomial σ k) (hp : p∈Gr 1) (hq : q∈Gr 1)
    (x : (Proj.basicOpen Gr q).toScheme) :
    x.1 ∉ (Proj Gr).basicOpen
      ((Proj.awayToSection Gr q).hom (Away.mk Gr hq 1 p (by simpa using hp))) ↔
    p ∈ x.1.asHomogeneousIdeal := by
  have h := hyperplane_ratio_mem_affine_prime p q hp hq x
  have hsec := congrArg (fun W : (Proj.basicOpen Gr q).toScheme.Opens => x ∈ W)
    (Scheme.Opens.toSpecΓ_preimage_basicOpen (Proj.basicOpen Gr q)
      ((Proj.awayToSection Gr q).hom (Away.mk Gr hq 1 p (by simpa using hp))))
  change ((Proj.awayToSection Gr q).hom (Away.mk Gr hq 1 p (by simpa using hp))) ∈
    ((Proj.basicOpen Gr q).toSpecΓ x).asIdeal ↔ _ at h
  change (((Proj.awayToSection Gr q).hom (Away.mk Gr hq 1 p (by simpa using hp))) ∉
    ((Proj.basicOpen Gr q).toSpecΓ x).asIdeal) = _ at hsec
  have hs : x.1 ∉ (Proj Gr).basicOpen
      ((Proj.awayToSection Gr q).hom (Away.mk Gr hq 1 p (by simpa using hp))) ↔
      ((Proj.awayToSection Gr q).hom (Away.mk Gr hq 1 p (by simpa using hp))) ∈
        ((Proj.basicOpen Gr q).toSpecΓ x).asIdeal := by
    change _ = (x.1 ∈ (Proj Gr).basicOpen _) at hsec
    simpa only [not_not] using (not_congr (Eq.to_iff hsec)).symm
  exact hs.trans h

theorem dimension_le_hyperplane_add_one
    (X : Geometric k) [IrreducibleSpace X.toScheme]
    (φ : Morphism X (projectiveSpaceByCoordinates k σ)) [IsClosedImmersion φ.hom]
    (p : MvPolynomial σ k) (hp : p∈Gr 1)
    (hne : (φ.hom ⁻¹' (Proj.basicOpen Gr p : Set (Proj Gr))ᶜ).Nonempty) :
    dimension X ≤
      topologicalKrullDim (φ.hom ⁻¹' (Proj.basicOpen Gr p : Set (Proj Gr))ᶜ)+1 := by
  obtain ⟨x,hx⟩ := hne
  have hc := (Proj.iSup_basicOpen_eq_top Gr (MvPolynomial.X : σ → MvPolynomial σ k)
    (coordinate_irrelevant_le_span k σ)).ge (Set.mem_univ (φ.hom x))
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hc
  let q : MvPolynomial σ k := MvPolynomial.X i
  have hq : q∈Gr 1 := MvPolynomial.isHomogeneous_X k i
  let D := Proj.basicOpen Gr q
  have hD : IsAffineOpen D :=
    (IsAffine.iff_of_isIso (Proj.basicOpenIsoSpec Gr q hq Nat.zero_lt_one).hom).mpr inferInstance
  let U := φ.hom ⁻¹ᵁ D
  have hU : IsAffineOpen U := hD.preimage φ.hom
  let s : Γ(Proj Gr,D) :=
    (Proj.awayToSection Gr q).hom (Away.mk Gr hq 1 p (by simpa using hp))
  let r : Γ(X.toScheme,U) := (φ.hom.app D).hom s
  apply dimension_le_principal_locus_add_one X U hU _ r ?_ ⟨x,hx,hi⟩
  intro z
  rw [affine_prime_mem_iff_not_basicOpen hU r z]
  have hpre := congrArg (fun W : X.toScheme.Opens => z.1 ∈ W)
    (Scheme.preimage_basicOpen φ.hom s)
  change (φ.hom z.1 ∈ (Proj Gr).basicOpen s) = (z.1 ∈ X.toScheme.basicOpen r) at hpre
  rw [←hpre]
  change (φ.hom z.1 ∉ (Proj Gr).basicOpen s) ↔ ¬p ∉ (φ.hom z.1).asHomogeneousIdeal
  rw [not_not]
  exact hyperplane_section_vanish_iff p q hp hq ⟨φ.hom z.1,z.2⟩
end Theory.AlgebraicGroup.Variety.Geometric
