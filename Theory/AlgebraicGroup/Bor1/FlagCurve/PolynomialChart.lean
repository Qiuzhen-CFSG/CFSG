module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit.Coordinates
public import Theory.AlgebraicGroup.Bor1.FlagCurve.AffineChart

/-!
# Polynomial coordinates on projective affine charts

A unit coordinate confines the polynomial projective curve to its actual basic
open. Homogeneous relations persist on the closure of the scheme image. The
localization map records the coordinate fractions for the normal monomial-chart
argument in Borel, Linear Algebraic Groups, §13.13.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open Theory.AlgebraicGroup.Variety.Geometric
open Theory.AlgebraicGroup.Variety.Geometric.ProjectivePolynomialCurve
namespace Theory.AlgebraicGroup.Bor1.FlagCurve
universe u
variable {k : Type u} [Field k] {ι : Type} [Finite ι]

@[expose]
noncomputable def polynomialChartMap (p : ι → Polynomial k) (i : ι) (hi : IsUnit (p i)) :
    HomogeneousLocalization.Away (projectiveGrading k ι) (MvPolynomial.X i) →+* Polynomial k :=
  (Localization.awayLift (MvPolynomial.aeval p).toRingHom (MvPolynomial.X i) (by simpa using hi)).comp
    { toFun := HomogeneousLocalization.val
      map_one' := HomogeneousLocalization.val_one
      map_mul' := HomogeneousLocalization.val_mul
      map_zero' := HomogeneousLocalization.val_zero
      map_add' := HomogeneousLocalization.val_add }

omit [Finite ι] in
theorem polynomialChartMap_mk (p : ι → Polynomial k) (i : ι) (hi : IsUnit (p i))
    (q : Polynomial k) (hq : p i * q = 1) (n : ℕ) (a : MvPolynomial ι k)
    (ha : a ∈ projectiveGrading k ι (n • 1)) :
    polynomialChartMap p i hi (HomogeneousLocalization.Away.mk (projectiveGrading k ι)
      (MvPolynomial.isHomogeneous_X k i) n a ha) = (MvPolynomial.aeval p) a * q ^ n := by
  apply Localization.awayLift_mk
  simpa using hq

set_option backward.isDefEq.respectTransparency false in
theorem curve_preimage_coordinate_top (p : ι → Polynomial k) (i : ι) (hi : IsUnit (p i)) :
    (curve p ⟨i, hi⟩).hom ⁻¹ᵁ Proj.basicOpen (projectiveGrading k ι) (MvPolynomial.X i) = ⊤ := by
  rw [show (curve p ⟨i, hi⟩).hom = Proj.fromOfGlobalSections _ _ _ from rfl]
  rw [Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ Nat.zero_lt_one
    (MvPolynomial.isHomogeneous_X k i)]
  apply Scheme.basicOpen_of_isUnit
  change IsUnit ((Scheme.ΓSpecIso (.of (Polynomial k))).inv.hom
    ((MvPolynomial.aeval p) (MvPolynomial.X i)))
  rw [MvPolynomial.aeval_X]
  exact hi.map _

set_option backward.isDefEq.respectTransparency false in
theorem curve_closure_vanishes (p : ι → Polynomial k) (hp : ∃ i, IsUnit (p i))
    (a : MvPolynomial ι k) (d : ℕ) (hd : 0 < d)
    (ha : a ∈ projectiveGrading k ι d) (hz : (MvPolynomial.aeval p) a = 0) :
    closure (Set.range (curve p hp).hom) ⊆
      (Proj.basicOpen (projectiveGrading k ι) a : Set (Proj (projectiveGrading k ι)))ᶜ := by
  apply closure_minimal _ (Proj.basicOpen (projectiveGrading k ι) a).isOpen.isClosed_compl
  rintro _ ⟨x, rfl⟩ hx
  have hh : x ∈ (curve p hp).hom ⁻¹ᵁ Proj.basicOpen (projectiveGrading k ι) a := hx
  change x ∈ Proj.fromOfGlobalSections (projectiveGrading k ι) (sections p)
    (irrelevant p hp) ⁻¹ᵁ Proj.basicOpen (projectiveGrading k ι) a at hh
  rw [Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ hd ha] at hh
  have hs : sections p a = 0 := by
    change (Scheme.ΓSpecIso (.of (Polynomial k))).inv.hom ((MvPolynomial.aeval p) a) = 0
    rw [hz, map_zero]
  rw [hs, Scheme.basicOpen_zero] at hh
  exact hh

end Theory.AlgebraicGroup.Bor1.FlagCurve
