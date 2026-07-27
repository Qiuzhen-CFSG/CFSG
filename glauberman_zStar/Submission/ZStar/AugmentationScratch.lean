import Submission.ZStar.BrauerBlockReduction

noncomputable section

open scoped BigOperators

namespace Submission.ZStar

namespace AugmentationScratch

universe u v

attribute [local instance] Fintype.ofFinite

noncomputable def augmentation
    (R : Type u) (G : Type v) [CommSemiring R] [Monoid G] :
    MonoidAlgebra R G →+* R :=
  ((MonoidAlgebra.lift R R G) (1 : G →* R)).toRingHom

@[simp] theorem augmentation_single
    {R : Type u} {G : Type v} [CommSemiring R] [Monoid G]
    (g : G) (r : R) :
    augmentation R G (MonoidAlgebra.single g r) = r := by
  simp [augmentation]

theorem augmentation_apply
    {R : Type u} {G : Type v} [CommSemiring R] [Monoid G] [Finite G]
    (a : MonoidAlgebra R G) :
    augmentation R G a = ∑ g : G, a g := by
  change ((MonoidAlgebra.lift R R G) (1 : G →* R)) a = _
  rw [MonoidAlgebra.lift_apply]
  simp only [MonoidHom.one_apply, smul_eq_mul, mul_one]
  exact Finsupp.sum_fintype a (fun _ r => r) (by simp)

/-- Augmentation is natural under change of coefficient ring. -/
theorem augmentation_mapRingHom
    {R : Type u} {S : Type*} {G : Type v}
    [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (a : MonoidAlgebra R G) [Monoid G] :
    augmentation S G (MonoidAlgebra.mapRingHom G f a) =
      f (augmentation R G a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single g r => simp [augmentation_single]

theorem mul_ne_zero_of_augmentation_eq_one
    {R : Type u} {G : Type v}
    [CommRing R] [Nontrivial R] [Group G]
    (a b : MonoidAlgebra R G)
    (ha : augmentation R G a = 1)
    (hb : augmentation R G b = 1) :
    a * b ≠ 0 := by
  intro hab
  have h := congrArg (augmentation R G) hab
  rw [map_mul, ha, hb, one_mul, map_zero] at h
  exact one_ne_zero h

/-- In characteristic two, an involution Brauer restriction preserves the
augmentation of central elements: all omitted conjugation orbits have size
two and cancel. -/
theorem augmentation_centralizerRestriction
    {R : Type u} {G : Type v}
    [CommRing R] [CharP R 2] [Group G] [Finite G]
    (z : G) (hz : z * z = 1)
    (e : MonoidAlgebra R G)
    (he : e ∈ Set.center (MonoidAlgebra R G)) :
    augmentation R (Subgroup.centralizer ({z} : Set G))
        (BrauerMapScratch.centralizerRestriction R z e) =
      augmentation R G e := by
  rw [augmentation_apply, augmentation_apply]
  exact (BrauerMapScratch.sum_centralizer_of_conj_invariant
    z hz (fun g : G => e g) (fun g =>
      CentralIdempotentSupport.coeff_conj_eq_of_mem_center
        e he z g)).symm

theorem trivial_asAlgebraHom_apply_one
    {R : Type u} {G : Type v} [CommSemiring R] [Group G]
    (a : MonoidAlgebra R G) :
    ((Representation.trivial R G (Fin 1 → R)).asAlgebraHom a
        (fun _ => 1)) 0 = augmentation R G a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single g r => simp [augmentation_single]

theorem principalBlockElement_augmentation_eq_one
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G) :
    augmentation ℂ G (BlockOrthogonality.principalBlockElement d) = 1 := by
  let rho0 : Representation ℂ G (Fin 1 → ℂ) :=
    Representation.trivial ℂ G (Fin 1 → ℂ)
  have hchar : d.chi d.principal = rho0.characterClassFunction := by
    rw [d.principal_eq]
    ext C
    rcases ConjClasses.exists_rep C with ⟨g, rfl⟩
    change 1 = rho0.character g
    simp [rho0, Representation.character]
  have haction := BlockOrthogonality.principalBlockElement_action
    d d.principal rho0 hchar
  have haction' :
      rho0.asAlgebraHom (BlockOrthogonality.principalBlockElement d) = 1 := by
    simpa using haction
  have hone := congrArg
    (fun f : Module.End ℂ (Fin 1 → ℂ) => f (fun _ => 1) 0) haction'
  change
    (rho0.asAlgebraHom (BlockOrthogonality.principalBlockElement d)
      (fun _ => 1)) 0 = 1 at hone
  rw [show rho0 = Representation.trivial ℂ G (Fin 1 → ℂ) by rfl,
    trivial_asAlgebraHom_apply_one] at hone
  exact hone

theorem localizedPrincipalBlockElement_augmentation_eq_one
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G) :
    augmentation (Localization.AtPrime d.primeIdeal) G
        (BlockOrthogonality.localizedPrincipalBlockElement d) = 1 := by
  rw [augmentation_apply]
  exact BlockOrthogonality.localizedPrincipalBlockElement_sum_coeff_eq_one d

theorem reducedPrincipalBlockElement_augmentation_eq_one
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G) :
    augmentation (BrauerBlockReduction.principalResidueField d) G
        (BrauerBlockReduction.reducedPrincipalBlockElement d) = 1 := by
  change augmentation (BrauerBlockReduction.principalResidueField d) G
      (MonoidAlgebra.mapRingHom G
        (BrauerBlockReduction.localizationToResidue d)
        (BlockOrthogonality.localizedPrincipalBlockElement d)) = 1
  rw [augmentation_mapRingHom,
    localizedPrincipalBlockElement_augmentation_eq_one, map_one]

/-- The reduced ambient principal idempotent and its involution Brauer image
both act as one on the trivial module. -/
theorem involutionBrauerPrincipalBlockElement_augmentation_eq_one
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (z : G) (hz : z * z = 1) :
    augmentation (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer ({z} : Set G))
        (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z) = 1 := by
  calc
    augmentation (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer ({z} : Set G))
        (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z) =
      augmentation (BrauerBlockReduction.principalResidueField d) G
        (BrauerBlockReduction.reducedPrincipalBlockElement d) :=
      augmentation_centralizerRestriction z hz
        (BrauerBlockReduction.reducedPrincipalBlockElement d)
        (BrauerBlockReduction.reducedPrincipalBlockElement_mem_center d)
    _ = 1 := reducedPrincipalBlockElement_augmentation_eq_one d

end AugmentationScratch

end Submission.ZStar
