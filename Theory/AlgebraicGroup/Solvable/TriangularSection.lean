module

public import Theory.AlgebraicGroup.Solvable.TorusComplement
public import Theory.AlgebraicGroup.Tori.TriangularDiagonalPullbackSurjective
public import Theory.AlgebraicGroup.Variety.InjectiveOfPullbackSurjective

/-!
# Regular triangular diagonal sections

This module proves the regular splitting core associated to a triangular
presentation of a connected solvable algebraic group.  Borel, *Linear
Algebraic Groups*, Chapter III, Theorem 10.6(4), supplies a subtorus complement
to the connected unipotent radical.  For a fixed triangular presentation `P`,
that radical is the kernel of diagonal projection.

The main theorem identifies the complement with `P.diagonalImage` as an
algebraic group.  The nontrivial regularity step uses triangular character
support: surjectivity of the coordinate pullback for the embedded complement
descends through diagonal projection.  Together with point-surjectivity from
the torus-unipotent factorization, this produces an honest isomorphism rather
than merely a bijection on points.  Its inverse, followed by the complement's
inclusion, is therefore a regular section of `P.diagonalImageMorphism`.

The construction is characteristic-free and remains below maximal-torus
conjugacy and the later numbered torus theorems in the import graph.
-/

universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem TriangularPresentation.diagonalImageIso_of_torus_factor
    {G : Variety k} [AlgebraicGroup G] (P : TriangularPresentation G)
    (T : ClosedSubgroup G) (hT : IsSubtorus T)
    (hfactor : ∀ x : Variety.Point G, ∃ t u,
      t ∈ T.toSubgroup ∧ u ∈ P.unipotentRadical.toSubgroup ∧
        x = t * u) :
    letI : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
    letI : AlgebraicGroup P.diagonalImage.carrierVariety :=
      P.diagonalImage.carrierAlgebraicGroup
    ∃ e : AlgebraicGroup.Iso T.carrierVariety
        P.diagonalImage.carrierVariety,
      e.hom = P.diagonalImageMorphism.comp T.inclusion := by
  letI : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
  letI : AlgebraicGroup P.subgroup.carrierVariety :=
    P.subgroup.carrierAlgebraicGroup
  letI : AlgebraicGroup P.diagonalImage.carrierVariety :=
    P.diagonalImage.carrierAlgebraicGroup
  let fTri : AlgebraicGroup.Morphism T.carrierVariety (tVariety k P.n) :=
    (P.subgroup.inclusion.comp P.iso.hom).comp T.inclusion
  have hsubgroupPull : Function.Surjective
      P.subgroup.inclusion.toVariety.pullbackRingHom :=
    P.subgroup.restrictionRingHom_surjective
  have hisoPull : Function.Surjective
      P.iso.hom.toVariety.pullbackRingHom :=
    algebraicGroupIso_hom_pullbackRingHom_surjective P.iso
  have hambientPull : Function.Surjective
      (P.subgroup.inclusion.comp P.iso.hom).toVariety.pullbackRingHom := by
    rw [show (P.subgroup.inclusion.comp P.iso.hom).toVariety.pullbackRingHom =
        P.iso.hom.toVariety.pullbackRingHom.comp
          P.subgroup.inclusion.toVariety.pullbackRingHom from
      Variety.Morphism.pullbackRingHom_comp
        P.subgroup.inclusion.toVariety P.iso.hom.toVariety]
    exact hisoPull.comp hsubgroupPull
  have hfTriPull : Function.Surjective fTri.toVariety.pullbackRingHom := by
    rw [show fTri.toVariety.pullbackRingHom =
        T.inclusion.toVariety.pullbackRingHom.comp
          (P.subgroup.inclusion.comp P.iso.hom).toVariety.pullbackRingHom from by
      dsimp only [fTri]
      exact Variety.Morphism.pullbackRingHom_comp
        (P.subgroup.inclusion.comp P.iso.hom).toVariety T.inclusion.toVariety]
    exact T.restrictionRingHom_surjective.comp hambientPull
  let fDiag := (tDiagonalMorphism P.n).comp fTri
  have hfDiagPull : Function.Surjective fDiag.toVariety.pullbackRingHom :=
    triangularMorphism_diagonal_pullbackRingHom_surjective
      hT P.n fTri hfTriPull
  let fImage := P.diagonalImageMorphism.comp T.inclusion
  have hfImagePull : Function.Surjective
      fImage.toVariety.pullbackRingHom := by
    intro q
    obtain ⟨qD, hqD⟩ := hfDiagPull q
    refine ⟨P.diagonalImage.inclusion.toVariety.pullbackRingHom qD, ?_⟩
    calc
      fImage.toVariety.pullbackRingHom
          (P.diagonalImage.inclusion.toVariety.pullbackRingHom qD) =
          fDiag.toVariety.pullbackRingHom qD := by
            apply Variety.PolynomialFunction.ext
            intro x
            rfl
      _ = q := hqD
  have hinc (x : Variety.Point G) :
      P.diagonalImage.inclusion.onPoints
          (P.diagonalImageMorphism.onPoints x) =
        P.diagonalMorphism.onPoints x := by
    simpa only [TriangularPresentation.diagonalImageMorphism] using
      (AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply
        P.diagonalMorphism P.diagonalImage
        (fun z => by
          change P.diagonalMorphism.onPoints z ∈ P.diagonalMorphism.image
          exact ⟨z, rfl⟩) x)
  have hdiagSurj : Function.Surjective
      P.diagonalImageMorphism.onPoints := by
    intro y
    have hy := (P.diagonalImage.pointEquiv y).property
    change (P.diagonalImage.pointEquiv y).val ∈
      P.diagonalMorphism.image at hy
    rcases hy with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply P.diagonalImage.inclusion_injective
    exact (hinc x).trans hx
  have hfImageSurj : Function.Surjective fImage.onPoints := by
    intro y
    obtain ⟨x, hx⟩ := hdiagSurj y
    obtain ⟨t, u, ht, hu, htu⟩ := hfactor x
    let tT : Variety.Point T.carrierVariety :=
      T.pointEquiv.symm ⟨t, ht⟩
    refine ⟨tT, ?_⟩
    apply P.diagonalImage.inclusion_injective
    have htT : T.inclusion.onPoints tT = t := by
      change (T.pointEquiv tT).val = t
      simp [tT]
    have hdiagu : P.diagonalMorphism.onPoints u = 1 := by
      change u ∈ P.diagonalMorphism.kernel
      exact hu
    calc
      P.diagonalImage.inclusion.onPoints (fImage.onPoints tT) =
          P.diagonalMorphism.onPoints (T.inclusion.onPoints tT) :=
        hinc (T.inclusion.onPoints tT)
      _ = P.diagonalMorphism.onPoints t := by rw [htT]
      _ = P.diagonalMorphism.onPoints (t * u) := by
        rw [map_mul, hdiagu, mul_one]
      _ = P.diagonalMorphism.onPoints x := by rw [← htu]
      _ = P.diagonalImage.inclusion.onPoints y := by rw [← hinc x, hx]
  have hfImageInj : Function.Injective fImage.onPoints :=
    fImage.toVariety.injective_of_pullbackRingHom_surjective hfImagePull
  exact algebraicGroupIso_of_bijective_morphism_of_pullback_surjective
    fImage ⟨hfImageInj, hfImageSurj⟩ hfImagePull

/-- A connected solvable triangularly presented group has a torus complement
whose restriction to the diagonal image is an algebraic-group isomorphism.
The inverse is the regular diagonal section into the complement. -/
public theorem TriangularPresentation.exists_torusComplement_diagonalImageIso_of_solvable_connected
    {G : Variety k} [AlgebraicGroup G] (P : TriangularPresentation G)
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G) :
    ∃ T : ClosedSubgroup G,
      IsTorusComplement T P.unipotentRadical ∧
        (letI : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
         letI : AlgebraicGroup P.diagonalImage.carrierVariety :=
           P.diagonalImage.carrierAlgebraicGroup
         ∃ e : AlgebraicGroup.Iso T.carrierVariety
             P.diagonalImage.carrierVariety,
           e.hom = P.diagonalImageMorphism.comp T.inclusion) := by
  obtain ⟨U, hU, -, T, hT, -⟩ :=
    exists_maximalTorus_complement_of_solvable_connected
      hsolvable hconnected
  have hUP : U = P.unipotentRadical := by
    apply SetLike.coe_injective
    ext x
    exact (hU x).trans
      (P.mem_unipotentRadical_iff_characteristicFree x).symm
  subst U
  refine ⟨T, hT, ?_⟩
  exact P.diagonalImageIso_of_torus_factor T hT.1 hT.2.1

end Theory.AlgebraicGroup
