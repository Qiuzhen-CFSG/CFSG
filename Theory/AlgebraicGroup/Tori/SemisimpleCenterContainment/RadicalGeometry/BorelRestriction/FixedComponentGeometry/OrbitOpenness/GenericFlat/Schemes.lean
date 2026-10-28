module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.FixedComponentGeometry.OrbitOpenness.GenericFlat.Algebra
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# A nonempty flat source patch of a dominant scheme morphism

A dominant morphism locally of finite type between integral schemes has a
nonempty flat source-open subscheme when the target is locally Noetherian.
Restrict to nonempty affine charts: source irreducibility ensures the
restricted map is still dominant, and reducedness of the target makes its
coordinate-ring homomorphism injective. The algebraic source-localization
theorem supplies a flat principal open. Its spectrum is an open subscheme
of the original source, and flatness transports through this identification.

This is the generic flatness input for the homogeneous orbit argument in
Borel, *Linear Algebraic Groups*, §11.15
(`refs/KGroup/Bor1/Chapter4.tex`). No separability is used.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
set_option linter.style.haveILetI false
universe u

namespace AlgebraicGeometry

private theorem exists_flat_patch_of_openImmersion
    {T X Y : Scheme.{u}} (i : T ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion i] [Nonempty T] (hflat : Flat (i ≫ f)) :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ Flat (U.ι ≫ f) := by
  refine ⟨i.opensRange, Set.range_nonempty i, ?_⟩
  letI : Flat (i ≫ f) := hflat
  rw [← i.isoOpensRange_inv_comp, Category.assoc]
  infer_instance

private theorem exists_flat_patch_affine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDominant f] :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ Flat (U.ι ≫ f) := by
  let R := Γ(Y, ⊤)
  let A := Γ(X, ⊤)
  letI : Algebra R A := f.appTop.hom.toAlgebra
  letI : IsNoetherianRing R :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  letI : Algebra.FiniteType R A :=
    HasRingHomProperty.appTop @LocallyOfFiniteType f inferInstance
  letI : IsSchemeTheoreticallyDominant f := .of_isDominant f
  letI : FaithfulSMul R A :=
    (faithfulSMul_iff_algebraMap_injective R A).mpr (f.app_injective ⊤)
  obtain ⟨a, ha, hflat⟩ :=
    Theory.AlgebraicGroup.GenericFlat.exists_flat_source_localization (R := R) (A := A)
  letI : IsDomain (Localization.Away a) := Localization.Away.isDomain ha
  let l : Spec (.of (Localization.Away a)) ⟶ Spec A :=
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a)))
  let i := l ≫ X.isoSpec.inv
  apply exists_flat_patch_of_openImmersion i f
  have he : i ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away a))) ≫ Y.isoSpec.inv := by
    dsimp [i]
    rw [Category.assoc, ← Scheme.isoSpec_inv_naturality]
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  rw [he]
  letI : Flat (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away a)))) :=
    Flat.SpecMap_iff.mpr hflat
  infer_instance

/-- A dominant morphism locally of finite type between integral schemes, with locally
Noetherian target, is flat on some nonempty open subscheme of the source. -/
public theorem Scheme.Hom.exists_nonempty_flat_patch
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : DenseRange f) :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ Flat (U.ι ≫ f) := by
  letI : IsDominant f := ⟨hf⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := f x) (U := ⊤) (by trivial)
  obtain ⟨V, hV, hxV, hVU⟩ :=
    exists_isAffineOpen_mem_and_subset (x := x) (U := f ⁻¹ᵁ U) hxU
  letI : IsAffine U := hU
  letI : IsAffine V := hV
  letI : Nonempty U := ⟨⟨f x, hxU⟩⟩
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  letI : IsIntegral U := isIntegral_of_isOpenImmersion U.ι
  letI : IsIntegral V := isIntegral_of_isOpenImmersion V.ι
  have hle : V ≤ f ⁻¹ᵁ U := hVU
  let g := f.resLE U V hle
  letI : IsDominant V.ι := Opens.isDominant_ι (V.isOpen.dense ⟨x, hxV⟩)
  letI : IsDominant (g ≫ U.ι) := by
    dsimp [g]
    rw [Scheme.Hom.resLE_comp_ι]
    infer_instance
  letI : IsDominant g := IsDominant.of_comp_of_isOpenImmersion g U.ι
  obtain ⟨W, hW, hflat⟩ := exists_flat_patch_affine g
  letI : Nonempty W := hW.to_subtype
  let i := W.ι ≫ V.ι
  apply exists_flat_patch_of_openImmersion i f
  have he : i ≫ f = (W.ι ≫ g) ≫ U.ι := by
    simp only [i, Category.assoc, g, Scheme.Hom.resLE_comp_ι]
  rw [he]
  letI : Flat (W.ι ≫ g) := hflat
  infer_instance

end AlgebraicGeometry
