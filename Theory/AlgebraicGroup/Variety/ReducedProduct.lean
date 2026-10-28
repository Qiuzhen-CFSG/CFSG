module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Properties
public import Theory.AlgebraicGroup.Bor1.SmoothReduced

set_option linter.style.haveILetI false

/-!
# Reduced products over an algebraically closed field

For a finite-type reduced scheme over an algebraically closed field, the smooth
locus is dense (AG.5.3).  Its structure morphism is smooth, hence geometrically
reduced; after a flat base change, the resulting pullback is reduced.  The
canonical map from this pullback to the original fiber product is the flat base
change of the dense open immersion of the smooth locus.  Scheme-theoretic
dominance therefore descends reducedness to the original product, giving the
reduced-product step used in the geometric variety formalism (AG.6.2).

The affine step identifies the ring of global sections of an affine smooth
scheme over a field with a smooth algebra, and applies the field-smooth
reducedness theorem from `Bor1.SmoothReduced`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

namespace Theory.AlgebraicGroup.Variety

universe u

private lemma affine_smooth_reduced {K : Type u} [Field K] {Z : Scheme} (q : Z ⟶ Spec (.of K))
    [IsAffine Z] [Smooth q] : IsReduced Z := by
  have hsm : (q.appTop.hom).Smooth :=
    (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp inferInstance
  let e := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  let φ : K →+* Γ(Z, ⊤) :=
    (q.appTop.hom).comp e.symm.toRingHom
  have hφ : φ.Smooth := by
    apply RingHom.Smooth.comp
    · exact RingHom.Smooth.of_bijective e.symm.bijective
    · exact hsm
  letI : Algebra K Γ(Z, ⊤) := φ.toAlgebra
  haveI : Algebra.Smooth K Γ(Z, ⊤) := RingHom.Smooth.toAlgebra hφ
  letI : IsReduced Γ(Z, ⊤) :=
    Theory.AlgebraicGroup.Bor1.isReduced_of_smooth_of_field
      (K := K) (A := Γ(Z, ⊤))
  exact isReduced_of_isAffine_isReduced Z

private lemma smooth_geometricallyReduced {X Y : Scheme} (f : X ⟶ Y) [Smooth f] :
    GeometricallyReduced f := by
  rw [geometricallyReduced_iff]
  intro K _ y Z fst snd h
  let q : Z ⟶ Spec (.of K) := snd
  letI : Smooth q := MorphismProperty.of_isPullback h inferInstance
  letI : ∀ i, IsReduced (Z.affineCover.X i) := fun i ↦ by
    let qi : Z.affineCover.X i ⟶ Spec (.of K) := Z.affineCover.f i ≫ q
    haveI : Smooth qi := by infer_instance
    exact affine_smooth_reduced qi
  exact IsReduced.of_openCover Z Z.affineCover

public theorem isReduced_pullback_over_algClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsReduced X]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsReduced Y] :
    IsReduced (pullback f g) := by
  let U : X.Opens := f.smoothLocus
  let i : U.toScheme ⟶ X := U.ι
  let fi : U.toScheme ⟶ Spec (.of k) := i ≫ f
  have hfi : Smooth fi := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff]
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    change U.ι ⁻¹ᵁ U = ⊤
    exact U.ι_preimage_self
  letI : Smooth fi := hfi
  letI : GeometricallyReduced fi := smooth_geometricallyReduced fi
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  letI : IsLocallyNoetherian U.toScheme := inferInstance
  letI : QuasiCompact i := inferInstance
  have hdom : IsDominant i := by
    apply Opens.isDominant_ι
    exact f.dense_smoothLocus_of_perfectField
  letI : IsSchemeTheoreticallyDominant i :=
    IsSchemeTheoreticallyDominant.of_isDominant i
  letI : IsReduced (pullback fi g) := by
    exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
      (pullback.snd fi g)
  let qmap : pullback fi g ⟶ pullback f g :=
    pullback.map fi g f g i (𝟙 _) (𝟙 _) (by simp [fi]) (by simp)
  have hqfst : qmap ≫ pullback.fst f g = pullback.fst fi g ≫ i := by
    dsimp [qmap, pullback.map]
    rw [pullback.lift_fst]
  have hqsnd : qmap ≫ pullback.snd f g = pullback.snd fi g := by
    dsimp [qmap, pullback.map]
    rw [pullback.lift_snd]
    simp
  have hpb : IsPullback (pullback.fst fi g) qmap i (pullback.fst f g) := by
    refine IsPullback.mk' ?_ ?_ ?_
    · exact hqfst.symm
    · intro T a b h₁ h₂
      apply pullback.hom_ext
      · exact h₁
      · have h₂' := congrArg (fun t ↦ t ≫ pullback.snd f g) h₂
        simpa only [Category.assoc, hqsnd] using h₂'
    · intro T a b hab
      have hab' : a ≫ fi = (b ≫ pullback.snd f g) ≫ g := by
        calc
          a ≫ fi = a ≫ i ≫ f := by simp [fi]
          _ = b ≫ pullback.fst f g ≫ f := by
            simpa [Category.assoc] using congrArg (fun h ↦ h ≫ f) hab
          _ = b ≫ pullback.snd f g ≫ g := by rw [pullback.condition]
          _ = (b ≫ pullback.snd f g) ≫ g := by simp [Category.assoc]
      let l : T ⟶ pullback fi g := pullback.lift a (b ≫ pullback.snd f g) hab'
      refine ⟨l, ?_, ?_⟩
      · rw [pullback.lift_fst]
      · apply pullback.hom_ext
        · rw [Category.assoc, hqfst]
          dsimp [l]
          rw [← Category.assoc, pullback.lift_fst]
          exact hab
        · rw [Category.assoc, hqsnd]
          dsimp [l]
          rw [pullback.lift_snd]
  letI : IsSchemeTheoreticallyDominant qmap := by
    exact IsSchemeTheoreticallyDominant.of_isPullback hpb
  exact IsSchemeTheoreticallyDominant.isReduced qmap

end Theory.AlgebraicGroup.Variety
