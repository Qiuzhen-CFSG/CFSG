module

public import Theory.AlgebraicGroup.Variety.Complete
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-!
# Normalization factorization of a bijective morphism

This module proves the normalization step used in Borovoi, *Linear Algebraic Groups* (`Bor1`),
AG.18.2--18.3.  If `f : V ⟶ W` is a bijective morphism of geometric varieties over an
algebraically closed field, `V` is irreducible, and `W` is normal, then Mathlib's relative
normalization of `f` maps surjectively to `V` and its integral map to `W` factors through `f`.
Composing that factorization with universal closedness of integral morphisms proves the repaired
Bor1 10.1(4) backward completeness transfer.

The key missing implication is the purely inseparable function-field extension.  Point
injectivity makes the diagonal surjective: its image is closed by separatedness and contains
all closed points of its finite-type, hence Jacobson, source.  Universal injectivity then makes
the generic residue-field map purely inseparable.  On an affine open of `W`, a power of every
element of the relative integral closure consequently lies in the fraction field of the normal
section ring, hence in the ring itself.  The resulting universal homeomorphism on prime spectra
shows that the integral normalization map is injective.  Surjectivity of `f` makes the other
normalization map surjective; Zariski's Main Theorem makes it an isomorphism, after which
`normalizationDesc` supplies the required factor.
-/

@[expose] public noncomputable section

set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u

variable {k : Type u} [Field k]

/-- A morphism between finite-type geometric varieties is locally of finite type. -/
instance Morphism.locallyOfFiniteType {V W : Geometric k} (f : Morphism V W) :
    LocallyOfFiniteType f.hom := by
  haveI : LocallyOfFiniteType (f.hom ≫ W.structureMap) := by
    rw [f.commutes]
    infer_instance
  exact locallyOfFiniteType_of_comp f.hom W.structureMap

/-- A morphism between separated geometric varieties is separated. -/
instance Morphism.isSeparated {V W : Geometric k} (f : Morphism V W) :
    IsSeparated f.hom := by
  haveI : IsSeparated (f.hom ≫ W.structureMap) := by
    rw [f.commutes]
    infer_instance
  exact IsSeparated.of_comp f.hom W.structureMap

/-- A morphism of geometric varieties is quasi-compact because its source is Noetherian. -/
instance Morphism.quasiCompact {V W : Geometric k} (f : Morphism V W) :
    QuasiCompact f.hom := by
  letI : CompactSpace V.toScheme :=
    QuasiCompact.compactSpace_of_compactSpace V.structureMap
  letI : IsNoetherian V.toScheme :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian V.structureMap }
  infer_instance

private theorem universallyInjective_of_injective {V W : Geometric k} (f : Morphism V W)
    [IsAlgClosed k] (hf : Function.Injective f.hom) : UniversallyInjective f.hom := by
  let P := pullback f.hom f.hom
  let p : P ⟶ Spec (.of k) := pullback.fst f.hom f.hom ≫ V.structureMap
  haveI : LocallyOfFiniteType p := by
    dsimp [p]
    infer_instance
  haveI : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace p
  have hclosed : IsClosed (Set.range (pullback.diagonal f.hom)) :=
    (pullback.diagonal f.hom).isClosedMap.isClosed_range
  have hclosedPoints : closedPoints P ⊆ Set.range (pullback.diagonal f.hom) := by
    intro z hz
    let q : Spec (.of k) ⟶ P := pointOfClosedPoint p z hz
    have hqfst : q ≫ pullback.fst f.hom f.hom ≫ V.structureMap = 𝟙 _ := by
      simpa [p, Category.assoc] using pointOfClosedPoint_comp p z hz
    have hqsnd : q ≫ pullback.snd f.hom f.hom ≫ V.structureMap = 𝟙 _ := by
      have hqfst' : q ≫ pullback.fst f.hom f.hom ≫ f.hom ≫ W.structureMap = 𝟙 _ := by
        simpa only [Category.assoc, f.commutes] using hqfst
      have hcon := congrArg (fun g => q ≫ g ≫ W.structureMap)
        (pullback.condition : pullback.fst f.hom f.hom ≫ f.hom =
          pullback.snd f.hom f.hom ≫ f.hom).symm
      simpa only [Category.assoc, f.commutes] using hcon.trans hqfst'
    have hproj : q ≫ pullback.fst f.hom f.hom =
        q ≫ pullback.snd f.hom f.hom := by
      apply ext_of_apply_closedPoint_eq V.structureMap hqfst hqsnd
      apply hf
      have hcomp : (q ≫ pullback.fst f.hom f.hom) ≫ f.hom =
          (q ≫ pullback.snd f.hom f.hom) ≫ f.hom := by
        exact congrArg (fun g => q ≫ g) (pullback.condition :
          pullback.fst f.hom f.hom ≫ f.hom =
            pullback.snd f.hom f.hom ≫ f.hom)
      have hpoint : (default : Spec (.of k)) = IsLocalRing.closedPoint k :=
        Subsingleton.elim _ _
      rw [← hpoint]
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      exact congrArg (fun g : Spec (.of k) ⟶ W.toScheme => g default) hcomp
    have hq : (q ≫ pullback.fst f.hom f.hom) ≫ pullback.diagonal f.hom = q := by
      apply pullback.hom_ext
      · simp
      · simpa [Category.assoc] using hproj
    refine ⟨(q ≫ pullback.fst f.hom f.hom) default, ?_⟩
    calc
      (pullback.diagonal f.hom) ((q ≫ pullback.fst f.hom f.hom) default) =
          ((q ≫ pullback.fst f.hom f.hom) ≫ pullback.diagonal f.hom) default := rfl
      _ = q default := congrArg (fun g => g default) hq
      _ = z := pointOfClosedPoint_apply p z hz default
  have hrange : Set.range (pullback.diagonal f.hom) = Set.univ := by
    rw [← Set.univ_subset_iff, ← closure_closedPoints]
    exact (closure_mono hclosedPoints).trans hclosed.closure_eq.le
  apply (UniversallyInjective.iff_diagonal f.hom).mpr
  rw [surjective_iff, ← Set.range_eq_univ]
  exact hrange

private theorem genericPoint_map_eq_of_surjective {V W : Geometric k} (f : Morphism V W)
    [IrreducibleSpace V.toScheme] [IrreducibleSpace W.toScheme]
    (hf : Function.Surjective f.hom) :
    f.hom (genericPoint V.toScheme) = genericPoint W.toScheme := by
  apply ((genericPoint_spec W.toScheme).eq _).symm
  convert! (genericPoint_spec V.toScheme).image f.hom.continuous
  rw [Set.image_univ, hf.range_eq, closure_univ]

private lemma pure_of_bijective
    {F E : Type*} [Field F] [Field E] (g : F →+* E) (hg : Function.Bijective g) :
    g.IsPurelyInseparable := by
  algebraize [g]
  refine ⟨⟨fun x ↦ ?_⟩, fun x _ ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := hg.2 x
    exact isIntegral_algebraMap
  · simpa only [RingHom.mem_range, RingHom.algebraMap_toAlgebra] using hg.2 x

private noncomputable def genericResidueIso (X : Scheme) [IsIntegral X] :
    X.functionField ≅ X.residueField (genericPoint X) := by
  letI : IsIso (X.residue (genericPoint X)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨RingHom.injective _, X.residue_surjective _⟩
  exact asIso (X.residue (genericPoint X))

@[simp] private lemma genericResidueIso_hom (X : Scheme) [IsIntegral X] :
    (genericResidueIso X).hom = X.residue (genericPoint X) := rfl

private noncomputable def functionFieldMap {V W : Geometric k} (f : Morphism V W)
    [IrreducibleSpace V.toScheme] [IrreducibleSpace W.toScheme]
    (hgeneric : f.hom (genericPoint V.toScheme) = genericPoint W.toScheme) :
    W.toScheme.functionField ⟶ V.toScheme.functionField :=
  (W.toScheme.presheaf.stalkCongr (.of_eq hgeneric.symm)).hom ≫
    f.hom.stalkMap (genericPoint V.toScheme)

private theorem residueFunctionFieldMap_isPurelyInseparable {V W : Geometric k}
    (f : Morphism V W) [IsIntegral V.toScheme] [IsIntegral W.toScheme]
    (hf : UniversallyInjective f.hom)
    (hgeneric : f.hom (genericPoint V.toScheme) = genericPoint W.toScheme) :
    let g : W.toScheme.functionField ⟶ V.toScheme.functionField :=
      W.toScheme.residue (genericPoint W.toScheme) ≫
        (W.toScheme.residueFieldCongr hgeneric.symm).hom ≫
        f.hom.residueFieldMap (genericPoint V.toScheme) ≫
        (genericResidueIso V.toScheme).inv
    g.hom.IsPurelyInseparable := by
  have hUI : UniversallyInjective f.hom ↔
      Function.Injective f.hom ∧
        ∀ x, (f.hom.residueFieldMap x).hom.IsPurelyInseparable :=
    (tfae_universallyInjective f.hom).out 0 2
  have hpure : ∀ x, (f.hom.residueFieldMap x).hom.IsPurelyInseparable := (hUI.mp hf).2
  have hres := pure_of_bijective
    (genericResidueIso W.toScheme).hom.hom
    (genericResidueIso W.toScheme).commRingCatIsoToRingEquiv.bijective
  have hcongr := pure_of_bijective
    (W.toScheme.residueFieldCongr hgeneric.symm).hom.hom
    ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance)
  have hfres := hpure (genericPoint V.toScheme)
  have hinv := pure_of_bijective
    (genericResidueIso V.toScheme).inv.hom
    (genericResidueIso V.toScheme).symm.commRingCatIsoToRingEquiv.bijective
  exact hres.comp hcongr |>.comp hfres |>.comp hinv

private theorem functionFieldMap_isPurelyInseparable {V W : Geometric k} (f : Morphism V W)
    [IsIntegral V.toScheme] [IsIntegral W.toScheme]
    (hf : UniversallyInjective f.hom)
    (hgeneric : f.hom (genericPoint V.toScheme) = genericPoint W.toScheme) :
    (functionFieldMap f hgeneric).hom.IsPurelyInseparable := by
  have hcomposition : functionFieldMap f hgeneric =
      W.toScheme.residue (genericPoint W.toScheme) ≫
        (W.toScheme.residueFieldCongr hgeneric.symm).hom ≫
        f.hom.residueFieldMap (genericPoint V.toScheme) ≫
        (genericResidueIso V.toScheme).inv := by
    rw [← cancel_mono (genericResidueIso V.toScheme).hom]
    simp only [functionFieldMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [genericResidueIso_hom]
    rw [← Scheme.residue_residueFieldMap]
    rw [← Category.assoc,
      ← Scheme.residue_residueFieldCongr W.toScheme hgeneric.symm]
    simp only [Category.assoc]
  rw [hcomposition]
  exact residueFunctionFieldMap_isPurelyInseparable f hf hgeneric

private theorem functionFieldMap_comp_germ {V W : Geometric k} (f : Morphism V W)
    [IsIntegral V.toScheme] [IsIntegral W.toScheme]
    (hgeneric : f.hom (genericPoint V.toScheme) = genericPoint W.toScheme)
    (U : W.toScheme.Opens) [Nonempty U] [Nonempty (f.hom ⁻¹ᵁ U)] :
    W.toScheme.germToFunctionField U ≫ functionFieldMap f hgeneric =
      f.hom.app U ≫ V.toScheme.germToFunctionField (f.hom ⁻¹ᵁ U) := by
  rw [functionFieldMap, ← Category.assoc, TopCat.Presheaf.stalkCongr_hom]
  erw [W.toScheme.presheaf.germ_stalkSpecializes]
  exact f.hom.germ_stalkMap U (genericPoint V.toScheme) _

private lemma integralClosure_exists_pow_mem_range
    {A B K L : Type*} [CommRing A] [CommRing B] [IsDomain B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsIntegrallyClosed A] [IsPurelyInseparable K L]
    (hBL : Function.Injective (algebraMap B L)) (z : integralClosure A B) :
    ∃ n > 0, z ^ n ∈ (algebraMap A (integralClosure A B)).range := by
  let q := ringExpChar K
  obtain ⟨m, x, hx⟩ := IsPurelyInseparable.pow_mem K q (algebraMap B L z.1)
  let n := q ^ m
  have hn : 0 < n := expChar_pow_pos K q m
  have hzIntegral : IsIntegral A ((algebraMap B L z.1) ^ n) :=
    (z.2.map (IsScalarTower.toAlgHom A B L)).pow n
  have hxIntegralL : IsIntegral A (algebraMap K L x) := hx.symm ▸ hzIntegral
  have hxIntegralK : IsIntegral A x :=
    (isIntegral_algebraMap_iff (algebraMap K L).injective).mp hxIntegralL
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxIntegralK
  refine ⟨n, hn, a, Subtype.ext ?_⟩
  apply hBL
  symm
  calc
    algebraMap B L (z ^ n).1 = (algebraMap B L z.1) ^ n := by simp
    _ = algebraMap K L x := hx.symm
    _ = algebraMap K L (algebraMap A K a) := by rw [ha]
    _ = algebraMap B L (algebraMap A B a) := by
      rw [← IsScalarTower.algebraMap_apply A K L,
        ← IsScalarTower.algebraMap_apply A B L]
    _ = algebraMap B L (algebraMap A (integralClosure A B) a).1 := by simp

private theorem normalizationChart_exists_pow {V W : Geometric k} (f : Morphism V W)
    [IsIntegral V.toScheme] [IsIntegral W.toScheme]
    (hW : IsNormal W) (hui : UniversallyInjective f.hom)
    (hsurj : Function.Surjective f.hom)
    (U : W.toScheme.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : Algebra Γ(W.toScheme, U) Γ(V.toScheme, f.hom ⁻¹ᵁ U) :=
      f.hom.app U |>.hom.toAlgebra
    ∀ z : integralClosure Γ(W.toScheme, U) Γ(V.toScheme, f.hom ⁻¹ᵁ U),
      ∃ n > 0, z ^ n ∈
        (algebraMap Γ(W.toScheme, U)
          (integralClosure Γ(W.toScheme, U) Γ(V.toScheme, f.hom ⁻¹ᵁ U))).range := by
  letI : Algebra Γ(W.toScheme, U) Γ(V.toScheme, f.hom ⁻¹ᵁ U) :=
    f.hom.app U |>.hom.toAlgebra
  let v : V.toScheme := hsurj (Classical.choice (inferInstance : Nonempty U)).1 |>.choose
  have hv : f.hom v ∈ U := by
    rw [hsurj (Classical.choice (inferInstance : Nonempty U)).1 |>.choose_spec]
    exact (Classical.choice (inferInstance : Nonempty U)).2
  letI : Nonempty (f.hom ⁻¹ᵁ U) := ⟨⟨v, hv⟩⟩
  have hgeneric := genericPoint_map_eq_of_surjective f hsurj
  letI : Algebra W.toScheme.functionField V.toScheme.functionField :=
    (functionFieldMap f hgeneric).hom.toAlgebra
  letI : Algebra Γ(W.toScheme, U) V.toScheme.functionField :=
    (W.toScheme.germToFunctionField U ≫ functionFieldMap f hgeneric).hom.toAlgebra
  letI : IsScalarTower Γ(W.toScheme, U) W.toScheme.functionField
      V.toScheme.functionField := IsScalarTower.of_algebraMap_eq' (by
    rfl)
  letI : IsScalarTower Γ(W.toScheme, U) Γ(V.toScheme, f.hom ⁻¹ᵁ U)
      V.toScheme.functionField := IsScalarTower.of_algebraMap_eq' (by
    simpa only [RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp] using
      congrArg CommRingCat.Hom.hom
      (functionFieldMap_comp_germ f hgeneric U))
  letI : IsFractionRing Γ(W.toScheme, U) W.toScheme.functionField :=
    functionField_isFractionRing_of_isAffineOpen W.toScheme U hU
  letI : IsIntegrallyClosed Γ(W.toScheme, U) :=
    affineSections_isIntegrallyClosed_of_isNormal hW hU
  letI : IsPurelyInseparable W.toScheme.functionField V.toScheme.functionField := by
    exact functionFieldMap_isPurelyInseparable f hui hgeneric
  exact fun z ↦ integralClosure_exists_pow_mem_range
    (A := Γ(W.toScheme, U)) (B := Γ(V.toScheme, f.hom ⁻¹ᵁ U))
    (K := W.toScheme.functionField) (L := V.toScheme.functionField)
    (V.toScheme.germToFunctionField_injective (f.hom ⁻¹ᵁ U)) z

private theorem fromNormalization_app_spec_injective {V W : Geometric k} (f : Morphism V W)
    [IsIntegral V.toScheme] [IsIntegral W.toScheme]
    (hW : IsNormal W) (hui : UniversallyInjective f.hom)
    (hsurj : Function.Surjective f.hom)
    (U : W.toScheme.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    Function.Injective (Spec.map (f.hom.fromNormalization.app U)) := by
  letI : Surjective f.hom := ⟨hsurj⟩
  letI : IsSchemeTheoreticallyDominant f.hom :=
    IsSchemeTheoreticallyDominant.of_isDominant f.hom
  letI : Algebra Γ(W.toScheme, U) Γ(V.toScheme, f.hom ⁻¹ᵁ U) :=
    f.hom.app U |>.hom.toAlgebra
  have hAC : Function.Injective
      (algebraMap Γ(W.toScheme, U)
        (integralClosure Γ(W.toScheme, U) Γ(V.toScheme, f.hom ⁻¹ᵁ U))) := by
    intro a b hab
    apply f.hom.app_injective U
    have hab' := congrArg Subtype.val hab
    change f.hom.app U a = f.hom.app U b at hab'
    exact hab'
  have hpow := normalizationChart_exists_pow f hW hui hsurj U hU
  have hhome := PrimeSpectrum.isHomeomorph_comap
    (algebraMap Γ(W.toScheme, U)
      (integralClosure Γ(W.toScheme, U) Γ(V.toScheme, f.hom ⁻¹ᵁ U)))
    hpow (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hAC]; exact bot_le)
  have hSpecAlg : Function.Injective
      (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(W.toScheme, U)
          (integralClosure Γ(W.toScheme, U) Γ(V.toScheme, f.hom ⁻¹ᵁ U))))) :=
    hhome.injective
  have hmorphism : Spec.map (f.hom.fromNormalization.app U) =
      Spec.map (f.hom.normalizationObjIso hU).inv ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap Γ(W.toScheme, U)
            (integralClosure Γ(W.toScheme, U) Γ(V.toScheme, f.hom ⁻¹ᵁ U)))) := by
    rw [f.hom.fromNormalization_app hU, ← Spec.map_comp]
  intro x y hxy
  apply (Spec.map (f.hom.normalizationObjIso hU).inv).injective
  apply hSpecAlg
  rw [hmorphism] at hxy
  exact hxy

private theorem fromNormalization_injective {V W : Geometric k} (f : Morphism V W)
    [IsIntegral V.toScheme] [IsIntegral W.toScheme]
    (hW : IsNormal W) (hui : UniversallyInjective f.hom)
    (hsurj : Function.Surjective f.hom) :
    Function.Injective f.hom.fromNormalization := by
  intro x y hxy
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    W.toScheme.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f.hom.fromNormalization x)) isOpen_univ
  have hyU : f.hom.fromNormalization y ∈ U := by
    rwa [← hxy]
  letI : Nonempty U := ⟨⟨f.hom.fromNormalization x, hxU⟩⟩
  have hpre : IsAffineOpen (f.hom.fromNormalization ⁻¹ᵁ U) :=
    hU.preimage f.hom.fromNormalization
  have hprime :
      hpre.primeIdealOf ⟨x, hxU⟩ = hpre.primeIdealOf ⟨y, hyU⟩ := by
    apply fromNormalization_app_spec_injective f hW hui hsurj U hU
    change (hpre.primeIdealOf ⟨x, hxU⟩).comap
        (f.hom.fromNormalization.app U).hom =
      (hpre.primeIdealOf ⟨y, hyU⟩).comap
        (f.hom.fromNormalization.app U).hom
    rw [f.hom.fromNormalization.app_eq_appLE,
      IsAffineOpen.comap_primeIdealOf_appLE U hU _ hpre le_rfl hxU,
      IsAffineOpen.comap_primeIdealOf_appLE U hU _ hpre le_rfl hyU]
    congr 1
    exact Subtype.ext hxy
  have hsub : (⟨x, hxU⟩ : f.hom.fromNormalization ⁻¹ᵁ U) = ⟨y, hyU⟩ :=
    hpre.isoSpec.hom.homeomorph.injective hprime
  exact congrArg Subtype.val hsub

/-- Bor1 AG.18.3: the integral relative normalization of a bijective morphism from an
irreducible variety to a normal variety factors through the source by a surjective morphism.

The second equality is the normalization factorization `β = γ ≫ f`; the first records that
`γ` is inverse on the image of the relative-normalization map from `V`.
-/
theorem exists_surjective_normalization_factorization_of_bijective
    {V W : Geometric k} (f : Morphism V W) [IsAlgClosed k]
    (hV : IsIrreducible V) (hW : IsNormal W)
    (hf : Function.Bijective f.hom) :
    ∃ gamma : f.hom.normalization ⟶ V.toScheme,
      Function.Surjective gamma ∧
        f.hom.toNormalization ≫ gamma = 𝟙 V.toScheme ∧
          f.hom.fromNormalization = gamma ≫ f.hom := by
  letI : IrreducibleSpace V.toScheme := hV
  letI : IrreducibleSpace W.toScheme :=
    hf.2.irreducibleSpace f.hom.continuous
  letI : IsIntegral V.toScheme :=
    isIntegral_of_irreducibleSpace_of_isReduced V.toScheme
  letI : IsIntegral W.toScheme :=
    isIntegral_of_irreducibleSpace_of_isReduced W.toScheme
  have hui : UniversallyInjective f.hom :=
    universallyInjective_of_injective f hf.1
  have hfrom : Function.Injective f.hom.fromNormalization :=
    fromNormalization_injective f hW hui hf.2
  have hto : Function.Surjective f.hom.toNormalization := by
    intro z
    obtain ⟨x, hx⟩ := hf.2 (f.hom.fromNormalization z)
    refine ⟨x, hfrom ?_⟩
    rw [← Scheme.Hom.comp_apply, f.hom.toNormalization_fromNormalization]
    exact hx
  letI : UniversallyInjective f.hom := hui
  letI : LocallyQuasiFinite f.hom :=
    LocallyQuasiFinite.of_injective hf.1
  letI : Surjective f.hom.toNormalization := ⟨hto⟩
  letI : IsIso f.hom.toNormalization :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr
      ⟨inferInstance, inferInstance⟩
  letI : IsIntegralHom f.hom := by
    rw [← f.hom.toNormalization_fromNormalization]
    infer_instance
  let gamma : f.hom.normalization ⟶ V.toScheme :=
    f.hom.normalizationDesc (𝟙 V.toScheme) f.hom (by simp)
  refine ⟨gamma, ?_, ?_, ?_⟩
  · intro x
    refine ⟨f.hom.toNormalization x, ?_⟩
    rw [← Scheme.Hom.comp_apply,
      f.hom.toNormalization_normalizationDesc (𝟙 V.toScheme) f.hom (by simp)]
    rfl
  · exact f.hom.toNormalization_normalizationDesc (𝟙 V.toScheme) f.hom (by simp)
  · exact (f.hom.normalizationDesc_comp (𝟙 V.toScheme) f.hom (by simp)).symm

/-- Bor1 10.1(4), with the irreducible-source hypothesis restored from its cited AG.18.3:
a bijective morphism to a normal complete variety has complete source.

The hypothesis cannot be omitted for this repository's possibly disconnected carrier: one may
map the disjoint union of a punctured projective line and the missing point bijectively to the
projective line.  The proof uses the AG.18.3 relative-normalization factorization above and
descends universal closedness along its surjective factor.
-/
theorem isComplete_of_bijective_morphism_to_normal_complete
    {V W : Geometric k} (f : Morphism V W) [IsAlgClosed k]
    (hV : IsIrreducible V) (hW : IsNormal W)
    (hf : Function.Bijective f.hom) (hWcomplete : IsComplete W) :
    IsComplete V := by
  obtain ⟨gamma, hgamma, -, hfactor⟩ :=
    exists_surjective_normalization_factorization_of_bijective f hV hW hf
  letI : Surjective gamma := ⟨hgamma⟩
  exact isComplete_of_surjective_factorization_of_isIntegralHom
    f f.hom.normalization f.hom.fromNormalization gamma hfactor hWcomplete

end Theory.AlgebraicGroup.Variety.Geometric
