module
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.MinimalOrbit.FiberDimension
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.MinimalOrbit.HomogeneousDimension
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# The fibre dimension formula on integral affine geometric varieties

For a dominant morphism between integral affine geometric varieties, constant
dimension `d` of all nonempty open pieces of rational scheme fibres gives
`dim V = dim W + d`. The coordinate algebras come from the actual structure
maps to `Spec k`; scheme-theoretic dominance makes their pullback injective.
At a closed point, the quotient by the extended maximal ideal has the same
underlying space as the actual scheme fibre. This applies `FiberDimension`
without identifying nonreduced fibres with reduced stabilizer schemes.

This is the affine case of the orbit-dimension argument in Borel, *Linear
Algebraic Groups*, §11.1 (`refs/KGroup/Bor1/Chapter4.tex`).
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry Topology Cardinal
universe u
namespace Theory.AlgebraicGroup.Variety.Geometric.MinimalOrbit

private noncomputable def spectrumQuotientFiberHomeomorph
    {B A : Type u} [CommRing B] [CommRing A] (φ : B →+* A)
    (N : Ideal B) [N.IsMaximal] :
    PrimeSpectrum (A ⧸ N.map φ) ≃ₜ
      (Spec.map (CommRingCat.ofHom φ)).fiber ⟨N, inferInstance⟩ := by
  let J := N.map φ
  let j := PrimeSpectrum.isEmbedding_comap_of_surjective _ _
    (Ideal.Quotient.mk_surjective (I := J))
  apply j.toHomeomorph.trans
  apply Homeomorph.trans _ ((Spec.map (CommRingCat.ofHom φ)).fiberHomeo _).symm
  apply Homeomorph.setCongr
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  ext p
  change J ≤ p.asIdeal ↔ PrimeSpectrum.comap φ p = ⟨N, inferInstance⟩
  rw [Ideal.map_le_iff_le_comap, PrimeSpectrum.ext_iff]
  constructor
  · intro h
    exact (Ideal.IsMaximal.eq_of_le inferInstance (Ideal.comap_isPrime φ p.asIdeal).ne_top h).symm
  · intro h
    exact h.ge

private noncomputable def schemeFiberHomeomorphOfHomeomorphs
    {V W V' W' : Scheme.{u}} (f : V ⟶ W) (f' : V' ⟶ W')
    (eV : V ≃ₜ V') (eW : W ≃ₜ W')
    (hcomm : ∀ v, f' (eV v) = eW (f v)) (y : W) :
    f.fiber y ≃ₜ f'.fiber (eW y) := by
  apply (f.fiberHomeo y).trans
  apply Homeomorph.trans ((eV.image _).trans _) (f'.fiberHomeo (eW y)).symm
  apply Homeomorph.setCongr
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    change f' (eV v) = eW y
    change f v = y at hv
    rw [hcomm, hv]
  · intro hz
    refine ⟨eV.symm z, ?_, eV.apply_symm_apply z⟩
    change f (eV.symm z) = y
    apply eW.injective
    rw [← hcomm, eV.apply_symm_apply]
    exact hz

set_option backward.isDefEq.respectTransparency false in
/-- The genuine affine scheme fibre dimension formula, allowing nonreduced fibres. -/
public theorem affine_dimension_eq_add_of_constant_fiber_open_dimension
    {k : Type u} [Field k] [IsAlgClosed k]
    {V W : Geometric k} [IsAffine V.toScheme] [IsAffine W.toScheme]
    [IrreducibleSpace V.toScheme] [IrreducibleSpace W.toScheme]
    (f : Morphism V W) [IsDominant f.hom] (d : ℕ)
    (hfiber : ∀ y : Point W,
      ∀ U : (f.hom.fiber (y.1 (IsLocalRing.closedPoint k))).Opens,
        (U : Set (f.hom.fiber (y.1 (IsLocalRing.closedPoint k)))).Nonempty →
          topologicalKrullDim U = (d : WithBot ℕ∞)) :
    dimension V = dimension W + (d : WithBot ℕ∞) := by
  let : IsIntegral V.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  let : IsIntegral W.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  let A := Γ(V.toScheme, ⊤)
  let B := Γ(W.toScheme, ⊤)
  let ek : k ≃+* Γ(Spec (.of k), ⊤) :=
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv
  let kA : k →+* A := V.structureMap.appTop.hom.comp ek.toRingHom
  let kB : k →+* B := W.structureMap.appTop.hom.comp ek.toRingHom
  let φ : B →+* A := f.hom.appTop.hom
  let : Algebra k A := kA.toAlgebra
  let : Algebra k B := kB.toAlgebra
  let : Algebra B A := φ.toAlgebra
  let : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq' (by
    change kA = φ.comp kB
    dsimp [kA, kB, φ]
    rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp,
      ← Scheme.Hom.comp_appTop, f.commutes])
  have hfinite (Y : Geometric k) [IsAffine Y.toScheme] :
      (Y.structureMap.appTop.hom.comp ek.toRingHom).FiniteType := by
    apply RingHom.FiniteType.comp _ (RingHom.FiniteType.of_surjective _ ek.surjective)
    simpa [Scheme.Hom.appLE] using
      Y.structureMap.finiteType_appLE (isAffineOpen_top _) (isAffineOpen_top _) le_rfl
  let : Algebra.FiniteType k A := hfinite V
  let : Algebra.FiniteType k B := hfinite W
  let : QuasiCompact f.hom := by
    have : QuasiCompact (f.hom ≫ W.structureMap) := by rw [f.commutes]; infer_instance
    exact QuasiCompact.of_comp f.hom W.structureMap
  let : IsSchemeTheoreticallyDominant f.hom := .of_isDominant _
  let : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr
    (f.hom.app_injective ⊤)
  let eA : V.toScheme ≃ₜ PrimeSpectrum A := Scheme.homeoOfIso V.toScheme.isoSpec
  let eB : W.toScheme ≃ₜ PrimeSpectrum B := Scheme.homeoOfIso W.toScheme.isoSpec
  have hcomm (v : V.toScheme) :
      (Spec.map (CommRingCat.ofHom φ)) (eA v) = eB (f.hom v) := by
    exact (congrArg (fun g : V.toScheme ⟶ Spec B => g v)
      (Scheme.toSpecΓ_naturality f.hom)).symm
  have hdim : ringKrullDim A = ringKrullDim B + (d : WithBot ℕ∞) := by
    apply ringKrullDim_eq_add_of_constant_fiber_open_dimension (k := k) d
    intro M hM U hUne
    let m : PrimeSpectrum A := ⟨M, hM.isPrime⟩
    have hmclosed : IsClosed ({m} : Set (PrimeSpectrum A)) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal m).mpr hM
    let v := eA.symm m
    have hvclosed : IsClosed ({v} : Set V.toScheme) := by
      have hv : ({v} : Set V.toScheme) = eA ⁻¹' {m} := by
        ext a
        simp [v, ← eA.injective.eq_iff]
      rw [hv]
      exact hmclosed.preimage eA.continuous
    let a : Point V := (pointEquivClosedPoint V.structureMap).symm ⟨v, hvclosed⟩
    have hav : a.1 (IsLocalRing.closedPoint k) = v :=
      congrArg Subtype.val ((pointEquivClosedPoint V.structureMap).apply_symm_apply ⟨v, hvclosed⟩)
    let y : Point W := f a
    let N := M.under B
    have hp : PrimeSpectrum.comap φ m = eB (y.1 (IsLocalRing.closedPoint k)) := by
      change PrimeSpectrum.comap φ m = eB (f.hom (a.1 (IsLocalRing.closedPoint k)))
      rw [← hcomm]
      change PrimeSpectrum.comap φ m = PrimeSpectrum.comap φ (eA (a.1 (IsLocalRing.closedPoint k)))
      rw [hav]
      exact congrArg (PrimeSpectrum.comap φ) (eA.apply_symm_apply m).symm
    have hNclosed : IsClosed ({PrimeSpectrum.comap φ m} : Set (PrimeSpectrum B)) := by
      rw [hp, ← Set.image_singleton]
      exact eB.isClosedMap _ (pointEquivClosedPoint W.structureMap y).2
    let : N.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal (PrimeSpectrum.comap φ m)).mp hNclosed
    let eF := schemeFiberHomeomorphOfHomeomorphs f.hom (Spec.map (CommRingCat.ofHom φ))
      eA eB hcomm (y.1 (IsLocalRing.closedPoint k))
    have ep : (⟨N, inferInstance⟩ : PrimeSpectrum B) = eB (y.1 (IsLocalRing.closedPoint k)) := hp
    let eQ := spectrumQuotientFiberHomeomorph φ N
    let e : PrimeSpectrum (A ⧸ N.map φ) ≃ₜ f.hom.fiber (y.1 (IsLocalRing.closedPoint k)) :=
      eQ.trans ((by rw [ep]; exact eF.symm) :
        (Spec.map (CommRingCat.ofHom φ)).fiber ⟨N, inferInstance⟩ ≃ₜ _)
    let T : (f.hom.fiber (y.1 (IsLocalRing.closedPoint k))).Opens :=
      ⟨e '' (U : Set _), e.isOpenMap _ U.2⟩
    have hT : (T : Set (f.hom.fiber (y.1 (IsLocalRing.closedPoint k)))).Nonempty := hUne.image e
    have heU : topologicalKrullDim U = topologicalKrullDim T :=
      (e.image (U : Set (PrimeSpectrum (A ⧸ N.map φ)))).isHomeomorph.topologicalKrullDim_eq
    exact heU.trans (hfiber y T hT)
  have hdA := eA.isHomeomorph.topologicalKrullDim_eq
  have hdB := eB.isHomeomorph.topologicalKrullDim_eq
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at hdA hdB
  exact hdA.trans (hdim.trans (congrArg (fun n => n + (d : WithBot ℕ∞)) hdB.symm))

end Theory.AlgebraicGroup.Variety.Geometric.MinimalOrbit
