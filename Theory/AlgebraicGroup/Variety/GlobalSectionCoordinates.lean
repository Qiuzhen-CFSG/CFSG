module
public import Theory.AlgebraicGroup.Variety.AffineGeometricMorphism
public import Theory.AlgebraicGroup.Variety.GeometricClosedImage

/-!
# Geometric maps specified by global regular coordinates

Global sections of a reduced finite-type variety over an algebraically closed
field are determined by their evaluations at rational points. A section with
no rational zero is a unit. Both assertions follow from the basic-open germ
criterion and the existence of closed points in nonempty locally closed sets.

Consequently a point map into a presented affine variety whose coordinate
functions are global regular sections is induced by a genuine geometric
morphism. We factor the polynomial coordinate map through the full vanishing
ideal and use the global-sections–Spec adjunction. Its point map is certified
exactly, not inferred from topological bijectivity.

This is the global-section form of the affine mapping property used in Borel,
*Linear Algebraic Groups*, AG §§1 and 7, and in the local constructions of §10.8.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace Theory.AlgebraicGroup.Variety.Geometric
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
public noncomputable section

@[expose] def sectionEvaluation (V : Geometric k) (x : Point V) : Γ(V.toScheme, ⊤) →+* k :=
  (Scheme.ΓSpecIso (.of k)).hom.hom.comp x.1.appTop.hom

omit [IsAlgClosed k] in
set_option backward.isDefEq.respectTransparency.types false in
private lemma spec_basicOpen_nonzero (s : Γ(Spec (.of k), ⊤)) :
    (IsLocalRing.closedPoint k : Spec (.of k)) ∈ (Spec (.of k)).basicOpen s ↔
      (Scheme.ΓSpecIso (.of k)).hom s ≠ 0 := by
  rw [basicOpen_eq_of_affine']
  change _ ∉ (IsLocalRing.closedPoint k).asIdeal ↔ _ ≠ 0
  have hclosed : (IsLocalRing.closedPoint k).asIdeal = (⊥ : Ideal k) :=
    (Ideal.eq_bot_or_top _).resolve_right (IsLocalRing.closedPoint k).isPrime.ne_top
  rw [hclosed]
  simp

omit [IsAlgClosed k] in
lemma closedPoint_mem_basicOpen_iff_evaluation (V : Geometric k) (x : Point V)
    (s : Γ(V.toScheme, ⊤)) :
    x.1 (IsLocalRing.closedPoint k) ∈ V.toScheme.basicOpen s ↔ sectionEvaluation V x s ≠ 0 := by
  change IsLocalRing.closedPoint k ∈ x.1 ⁻¹ᵁ V.toScheme.basicOpen s ↔ _
  rw [Scheme.preimage_basicOpen_top]
  exact spec_basicOpen_nonzero _

lemma section_eq_zero_of_evaluations (V : Geometric k) (s : Γ(V.toScheme, ⊤))
    (hs : ∀ x : Point V, sectionEvaluation V x s = 0) : s = 0 := by
  apply AlgebraicGeometry.eq_zero_of_basicOpen_eq_bot s
  apply TopologicalSpace.Opens.ext
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have : JacobsonSpace V.toScheme := LocallyOfFiniteType.jacobsonSpace V.structureMap
  obtain ⟨w, hw, hwclosed⟩ := nonempty_inter_closedPoints
    (show (V.toScheme.basicOpen s : Set V.toScheme).Nonempty from ⟨z, hz⟩)
    (V.toScheme.basicOpen s).isOpen.isLocallyClosed
  let x : Point V := ⟨pointOfClosedPoint V.structureMap w hwclosed,
    pointOfClosedPoint_comp V.structureMap w hwclosed⟩
  have hx : x.1 (IsLocalRing.closedPoint k) = w := pointOfClosedPoint_apply V.structureMap w hwclosed _
  have hn := (closedPoint_mem_basicOpen_iff_evaluation V x s).mp (hx ▸ hw)
  exact hn (hs x)

lemma section_isUnit_of_evaluations (V : Geometric k) (s : Γ(V.toScheme, ⊤))
    (hs : ∀ x : Point V, sectionEvaluation V x s ≠ 0) : IsUnit s := by
  apply V.toScheme.toRingedSpace.isUnit_of_isUnit_germ ⊤ s
  intro z hz
  apply (V.toScheme.toRingedSpace.mem_basicOpen s z hz).mp
  by_contra hznot
  have : JacobsonSpace V.toScheme := LocallyOfFiniteType.jacobsonSpace V.structureMap
  obtain ⟨w, hw, hwclosed⟩ := nonempty_inter_closedPoints
    (show ((V.toScheme.basicOpen s : Set V.toScheme)ᶜ).Nonempty from ⟨z, hznot⟩)
    (V.toScheme.basicOpen s).isOpen.isClosed_compl.isLocallyClosed
  let x : Point V := ⟨pointOfClosedPoint V.structureMap w hwclosed,
    pointOfClosedPoint_comp V.structureMap w hwclosed⟩
  have hx : x.1 (IsLocalRing.closedPoint k) = w := pointOfClosedPoint_apply V.structureMap w hwclosed _
  exact hw (hx ▸ (closedPoint_mem_basicOpen_iff_evaluation V x s).mpr (hs x))

def scalarSectionMap (V : Geometric k) : k →+* Γ(V.toScheme, ⊤) :=
  V.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

omit [IsAlgClosed k] in
lemma sectionEvaluation_scalar (V : Geometric k) (x : Point V) (r : k) :
    sectionEvaluation V x (scalarSectionMap V r) = r := by
  change (Scheme.ΓSpecIso (.of k)).hom
    (x.1.appTop (V.structureMap.appTop ((Scheme.ΓSpecIso (.of k)).inv r))) = r
  have he : V.structureMap.appTop ≫ x.1.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, x.2]
    rfl
  have heval := congrArg (fun φ => φ ((Scheme.ΓSpecIso (.of k)).inv r)) he
  change x.1.appTop (V.structureMap.appTop ((Scheme.ΓSpecIso (.of k)).inv r)) =
    (Scheme.ΓSpecIso (.of k)).inv r at heval
  rw [heval]
  simp

private def sectionCoordinatesMap {V : Geometric k} {W : Variety k}
    (c : W.Coordinates → Γ(V.toScheme, ⊤)) :
    MvPolynomial W.Coordinates k →+* Γ(V.toScheme, ⊤) :=
  MvPolynomial.eval₂Hom (scalarSectionMap V) c

omit [IsAlgClosed k] in
private lemma sectionCoordinatesMap_evaluation {V : Geometric k} {W : Variety k}
    (c : W.Coordinates → Γ(V.toScheme, ⊤)) (x : Point V)
    (p : MvPolynomial W.Coordinates k) :
    sectionEvaluation V x (sectionCoordinatesMap c p) =
      evalPolynomial (fun i => sectionEvaluation V x (c i)) p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [sectionCoordinatesMap, sectionEvaluation_scalar, evalPolynomial]
  | add p q hp hq => simpa only [map_add, hp, hq] using
      (show evalPolynomial (fun i => sectionEvaluation V x (c i)) p +
        evalPolynomial (fun i => sectionEvaluation V x (c i)) q =
        evalPolynomial (fun i => sectionEvaluation V x (c i)) (p + q) from by simp [evalPolynomial])
  | mul_X p i hp =>
      rw [map_mul, map_mul, hp, evalPolynomial_mul]
      congr 1
      simp [sectionCoordinatesMap, evalPolynomial]

private def sectionCoordinatePullback {V : Geometric k} {W : Variety k}
    (ψ : Point V → Variety.Point W) (c : W.Coordinates → Γ(V.toScheme, ⊤))
    (hc : ∀ x i, sectionEvaluation V x (c i) = (ψ x).val i) :
    coordinateRing W →+* Γ(V.toScheme, ⊤) :=
  Ideal.Quotient.lift _ (sectionCoordinatesMap c) (by
    intro p hp
    apply section_eq_zero_of_evaluations V
    intro x
    rw [sectionCoordinatesMap_evaluation]
    simp only [hc]
    exact hp (ψ x) (Set.mem_univ _))

private lemma sectionCoordinatePullback_scalar {V : Geometric k} {W : Variety k}
    (ψ : Point V → Variety.Point W) (c : W.Coordinates → Γ(V.toScheme, ⊤))
    (hc : ∀ x i, sectionEvaluation V x (c i) = (ψ x).val i) (r : k) :
    sectionCoordinatePullback ψ c hc (algebraMap k (coordinateRing W) r) = scalarSectionMap V r := by
  change sectionCoordinatePullback ψ c hc (Ideal.Quotient.mk _ (MvPolynomial.C r)) = _
  simp [sectionCoordinatePullback, sectionCoordinatesMap]

/-- A point map into an affine presentation is geometric when its coordinates
are evaluations of global regular sections. -/
def morphismOfSectionCoordinates {V : Geometric k} {W : Variety k}
    (ψ : Point V → Variety.Point W) (c : W.Coordinates → Γ(V.toScheme, ⊤))
    (hc : ∀ x i, sectionEvaluation V x (c i) = (ψ x).val i) : Morphism V (ofAffine W) where
  hom := V.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (sectionCoordinatePullback ψ c hc))
  commutes := by
    change (V.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (sectionCoordinatePullback ψ c hc))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (coordinateRing W))) = V.structureMap
    rw [Category.assoc, ← Spec.map_comp]
    have he : CommRingCat.ofHom (algebraMap k (coordinateRing W)) ≫
        CommRingCat.ofHom (sectionCoordinatePullback ψ c hc) =
        CommRingCat.ofHom (scalarSectionMap V) := by
      ext r
      exact sectionCoordinatePullback_scalar ψ c hc r
    rw [he]
    change V.toScheme.toSpecΓ ≫ Spec.map
      ((Scheme.ΓSpecIso (.of k)).inv ≫ V.structureMap.appTop) = _
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    rw [Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

omit [IsAlgClosed k] in
private lemma point_toSpec_sections {V : Geometric k} (x : Point V)
    {R : Type u} [CommRing R] (q : R →+* Γ(V.toScheme, ⊤)) :
    Spec.preimage (x.1 ≫ V.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom q)) =
      CommRingCat.ofHom ((sectionEvaluation V x).comp q) := by
  apply Spec.map_injective
  rw [Spec.map_preimage, ← Category.assoc, Scheme.toSpecΓ_naturality]
  rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, ← Spec.map_comp]
  rfl

lemma morphismOfSectionCoordinates_apply {V : Geometric k} {W : Variety k}
    (ψ : Point V → Variety.Point W) (c : W.Coordinates → Γ(V.toScheme, ⊤))
    (hc : ∀ x i, sectionEvaluation V x (c i) = (ψ x).val i) (x : Point V) :
    affinePointEquiv W (morphismOfSectionCoordinates ψ c hc x) = ψ x := by
  apply (coordinateRingPointAlgHomEquiv W).injective
  erw [coordinateRingPointAlgHomEquiv_affinePointEquiv]
  apply AlgHom.ext
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  change (Spec.preimage (x.1 ≫ V.toScheme.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (sectionCoordinatePullback ψ c hc)))).hom (Ideal.Quotient.mk _ p) = _
  rw [point_toSpec_sections]
  change sectionEvaluation V x (sectionCoordinatesMap c p) = _
  rw [sectionCoordinatesMap_evaluation]
  simp only [hc, coordinateRingPointAlgHomEquiv_apply, coordinatePointAlgHom_apply,
    coordinateRingAlgEquivPolynomialFunction_mk]
  rfl

end
end Theory.AlgebraicGroup.Variety.Geometric
