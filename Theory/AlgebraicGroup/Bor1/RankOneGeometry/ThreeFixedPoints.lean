module

public import Theory.AlgebraicGroup.Dimension.ProjectiveHyperplane
public import Theory.AlgebraicGroup.Variety.MorphicActionComponents
public import Theory.AlgebraicGroup.Bor1.TorusBorelGeneration.ProjectiveHyperplane
public import Theory.AlgebraicGroup.Unipotent.Radical
/-!
# Three torus fixed points on a complete variety of dimension at least two

Embed the variety equivariantly in projective space. A dual weight supplies an
invariant hyperplane missing one fixed point. Completeness forces the variety
to meet that hyperplane, and the principal-equation estimate makes the section
positive-dimensional. A connected torus preserves each irreducible component;
a positive-dimensional component has two distinct rational points and therefore
two fixed points by the affine-chart escape argument. Together with the omitted
point these are three distinct fixed points.

This is Borel, *Linear Algebraic Groups*, §13.5, in the precise equivariant
projective form used for the rank-one Borel orbit in §§13.9 and 13.13.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open scoped LinearAlgebra.Projectivization
namespace Theory.AlgebraicGroup.Variety.Geometric
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {E : Type u} [AddCommGroup E] [Module k E] [FiniteDimensional k E]
variable {G : Variety k} [AlgebraicGroup G] {X : Geometric k}

omit [IsAlgClosed k] in
private theorem pointMap_injective {V W : Geometric k} (f : Morphism V W)
    [IsClosedImmersion f.hom] : Function.Injective (fun p : Point V => f p) := by
  intro x y h
  apply Subtype.ext
  exact (cancel_mono f.hom).mp (congrArg Subtype.val h)

omit [IsAlgClosed k] in
private theorem exists_image_ne (f : Point X → Point (projectiveSpace k E))
    (x z : Point X) (hxz : f x ≠ f z) (p : Point X) : ∃ w, f p ≠ f w := by
  by_cases h : f p = f x
  · exact ⟨z,by rwa [h]⟩
  · exact ⟨x,h⟩

theorem MorphicAction.exists_two_fixedPoints_of_torus
    (A : MorphicAction G X) (hG : IsTorus G) (hX : IsComplete X) (hconn : IsConnected X)
    (ρ : RationalRepresentation G E) (hρ : IsRationalRepresentation ρ)
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (f : Morphism X (projectiveSpace k E))
    (he : ∀ (t : Variety.Point G) (x : Point X),
      projectiveSpacePointEquivOf b (f (A.toMulAction.smul t x)) =
      Projectivization.map (ρ.action t).1 (ρ.action t).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b (f x)))
    (x z : Point X) (hxz : f x ≠ f z) :
    ∃ p q : Point X, (∀ t : Variety.Point G, A.toMulAction.smul t p = p) ∧
      (∀ t : Variety.Point G, A.toMulAction.smul t q = q) ∧ f p ≠ f q := by
  have hsol : Group.IsSolvable (Variety.Point G) :=
    Group.isSolvable_of_comm (isMulCommutative_iff.mp hG.isMulCommutative)
  obtain ⟨p,hp⟩ := A.exists_fixedPoint_of_isConnected_isSolvable_isComplete
    hG.isConnected hsol hX ⟨x⟩
  obtain ⟨w,hw⟩ := exists_image_ne (fun x => f x) x z hxz p
  let T : ClosedSubgroup G := ClosedSubgroup.top
  obtain ⟨q,hq,hqp⟩ := A.exists_torus_fixedPoint_separating hX hconn ρ hρ T
    (closedSubgroup_top_isTorus G hG) b f (fun t x => he (T.includePoint t) x) p w hw
  refine ⟨p,q,hp,?_,hqp.symm⟩
  intro t
  have h := hq (T.pointEquiv.symm ⟨t,by trivial⟩)
  simpa only [ClosedSubgroup.includePoint, Equiv.apply_symm_apply] using h


theorem MorphicAction.exists_three_fixedPoints_of_dimension_ge_two
    (A : MorphicAction G X) (hG : IsTorus G) (hX : IsComplete X)
    [IrreducibleSpace X.toScheme] (hdim : 2 ≤ dimension X)
    (ρ : RationalRepresentation G E) (hρ : IsRationalRepresentation ρ)
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (f : Morphism X (projectiveSpace k E)) [IsClosedImmersion f.hom]
    (he : ∀ (t : Variety.Point G) (x : Point X),
      projectiveSpacePointEquivOf b (f (A.toMulAction.smul t x)) =
      Projectivization.map (ρ.action t).1 (ρ.action t).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b (f x))) :
    ∃ x y z : Point X,
      (∀ t : Variety.Point G, A.toMulAction.smul t x = x) ∧
      (∀ t : Variety.Point G, A.toMulAction.smul t y = y) ∧
      (∀ t : Variety.Point G, A.toMulAction.smul t z = z) ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  classical
  have hXpos : ¬dimension X ≤ 0 := by
    intro h
    have hh := hdim.trans h
    norm_num at hh
  obtain ⟨D₀,x₀,z₀,hxz₀⟩ := exists_component_distinct_points X hXpos
  let i₀ := (reducedIrreducibleComponent X D₀).inclusion
  have hfxz : f (i₀ x₀) ≠ f (i₀ z₀) := by
    intro hh
    exact hxz₀ (pointMap_injective i₀ (pointMap_injective f hh))
  obtain ⟨x,_,hxfixed,_,_⟩ := A.exists_two_fixedPoints_of_torus hG hX
    (inferInstance : ConnectedSpace X.toScheme) ρ hρ b f he _ _ hfxz
  obtain ⟨w,hw⟩ := exists_image_ne (fun x => f x) _ _ hfxz x
  obtain ⟨v,hv,hfx⟩ := exists_projective_vector b (f x)
  let T : ClosedSubgroup G := ClosedSubgroup.top
  obtain ⟨l,hlv,hlinv⟩ := exists_invariant_dual_nonzero ρ hρ T
    (closedSubgroup_top_isTorus G hG) v hv
  have hlinv' (g : Variety.Point G) (v : E) (hv : l v = 0) :
      l ((ρ.action g).1 v) = 0 := by
    have hh := hlinv (T.pointEquiv.symm ⟨g,by trivial⟩) v hv
    simpa only [ClosedSubgroup.includePoint,Equiv.apply_symm_apply] using hh
  let U := projectiveHyperplaneOpen b l
  have hxU : (f x).1 (IsLocalRing.closedPoint k) ∈ U := by
    rw [hfx]
    exact (projectiveHyperplaneOpen_vector_mem_iff b l v hv).mpr hlv
  obtain ⟨w',hw'⟩ := f.exists_point_outside_affine_open
    (inferInstance : ConnectedSpace X.toScheme) hX U x w hw
  let Z : Closeds X.toScheme :=
    ⟨(f.hom ⁻¹' (U : Set (projectiveSpace k E).toScheme))ᶜ,
      (U.isOpen.preimage f.hom.continuous).isClosed_compl⟩
  let C := reducedClosedSubvariety X Z
  have hZne : (Z : Set X.toScheme).Nonempty :=
    ⟨w'.1 (IsLocalRing.closedPoint k),hw'⟩
  have hCdim : dimension C.toGeometric = topologicalKrullDim (Z : Set X.toScheme) := by
    let e₁ := C.inclusion.hom.isClosedEmbedding.isEmbedding.toHomeomorph
    let e₂ : Set.range C.inclusion.hom ≃ₜ (Z : Set X.toScheme) :=
      Homeomorph.setCongr (reducedClosedSubvariety_range X Z)
    exact (e₁.trans e₂).isHomeomorph.topologicalKrullDim_eq
  have hCpos : ¬dimension C.toGeometric ≤ 0 := by
    intro hzero
    have hZne' := hZne
    change ((f.hom ⁻¹' (projectiveHyperplaneOpen b l : Set (projectiveSpace k E).toScheme))ᶜ).Nonempty at hZne'
    rw [projectiveHyperplaneOpen_eq] at hZne'
    have hd : dimension X ≤ topologicalKrullDim (Z : Set X.toScheme)+1 := by
      change dimension X ≤ topologicalKrullDim
        ((f.hom ⁻¹' (projectiveHyperplaneOpen b l : Set (projectiveSpace k E).toScheme))ᶜ : Set X.toScheme)+1
      rw [projectiveHyperplaneOpen_eq]
      exact dimension_le_hyperplane_add_one X f (dualHomogeneousPolynomial b l)
        (dualHomogeneousPolynomial_degree b l) hZne'
    have hh : (2 : WithBot ℕ∞) ≤ 1 := hdim.trans (hd.trans (by
      rw [←hCdim]
      simpa only [zero_add] using add_le_add_left hzero 1))
    norm_num at hh
  have hinv : ∀ (g : Variety.Point G) (p : Point X),
      p.1 (IsLocalRing.closedPoint k) ∈ Z →
      (A.toMulAction.smul g p).1 (IsLocalRing.closedPoint k) ∈ Z := by
    intro g p hp
    exact projectiveHyperplaneOpen_not_mem_of_map b l (ρ.action g)
      (hlinv' g) (f p) (f (A.toMulAction.smul g p)) (he g p) hp
  let AC := A.onInvariantReducedClosedSubvariety Z hinv
  obtain ⟨D,u₀,v₀,huv₀⟩ := exists_component_distinct_points C.toGeometric hCpos
  let Q := reducedIrreducibleComponent C.toGeometric D
  let AQ := AC.onConnectedGroupComponent hG.isConnected D
  let j := Q.inclusion.comp C.inclusion
  let fj := j.comp f
  have hfj : Function.Injective (fun p : Point Q.toGeometric => fj p) := by
    intro p q hpq
    apply pointMap_injective Q.inclusion
    apply pointMap_injective C.inclusion
    apply pointMap_injective f
    exact hpq
  have hQcomplete : IsComplete Q.toGeometric :=
    reducedClosedSubvariety_isComplete _ (reducedClosedSubvariety_isComplete Z hX)
  have hj (g : Variety.Point G) (p : Point Q.toGeometric) :
      j (AQ.toMulAction.smul g p) = A.toMulAction.smul g (j p) := by
    change C.inclusion (Q.inclusion (AQ.toMulAction.smul g p)) = _
    rw [AC.onConnectedGroupComponent_inclusion hG.isConnected D]
    exact A.onInvariantReducedClosedSubvariety_inclusion Z hinv g _
  have hej (g : Variety.Point G) (p : Point Q.toGeometric) :
      projectiveSpacePointEquivOf b (fj (AQ.toMulAction.smul g p)) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b (fj p)) := by
    change projectiveSpacePointEquivOf b (f (j (AQ.toMulAction.smul g p))) = _
    rw [hj]
    exact he g (j p)
  obtain ⟨u,v,huf,hvf,huv⟩ := AQ.exists_two_fixedPoints_of_torus hG hQcomplete
    (inferInstance : ConnectedSpace Q.toGeometric.toScheme) ρ hρ b fj hej u₀ v₀
      (fun hh => huv₀ (hfj hh))
  have hjfixed (p : Point Q.toGeometric)
      (hp : ∀ g : Variety.Point G, AQ.toMulAction.smul g p = p) (g : Variety.Point G) :
      A.toMulAction.smul g (j p) = j p := by
    rw [←hj,hp]
  have hxj (p : Point Q.toGeometric) : x ≠ j p := by
    have hp : (j p).1 (IsLocalRing.closedPoint k) ∈ Z := by
      change (j p).1 (IsLocalRing.closedPoint k) ∈ (Z : Set X.toScheme)
      rw [←reducedClosedSubvariety_range X Z]
      exact ⟨(Q.inclusion p).1 (IsLocalRing.closedPoint k),rfl⟩
    intro hh
    rw [←hh] at hp
    exact hp hxU
  refine ⟨x,j u,j v,hxfixed,hjfixed u huf,hjfixed v hvf,hxj u,hxj v,?_⟩
  intro hh
  exact huv (congrArg (fun p => f p) hh)


theorem MorphicAction.exists_three_torus_fixedPoints_of_dimension_ge_two
    (A : MorphicAction G X) (T : ClosedSubgroup G) (hT : IsTorus T.carrierVariety)
    (hX : IsComplete X) [IrreducibleSpace X.toScheme] (hdim : 2 ≤ dimension X)
    (ρ : RationalRepresentation G E) (hρ : IsRationalRepresentation ρ)
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (f : Morphism X (projectiveSpace k E)) [IsClosedImmersion f.hom]
    (he : ∀ (t : Variety.Point T.carrierVariety) (x : Point X),
      projectiveSpacePointEquivOf b (f (A.toMulAction.smul (T.includePoint t) x)) =
      Projectivization.map (ρ.action (T.includePoint t)).1
        (ρ.action (T.includePoint t)).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b (f x))) :
    ∃ x y z : Point X,
      (∀ t : Variety.Point T.carrierVariety, A.toMulAction.smul (T.includePoint t) x = x) ∧
      (∀ t : Variety.Point T.carrierVariety, A.toMulAction.smul (T.includePoint t) y = y) ∧
      (∀ t : Variety.Point T.carrierVariety, A.toMulAction.smul (T.includePoint t) z = z) ∧
      x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  obtain ⟨τ,hτ,hτrat⟩ := rationalRepresentation_pullback_exists T.inclusion ρ hρ
  apply (A.pullbackGroup T.inclusion).exists_three_fixedPoints_of_dimension_ge_two
    hT hX hdim τ hτrat b f
  intro t x
  rw [hτ]
  exact he t x

end Theory.AlgebraicGroup.Variety.Geometric
