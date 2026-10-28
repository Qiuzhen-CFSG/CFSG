module

public import Theory.AlgebraicGroup.Borel.AdjointCenter
public import Theory.AlgebraicGroup.Morphism.Connected
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.IsogenyRootDataTransportCore
public import Theory.AlgebraicGroup.Unipotent.Basic
public import Theory.AlgebraicGroup.Unipotent.OneParameter

universe u

/-!
# Root lifting through a central isogeny

For a connected target root subgroup, its closed preimage under a surjective
algebraic-group morphism has an identity component which still maps onto the
target.  If the ambient morphism has finite point kernel and the target is
one-parameter, the restricted identity component has dimension one.  It is
also invariant under every source torus whose image lies in the target torus.

The source lift is also unipotent.  Indeed, after triangularizing the connected
solvable source, the semisimple part of every point lies in the finite isogeny
kernel.  The diagonal image is therefore finite, while connectedness forces it
to be trivial.  Only the final recognition of a connected one-dimensional
unipotent group as an additive one-parameter group uses the converse direction
of GLS3, Proposition 1.3.5(c).
-/

namespace Theory.AlgebraicGroup

set_option linter.style.haveILetI false

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The identity component of the closed preimage of a prospective target root
subgroup. -/
public noncomputable def centralIsogenyRootLift
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (phi : AlgebraicGroup.Morphism G H) (Y : ClosedSubgroup H) :
    ClosedSubgroup G :=
  (phi.closedSubgroupPreimage Y).identityComponentAmbient

/-- The isogeny restricted from the identity-component lift to the target
subgroup. -/
public noncomputable def centralIsogenyRootLiftMorphism
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (phi : AlgebraicGroup.Morphism G H) (Y : ClosedSubgroup H) :
    AlgebraicGroup.Morphism (centralIsogenyRootLift phi Y).carrierVariety
      Y.carrierVariety := by
  let P := phi.closedSubgroupPreimage Y
  let X := centralIsogenyRootLift phi Y
  let q : AlgebraicGroup.Morphism X.carrierVariety H :=
    phi.comp X.inclusion
  exact q.codRestrictClosedSubgroup Y fun x => by
    exact P.identityComponentAmbient_le (X.pointEquiv x).property

private theorem centralIsogenyRootLiftMorphism_inclusion_apply
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (phi : AlgebraicGroup.Morphism G H) (Y : ClosedSubgroup H)
    (x : Variety.Point (centralIsogenyRootLift phi Y).carrierVariety) :
    Y.inclusion.onPoints (centralIsogenyRootLiftMorphism phi Y |>.onPoints x) =
      phi.onPoints ((centralIsogenyRootLift phi Y).inclusion.onPoints x) := by
  unfold centralIsogenyRootLiftMorphism
  change (Y.pointEquiv (Y.pointEquiv.symm ⟨_, _⟩)).val = _
  rw [Y.pointEquiv.apply_symm_apply]
  rfl

omit [IsAlgClosed k] in
private lemma closedSubgroup_isConnected_of_carrier
    {G : Variety k} [AlgebraicGroup G] (X : ClosedSubgroup G)
    (hX : Variety.IsConnected X.carrierVariety) :
    _root_.IsConnected (X : Set (Variety.Point G)) := by
  let e := Variety.closedSubvarietyPointHomeomorph X.isZariskiClosed
  let : ConnectedSpace (Variety.Point X.carrierVariety) :=
    connectedSpace_iff_univ.mpr hX
  let : ConnectedSpace {x : Variety.Point G // x ∈ (X : Set (Variety.Point G))} :=
    e.connectedSpace_iff.mp inferInstance
  exact isConnected_iff_connectedSpace.mpr inferInstance

omit [IsAlgClosed k] in
private lemma closedSubgroup_carrier_isConnected
    {G : Variety k} [AlgebraicGroup G] (X : ClosedSubgroup G)
    (hX : _root_.IsConnected (X : Set (Variety.Point G))) :
    Variety.IsConnected X.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph X.isZariskiClosed
  let : ConnectedSpace
      {x : Variety.Point G // x ∈ (X : Set (Variety.Point G))} :=
    Subtype.connectedSpace hX
  let : ConnectedSpace (Variety.Point X.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

private theorem isogeny_source_unipotent
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (phi : AlgebraicGroup.Morphism G H) (hphi : IsIsogeny phi)
    (hG : Variety.IsConnected G)
    (hH : IsUnipotentAlgebraicGroup H) :
    IsUnipotentAlgebraicGroup G := by
  have hkernelComm (a b : phi.kernel) : a * b = b * a := by
    have haCenter :=
      isogeny_kernel_le_center_of_connected phi hphi hG a.1 a.2
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp haCenter b.1).symm
  let _ : Group.IsSolvable phi.kernel :=
    Group.isSolvable_of_comm hkernelComm
  let _ : Group.IsSolvable (Variety.Point H) :=
    isSolvable_of_isUnipotentAlgebraicGroup hH
  have hGsolvable : Group.IsSolvable (Variety.Point G) :=
    Group.isSolvable_of_ker_le_range phi.kernel.subtype phi.onPoints (by
      intro x hx
      exact ⟨⟨x, hx⟩, rfl⟩)
  obtain ⟨n, hn, S, ⟨e⟩⟩ :=
    exists_iso_closedSubgroup_tVariety_of_isSolvable_isConnected
      hGsolvable hG
  letI : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
  let P : TriangularPresentation G :=
    { n := n, positive := hn, subgroup := S, iso := e }
  let D := P.diagonalImage
  letI : AlgebraicGroup D.carrierVariety := D.carrierAlgebraicGroup
  let delta : AlgebraicGroup.Morphism G D.carrierVariety :=
    P.diagonalImageMorphism
  have hDsemisimple (z : Variety.Point D.carrierVariety) :
      IsSemisimpleElement D.carrierVariety z := by
    exact (closedSubgroup_semisimpleElement_iff D
      (D.pointEquiv z).property).mp
        (dVariety_all_semisimple P.n (D.inclusion.onPoints z))
  have hdeltaInclusion (x : Variety.Point G) :
      D.inclusion.onPoints (delta.onPoints x) =
        P.diagonalMorphism.onPoints x := by
    simpa only [delta, TriangularPresentation.diagonalImageMorphism] using
      (AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply
        P.diagonalMorphism D (fun z => by
          change P.diagonalMorphism.onPoints z ∈ P.diagonalMorphism.image
          exact ⟨z, rfl⟩) x)
  have hdeltaSurjective : Function.Surjective delta.onPoints := by
    intro y
    have hy := (D.pointEquiv y).property
    change D.inclusion.onPoints y ∈ P.diagonalMorphism.image at hy
    rcases hy with ⟨x, hx⟩
    refine ⟨x, D.inclusion_injective ?_⟩
    exact (hdeltaInclusion x).trans hx
  let qmap : phi.kernel →* Variety.Point D.carrierVariety :=
    delta.onPoints.comp phi.kernel.subtype
  have hqmapSurjective : Function.Surjective qmap := by
    intro y
    obtain ⟨x, rfl⟩ := hdeltaSurjective y
    let d := jordanDecomposition x
    have hsKernel : d.semisimplePart ∈ phi.kernel := by
      change phi.onPoints d.semisimplePart = 1
      exact semisimple_unipotent_eq_one
        (phi.onPoints d.semisimplePart)
        (morphism_preserves_semisimpleElement phi _ d.semisimple)
        (hH (phi.onPoints d.semisimplePart))
    let s : phi.kernel := ⟨d.semisimplePart, hsKernel⟩
    refine ⟨s, ?_⟩
    have huOne : delta.onPoints d.unipotentPart = 1 :=
      semisimple_unipotent_eq_one
        (delta.onPoints d.unipotentPart)
        (hDsemisimple (delta.onPoints d.unipotentPart))
        (morphism_preserves_unipotentElement delta _ d.unipotent)
    have hdeltaDecomposition :
        delta.onPoints x =
          delta.onPoints d.semisimplePart * delta.onPoints d.unipotentPart := by
      rw [← map_mul, ← d.eq_mul]
    rw [huOne, mul_one] at hdeltaDecomposition
    exact hdeltaDecomposition.symm
  let _ : Finite phi.kernel := hphi.2
  let _ : Finite (Variety.Point D.carrierVariety) :=
    Finite.of_surjective qmap hqmapSurjective
  have hdeltaFinite : (Set.range delta.onPoints).Finite := Set.toFinite _
  have hdeltaSubsingleton :=
    connected_finite_morphism_range_subsingleton
      delta.toVariety hG hdeltaFinite
  intro x
  apply (P.mem_unipotentRadical_iff_characteristicFree x).mp
  change P.diagonalMorphism.onPoints x = 1
  have hdeltaOne := hdeltaSubsingleton
    (Set.mem_range_self x) (Set.mem_range_self (1 : Variety.Point G))
  have hdeltaOneAmbient := congrArg D.inclusion.onPoints hdeltaOne
  change D.inclusion.onPoints (delta.onPoints x) =
    D.inclusion.onPoints (delta.onPoints 1) at hdeltaOneAmbient
  rw [hdeltaInclusion, hdeltaInclusion, map_one] at hdeltaOneAmbient
  exact hdeltaOneAmbient

/-- The lifted subgroup is connected by construction. -/
public theorem centralIsogenyRootLift_isConnected
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (phi : AlgebraicGroup.Morphism G H) (Y : ClosedSubgroup H) :
    _root_.IsConnected
      (centralIsogenyRootLift phi Y : Set (Variety.Point G)) :=
  (phi.closedSubgroupPreimage Y).identityComponentAmbient_isConnected

/-- The identity-component lift still has the whole connected target subgroup
as its closed image. -/
public theorem centralIsogenyRootLift_image_eq
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (phi : AlgebraicGroup.Morphism G H)
    (hphi : Function.Surjective phi.onPoints)
    (Y : ClosedSubgroup H) (hY : IsOneParameterGroup Y.carrierVariety) :
    (phi.comp (centralIsogenyRootLift phi Y).inclusion).imageClosedSubgroup = Y := by
  apply phi.closedSubgroupPreimage_identityComponent_image_eq hphi Y
  exact closedSubgroup_isConnected_of_carrier Y hY.isConnected

/-- The restricted lift morphism is point-surjective. -/
public theorem centralIsogenyRootLiftMorphism_surjective
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (phi : AlgebraicGroup.Morphism G H)
    (hphi : Function.Surjective phi.onPoints)
    (Y : ClosedSubgroup H) (hY : IsOneParameterGroup Y.carrierVariety) :
    Function.Surjective (centralIsogenyRootLiftMorphism phi Y).onPoints := by
  let X := centralIsogenyRootLift phi Y
  let q : AlgebraicGroup.Morphism X.carrierVariety H :=
    phi.comp X.inclusion
  have himage : q.imageClosedSubgroup = Y :=
    centralIsogenyRootLift_image_eq phi hphi Y hY
  intro y
  have hy : Y.inclusion.onPoints y ∈
      (q.imageClosedSubgroup : Set (Variety.Point H)) := by
    rw [himage]
    exact (Y.pointEquiv y).property
  change Y.inclusion.onPoints y ∈ q.image at hy
  rcases hy with ⟨x, hx⟩
  refine ⟨x, Y.inclusion_injective ?_⟩
  exact (centralIsogenyRootLiftMorphism_inclusion_apply phi Y x).trans hx

/-- The restricted lift morphism has finite point kernel. -/
public theorem centralIsogenyRootLiftMorphism_kernel_finite
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (phi : AlgebraicGroup.Morphism G H) (hphi : Finite phi.kernel)
    (Y : ClosedSubgroup H) :
    Finite (centralIsogenyRootLiftMorphism phi Y).kernel := by
  let X := centralIsogenyRootLift phi Y
  let q := centralIsogenyRootLiftMorphism phi Y
  let embed : q.kernel → phi.kernel := fun z =>
    ⟨X.inclusion.onPoints z.1, by
      have hz := z.2
      change q.onPoints z.1 = 1 at hz
      have hzAmbient := congrArg Y.inclusion.onPoints hz
      change Y.inclusion.onPoints
          ((centralIsogenyRootLiftMorphism phi Y).onPoints z.1) =
        Y.inclusion.onPoints 1 at hzAmbient
      rw [centralIsogenyRootLiftMorphism_inclusion_apply, map_one]
        at hzAmbient
      exact hzAmbient⟩
  let _ : Finite phi.kernel := hphi
  exact Finite.of_injective embed (by
    intro x y hxy
    apply Subtype.ext
    apply X.inclusion_injective
    exact congrArg (fun z : phi.kernel => z.1) hxy)

/-- Restricting an isogeny to the identity-component root lift is again an
isogeny onto the target one-parameter subgroup. -/
public theorem centralIsogenyRootLiftMorphism_isIsogeny
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (phi : AlgebraicGroup.Morphism G H) (hphi : IsIsogeny phi)
    (Y : ClosedSubgroup H) (hY : IsOneParameterGroup Y.carrierVariety) :
    IsIsogeny (centralIsogenyRootLiftMorphism phi Y) :=
  ⟨centralIsogenyRootLiftMorphism_surjective phi hphi.1 Y hY,
    centralIsogenyRootLiftMorphism_kernel_finite phi hphi.2 Y⟩

/-- A finite-kernel lift of a one-parameter target has dimension one. -/
public theorem centralIsogenyRootLift_dimension_eq_one
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (phi : AlgebraicGroup.Morphism G H) (hphi : IsIsogeny phi)
    (Y : ClosedSubgroup H) (hY : IsOneParameterGroup Y.carrierVariety) :
    Variety.dimension (centralIsogenyRootLift phi Y).carrierVariety = 1 := by
  let X := centralIsogenyRootLift phi Y
  let q := phi.comp X.inclusion
  let embed : q.kernel → phi.kernel := fun z =>
    ⟨X.inclusion.onPoints z.1, by
      change phi.onPoints (X.inclusion.onPoints z.1) = 1
      exact MonoidHom.mem_ker.mp z.2⟩
  have hembed : Function.Injective embed := by
    intro x y hxy
    apply Subtype.ext
    apply X.inclusion_injective
    exact congrArg (fun z : phi.kernel => z.1) hxy
  let _ : Finite phi.kernel := hphi.2
  have hqfinite : Finite q.kernel := Finite.of_injective embed hembed
  have hqkernelPoints :
      Finite (Variety.Point q.kernelClosedSubgroup.carrierVariety) := by
    apply (Equiv.finite_iff q.kernelClosedSubgroup.pointEquiv).mpr
    change Finite q.kernel
    exact hqfinite
  have hqkernelDimension :
      Variety.dimension q.kernelClosedSubgroup.carrierVariety = 0 :=
    (dimension_zero_iff_finite_points q.kernelClosedSubgroup.carrierVariety).2
      hqkernelPoints
  have himage : q.imageClosedSubgroup = Y := by
    exact centralIsogenyRootLift_image_eq phi hphi.1 Y hY
  have hdimension := morphism_dimension_eq_kernel_add_image q
  rw [hqkernelDimension, himage, zero_add] at hdimension
  exact hdimension.trans hY.dimension_eq_one

/-- The connected lift of a target one-parameter subgroup through an isogeny
is unipotent. -/
public theorem centralIsogenyRootLift_isUnipotent
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (phi : AlgebraicGroup.Morphism G H) (hphi : IsIsogeny phi)
    (Y : ClosedSubgroup H) (hY : IsOneParameterGroup Y.carrierVariety) :
    IsUnipotentAlgebraicGroup
      (centralIsogenyRootLift phi Y).carrierVariety := by
  let X := centralIsogenyRootLift phi Y
  exact isogeny_source_unipotent
    (centralIsogenyRootLiftMorphism phi Y)
    (centralIsogenyRootLiftMorphism_isIsogeny phi hphi Y hY)
    (closedSubgroup_carrier_isConnected X
      (centralIsogenyRootLift_isConnected phi Y))
    hY.isUnipotentAlgebraicGroup

/-- The connected lift of a one-parameter subgroup is again one-parameter.

The preceding lemmas establish the three geometric conditions in the converse
direction of GLS3, Proposition 1.3.5(c): connectedness, dimension one, and
unipotence.  Applying that recognition theorem supplies the additive
parametrization needed by root-data transport.
-/
public theorem centralIsogenyRootLift_isOneParameter
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (phi : AlgebraicGroup.Morphism G H) (hphi : IsIsogeny phi)
    (Y : ClosedSubgroup H) (hY : IsOneParameterGroup Y.carrierVariety) :
    IsOneParameterGroup
      (centralIsogenyRootLift phi Y).carrierVariety := by
  let X := centralIsogenyRootLift phi Y
  apply (theorem_1_3_5_c (Y := X.carrierVariety)).2
  refine ⟨?_, centralIsogenyRootLift_dimension_eq_one phi hphi Y hY,
    centralIsogenyRootLift_isUnipotent phi hphi Y hY⟩
  exact closedSubgroup_carrier_isConnected X
    (centralIsogenyRootLift_isConnected phi Y)

/-- A chosen additive parametrization of the connected lift.

This noncomputable selector is a convenience for consumers that need an
explicit `OneParameterParametrization` rather than its existential wrapper.
-/
public noncomputable def centralIsogenyRootLift_oneParameterParametrization
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (phi : AlgebraicGroup.Morphism G H) (hphi : IsIsogeny phi)
    (Y : ClosedSubgroup H) (hY : IsOneParameterGroup Y.carrierVariety) :
    OneParameterParametrization
      (centralIsogenyRootLift phi Y).carrierVariety :=
  Classical.choice (centralIsogenyRootLift_isOneParameter phi hphi Y hY)

/-- Package the lifted subgroup as a scaling-aware image witness once source
and target additive coordinates have been chosen. -/
public noncomputable def centralIsogenyRootLift_imageWitness
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (phi : AlgebraicGroup.Morphism G H) (hphi : IsIsogeny phi)
    (Y : ClosedSubgroup H) (hY : IsOneParameterGroup Y.carrierVariety)
    (source : OneParameterParametrization
      (centralIsogenyRootLift phi Y).carrierVariety)
    (target : OneParameterParametrization Y.carrierVariety) :
    IsogenyRootImageWitness phi (centralIsogenyRootLift phi Y) Y :=
  IsogenyRootImageWitness.of_surjective
    phi (centralIsogenyRootLift phi Y) Y
    (centralIsogenyRootLift_image_eq phi hphi.1 Y hY)
    source target
    (centralIsogenyRootLiftMorphism phi Y)
    (centralIsogenyRootLiftMorphism_inclusion_apply phi Y)
    (centralIsogenyRootLiftMorphism_surjective phi hphi.1 Y hY)

omit [IsAlgClosed k] in
private lemma closedSubgroup_conjugate_isConnected
    {G : Variety k} [AlgebraicGroup G] (X : ClosedSubgroup G)
    (g : Variety.Point G)
    (hX : _root_.IsConnected (X : Set (Variety.Point G))) :
    _root_.IsConnected (X.conjugate g : Set (Variety.Point G)) := by
  apply closedSubgroup_isConnected_of_carrier
  exact (algebraicGroupIso_isConnected_iff (X.conjugateIso g)).mp
    (closedSubgroup_carrier_isConnected X hX)

/-- The lift is invariant under a source torus whenever the ambient morphism
sends that torus into a target torus which normalizes the target subgroup. -/
public theorem centralIsogenyRootLift_invariant
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (phi : AlgebraicGroup.Morphism G H)
    (T : ClosedSubgroup G) (T' : ClosedSubgroup H)
    (Y : ClosedSubgroup H) (hY : IsClosedSubgroupInvariant T' Y)
    (hTmap : ∀ t, t ∈ T → phi.onPoints t ∈ T') :
    IsClosedSubgroupInvariant T (centralIsogenyRootLift phi Y) := by
  let P := phi.closedSubgroupPreimage Y
  let X := centralIsogenyRootLift phi Y
  intro t ht x hx
  change x ∈ X.toSubgroup at hx
  have hconjConnected : _root_.IsConnected
      (X.conjugate t⁻¹ : Set (Variety.Point G)) :=
    closedSubgroup_conjugate_isConnected X t⁻¹
      (centralIsogenyRootLift_isConnected phi Y)
  have hconjP : X.conjugate t⁻¹ ≤ P := by
    intro z hz
    have htz : t * z * t⁻¹ ∈ X.toSubgroup := by
      simpa only [inv_inv] using (X.mem_conjugate_iff t⁻¹ z).mp hz
    have htzP : t * z * t⁻¹ ∈ P :=
      P.identityComponentAmbient_le htz
    change phi.onPoints z ∈ Y
    have hphiConj :
        phi.onPoints (t * z * t⁻¹) =
          phi.onPoints t * phi.onPoints z * (phi.onPoints t)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    have himage : phi.onPoints (t * z * t⁻¹) ∈ Y := htzP
    have hback := hY (phi.onPoints t) (hTmap t ht)
      (phi.onPoints (t * z * t⁻¹)) himage
    rw [hphiConj] at hback
    simpa [mul_assoc] using hback
  have hconjX : X.conjugate t⁻¹ ≤ X := by
    exact connected_closedSubgroup_le_identityComponentAmbient
      (X.conjugate t⁻¹) P hconjConnected hconjP
  apply hconjX
  change t⁻¹ * x * t ∈ (X.conjugate t⁻¹).toSubgroup
  apply (X.mem_conjugate_iff t⁻¹ (t⁻¹ * x * t)).mpr
  simpa [mul_assoc] using hx

end Theory.AlgebraicGroup
