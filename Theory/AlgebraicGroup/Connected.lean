module

public import Mathlib.Topology.Separation.Connected
public import Theory.AlgebraicGroup.ClosedSubgroup.Basic
public import Theory.AlgebraicGroup.Isomorphism
public import Theory.AlgebraicGroup.Morphism.Operations

universe u

/-!
Connectedness and the identity component of an algebraic group.
-/

namespace Theory.AlgebraicGroup

open scoped TensorProduct
open scoped commutatorElement

open LinearMap Submodule

variable {k : Type u} [Field k]

@[expose]
public def Variety.IsConnected (V : Variety k) : Prop :=
  _root_.IsConnected (Set.univ : Set (Variety.Point V))

/-- A finite morphism image of a connected affine variety is a singleton. -/
public lemma connected_finite_morphism_range_subsingleton
    {K H : Variety k} (f : Variety.Morphism K H)
    (hK : Variety.IsConnected K)
    (hfinite : (Set.range f.toFun).Finite) :
    (Set.range f.toFun).Subsingleton := by
  have hrangeConnected : _root_.IsConnected (Set.range f.toFun) := by
    simpa only [Set.image_univ] using
      hK.image f.toFun f.continuous.continuousOn
  let : T1Space (Variety.Point H) :=
    ⟨fun y ↦ Variety.isClosed_iff_isZariskiClosed.mpr
      (isZariskiClosed_singleton H y)⟩
  rw [← Set.not_nontrivial_iff]
  intro hnontrivial
  exact hfinite.not_infinite
    (hrangeConnected.isPreconnected.infinite_of_nontrivial hnontrivial)

/-- A morphism from a connected algebraic group to a commutative algebraic
group with finite kernel has commutative source. -/
public lemma connected_isMulCommutative_of_finiteKernel
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (hG : Variety.IsConnected G)
    (hker : Finite f.kernel)
    (hH : IsMulCommutative (Variety.Point H)) :
    IsMulCommutative (Variety.Point G) := by
  rw [isMulCommutative_iff] at hH ⊢
  intro x y
  let c : Variety.Morphism G G :=
    (AlgebraicGroup.rightMulMorphism G x⁻¹).comp
      (AlgebraicGroup.conjugateMorphism G x)
  have hcapply (z : Variety.Point G) :
      c.toFun z = z * x * z⁻¹ * x⁻¹ := by
    simp [c, Variety.Morphism.comp,
      AlgebraicGroup.rightMulMorphism_apply,
      AlgebraicGroup.conjugateMorphism_apply]
  have hcrange : Set.range c.toFun ⊆
      (f.kernel : Set (Variety.Point G)) := by
    rintro w ⟨z, rfl⟩
    rw [hcapply]
    change f.onPoints (z * x * z⁻¹ * x⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv,
      hH (f.onPoints z) (f.onPoints x)]
    simp
  let : Finite f.kernel := hker
  have hcfinite : (Set.range c.toFun).Finite :=
    (Set.toFinite (f.kernel : Set (Variety.Point G))).subset hcrange
  have hcsub := connected_finite_morphism_range_subsingleton c hG hcfinite
  have heq := hcsub (Set.mem_range_self y)
    (Set.mem_range_self (1 : Variety.Point G))
  rw [hcapply, hcapply] at heq
  simp only [one_mul, inv_one, mul_one, mul_inv_cancel] at heq
  exact (commutatorElement_eq_one_iff_mul_comm.mp (by
    simpa [commutatorElement_def] using heq)).symm

/-- Isomorphic affine algebraic groups are connected simultaneously. -/
public lemma algebraicGroupIso_isConnected_iff
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (e : AlgebraicGroup.Iso G H) :
    Variety.IsConnected G ↔ Variety.IsConnected H := by
  let eTop : Variety.Point G ≃ₜ Variety.Point H :=
    { toFun := e.hom.onPoints
      invFun := e.inv.onPoints
      left_inv := e.hom_inv_id
      right_inv := e.inv_hom_id
      continuous_toFun := e.hom.toVariety.continuous
      continuous_invFun := e.inv.toVariety.continuous }
  constructor
  · intro hG
    let : ConnectedSpace (Variety.Point G) :=
      connectedSpace_iff_univ.mpr hG
    let : ConnectedSpace (Variety.Point H) :=
      eTop.connectedSpace_iff.mp inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  · intro hH
    let : ConnectedSpace (Variety.Point H) :=
      connectedSpace_iff_univ.mpr hH
    let : ConnectedSpace (Variety.Point G) :=
      eTop.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance

/-- Definition 1.1.3: the identity component is the connected component of the
identity point in the Zariski topology. -/
@[expose]
public def identityComponent (G : Variety k)
    [AlgebraicGroup G] : Set (Variety.Point G) :=
  connectedComponent (1 : Variety.Point G)

public theorem one_mem_identityComponent (G : Variety k)
    [AlgebraicGroup G] :
    (1 : Variety.Point G) ∈ Theory.AlgebraicGroup.identityComponent G := by
  exact mem_connectedComponent

public theorem identityComponent_isClosed (G : Variety k)
    [AlgebraicGroup G] :
    IsZariskiClosed G (Theory.AlgebraicGroup.identityComponent G) := by
  rw [← Variety.isClosed_iff_isZariskiClosed]
  exact isClosed_connectedComponent

public theorem identityComponent_isConnected (G : Variety k)
    [AlgebraicGroup G] :
    _root_.IsConnected (Theory.AlgebraicGroup.identityComponent G) := by
  exact isConnected_connectedComponent

public theorem identityComponent_mul_mem (G : Variety k)
    [AlgebraicGroup G] {g h : Variety.Point G}
    (hg : g ∈ Theory.AlgebraicGroup.identityComponent G)
    (hh : h ∈ Theory.AlgebraicGroup.identityComponent G) :
    g * h ∈ Theory.AlgebraicGroup.identityComponent G := by
  change g * h ∈ connectedComponent (1 : Variety.Point G)
  rw [connectedComponent_eq hg]
  have hmul : g ∈ connectedComponent (g * h) := by
    apply Continuous.image_connectedComponent_subset
      (Theory.AlgebraicGroup.leftMulMorphism G g).continuous h
    rw [← connectedComponent_eq hh]
    exact ⟨(1 : Variety.Point G), mem_connectedComponent, by
      simp [Theory.AlgebraicGroup.leftMulMorphism_apply]⟩
  simpa [← connectedComponent_eq hmul] using mem_connectedComponent

public theorem identityComponent_inv_mem (G : Variety k)
    [AlgebraicGroup G] {g : Variety.Point G}
    (hg : g ∈ Theory.AlgebraicGroup.identityComponent G) :
    g⁻¹ ∈ Theory.AlgebraicGroup.identityComponent G := by
  change g⁻¹ ∈ connectedComponent (1 : Variety.Point G)
  rw [← inv_one]
  exact
    Continuous.image_connectedComponent_subset
      (Theory.AlgebraicGroup.invMorphism G).continuous _
      ((Set.mem_image _ _ _).mp ⟨g, hg, rfl⟩)

/-- The identity component is an actual subgroup of the underlying algebraic
group.  Its carrier is the connected component of the identity in the
Zariski topology; no subgroup law is stored as an assumption. -/
@[expose]
public def identityComponentSubgroup (G : Variety k)
    [AlgebraicGroup G] : Subgroup (Variety.Point G) where
  carrier := Theory.AlgebraicGroup.identityComponent G
  one_mem' := Theory.AlgebraicGroup.one_mem_identityComponent G
  mul_mem' := Theory.AlgebraicGroup.identityComponent_mul_mem G
  inv_mem' := Theory.AlgebraicGroup.identityComponent_inv_mem G

public theorem identityComponentSubgroup_carrier
    (G : Variety k) [AlgebraicGroup G] :
    (Theory.AlgebraicGroup.identityComponentSubgroup G : Set (Variety.Point G)) =
      Theory.AlgebraicGroup.identityComponent G := rfl

/-- The identity component as a genuine closed algebraic subgroup object. -/
@[expose]
public def identityComponentClosedSubgroup
    (G : Variety k) [AlgebraicGroup G] : ClosedSubgroup G :=
  ClosedSubgroup.ofSubgroup (Theory.AlgebraicGroup.identityComponentSubgroup G)
    (Theory.AlgebraicGroup.identityComponent_isClosed G)

public theorem identityComponentClosedSubgroup_carrier
    (G : Variety k) [AlgebraicGroup G] :
    (Theory.AlgebraicGroup.identityComponentClosedSubgroup G).toSubgroup =
      Theory.AlgebraicGroup.identityComponentSubgroup G := rfl

public theorem conjugation_mem_identityComponent
    (G : Variety k) [AlgebraicGroup G]
    (g : Variety.Point G) {x : Variety.Point G}
    (hx : x ∈ Theory.AlgebraicGroup.identityComponent G) :
    g * x * g⁻¹ ∈ Theory.AlgebraicGroup.identityComponent G := by
  have himage :=
    (Theory.AlgebraicGroup.conjugationByMorphism G g).continuous
      |>.image_connectedComponent_subset (1 : Variety.Point G)
  have hxImage :
      (Theory.AlgebraicGroup.conjugationByMorphism G g).toFun x ∈
        (Theory.AlgebraicGroup.conjugationByMorphism G g).toFun ''
          connectedComponent (1 : Variety.Point G) :=
    ⟨x, hx, rfl⟩
  have := himage hxImage
  simpa [Theory.AlgebraicGroup.conjugationByMorphism_apply,
    Theory.AlgebraicGroup.identityComponent] using this

public theorem identityComponentClosedSubgroup_isNormal
    (G : Variety k) [AlgebraicGroup G] :
    (Theory.AlgebraicGroup.identityComponentClosedSubgroup G).toSubgroup.Normal := by
  rw [Theory.AlgebraicGroup.identityComponentClosedSubgroup_carrier]
  constructor
  intro n hn g
  exact Theory.AlgebraicGroup.conjugation_mem_identityComponent G g hn

/-- Proposition 1.1.4(b): the identity component is connected, and it is the
whole group exactly when the underlying Zariski zero locus is connected. -/
public theorem identityComponent_eq_univ_iff_isConnected
    (G : Variety k) [AlgebraicGroup G] :
    Theory.AlgebraicGroup.identityComponent G = Set.univ ↔ Variety.IsConnected G := by
  constructor
  · intro hcomponent
    change _root_.IsConnected (Set.univ : Set (Variety.Point G))
    rw [← hcomponent]
    exact Theory.AlgebraicGroup.identityComponent_isConnected G
  · intro hconnected
    change _root_.IsConnected (Set.univ : Set (Variety.Point G)) at hconnected
    apply Set.eq_univ_of_univ_subset
    exact hconnected.subset_connectedComponent (Set.mem_univ 1)

/-- The always-valid inclusion in Proposition 1.1.4(c): a morphism sends the
identity component into the identity component of the target.  Equality with
the identity component of the image additionally uses the closed-image theorem. -/
public theorem Morphism.image_identityComponent_subset
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : Theory.AlgebraicGroup.Morphism G H) :
    f.onPoints '' Theory.AlgebraicGroup.identityComponent G ⊆
      Theory.AlgebraicGroup.identityComponent H := by
  have hsubset := f.toVariety.continuous.image_connectedComponent_subset
    (1 : Variety.Point G)
  rw [f.map_one] at hsubset
  simpa [Theory.AlgebraicGroup.Morphism.onPoints,
    Theory.AlgebraicGroup.identityComponent] using hsubset

public theorem Morphism.map_identityComponentSubgroup
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : Theory.AlgebraicGroup.Morphism G H) :
    (Theory.AlgebraicGroup.identityComponentSubgroup G).map f.onPoints ≤
      Theory.AlgebraicGroup.identityComponentSubgroup H := by
  rintro _ ⟨x, hx, rfl⟩
  exact f.image_identityComponent_subset
    ⟨x, (show x ∈ Theory.AlgebraicGroup.identityComponent G from hx), rfl⟩

/- Equality in Proposition 1.1.4(c) for an algebraic-group isomorphism. -/
public theorem Iso.image_identityComponent_eq
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (e : Theory.AlgebraicGroup.Iso G H) :
    e.hom.onPoints '' Theory.AlgebraicGroup.identityComponent G =
      Theory.AlgebraicGroup.identityComponent H := by
  apply Set.Subset.antisymm
  · exact e.hom.image_identityComponent_subset
  · intro y hy
    have hy' : e.inv.onPoints y ∈ Theory.AlgebraicGroup.identityComponent G := by
      exact e.inv.image_identityComponent_subset ⟨y, hy, rfl⟩
    exact ⟨e.inv.onPoints y, hy', e.inv_hom_id y⟩

/-- Proposition 1.1.4(d), at the level available before the subgroup theorem:
the identity component of a closed subgroup maps into that of the ambient
group under the canonical inclusion. -/
public theorem closedSubgroup_inclusion_identityComponent_subset {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G) :
    H.inclusion.onPoints '' Theory.AlgebraicGroup.identityComponent H.carrierVariety ⊆
      Theory.AlgebraicGroup.identityComponent G := by
  exact H.inclusion.image_identityComponent_subset

/- The subgroup form of 1.1.4(d), now that the identity component has been
constructed as a genuine subgroup rather than merely a set. -/
public theorem closedSubgroup_identityComponent_map {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G) :
    (Theory.AlgebraicGroup.identityComponentSubgroup H.carrierVariety).map
        H.inclusion.onPoints ≤ Theory.AlgebraicGroup.identityComponentSubgroup G := by
  rintro _ ⟨x, hx, rfl⟩
  exact H.inclusion.image_identityComponent_subset
    ⟨x, (show x ∈ Theory.AlgebraicGroup.identityComponent H.carrierVariety from hx), rfl⟩

/-- The order on closed subgroups is the inclusion order of the underlying
subgroups. -/
public theorem ClosedSubgroup.le_iff_le_toSubgroup {G : Variety k} [AlgebraicGroup G]
    (B C : ClosedSubgroup G) :
    B ≤ C ↔ B.toSubgroup ≤ C.toSubgroup := by
  rfl

/-- A connected closed subgroup is contained in the identity component
(Proposition 1.1.4(d) refines: a connected subgroup of `G` lies in `G°`). -/
public theorem connected_closedSubgroup_subset_identityComponent
    (G : Variety k) [AlgebraicGroup G] {H : ClosedSubgroup G}
    (hH : _root_.IsConnected (H : Set (Variety.Point G))) :
    (H.toSubgroup : Set (Variety.Point G)) ⊆
      Theory.AlgebraicGroup.identityComponent G := by
  intro x hx
  have hsub : (H : Set (Variety.Point G)) ⊆
      connectedComponent (1 : Variety.Point G) :=
    hH.subset_connectedComponent (H.toSubgroup.one_mem)
  exact hsub hx

public instance pointSeparatelyContinuousMul
    (G : Variety k) [AlgebraicGroup G] :
    SeparatelyContinuousMul (Variety.Point G) where
  continuous_const_mul := by
    intro a
    have heq : (fun x : Variety.Point G => a * x) =
        (Theory.AlgebraicGroup.leftMulMorphism G a).toFun := by
      funext x
      symm
      exact Theory.AlgebraicGroup.leftMulMorphism_apply G a x
    rw [heq]
    exact Variety.Morphism.continuous (Theory.AlgebraicGroup.leftMulMorphism G a)
  continuous_mul_const := by
    intro a
    have heq : (fun x : Variety.Point G => x * a) =
        (Theory.AlgebraicGroup.rightMulMorphism G a).toFun := by
      funext x
      symm
      exact Theory.AlgebraicGroup.rightMulMorphism_apply G a x
    rw [heq]
    exact Variety.Morphism.continuous (Theory.AlgebraicGroup.rightMulMorphism G a)

/- The finite-index minimality implication in Proposition 1.1.4(a). -/
public theorem identityComponent_subset_of_finiteIndexSubgroup
    (G : Variety k) [AlgebraicGroup G] (K : ClosedSubgroup G)
    [K.toSubgroup.FiniteIndex] :
    Theory.AlgebraicGroup.identityComponent G ⊆
      (K.toSubgroup : Set (Variety.Point G)) := by
  have hclosed : IsClosed (K.toSubgroup : Set (Variety.Point G)) :=
    Variety.isClosed_iff_isZariskiClosed.mpr K.isZariskiClosed
  have hopen : IsOpen (K.toSubgroup : Set (Variety.Point G)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex K.toSubgroup hclosed
  exact IsClopen.connectedComponent_subset
    ⟨hclosed, hopen⟩ K.toSubgroup.one_mem

/-- In a Noetherian space there are finitely many connected components: each
connected component contains an irreducible component, and distinct connected
components contain distinct irreducible components. -/
public theorem finite_connectedComponents_of_noetherian {X : Type*}
    [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] :
    Finite {C : Set X // C ∈ Set.range (connectedComponent : X → Set X)} := by
  let : Finite (irreducibleComponents X) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  let f : {C : Set X // C ∈ Set.range (connectedComponent : X → Set X)} →
      {u : Set X // u ∈ irreducibleComponents X} := fun C =>
    ⟨irreducibleComponent (Classical.choose (Set.mem_range.mp C.2)),
      irreducibleComponent_mem_irreducibleComponents (x := Classical.choose (Set.mem_range.mp C.2))⟩
  refine Finite.of_injective f ?_
  intro C D hEq
  apply Subtype.ext
  let xC := Classical.choose (Set.mem_range.mp C.2)
  let xD := Classical.choose (Set.mem_range.mp D.2)
  have hC : connectedComponent xC = C.1 := Classical.choose_spec (Set.mem_range.mp C.2)
  have hD : connectedComponent xD = D.1 := Classical.choose_spec (Set.mem_range.mp D.2)
  have huC : irreducibleComponent xC ⊆ C.1 := by
    calc
      irreducibleComponent xC ⊆ connectedComponent xC :=
        (isIrreducible_irreducibleComponent.isConnected).subset_connectedComponent mem_irreducibleComponent
      _ = C.1 := hC
  have huD : irreducibleComponent xD ⊆ D.1 := by
    calc
      irreducibleComponent xD ⊆ connectedComponent xD :=
        (isIrreducible_irreducibleComponent.isConnected).subset_connectedComponent mem_irreducibleComponent
      _ = D.1 := hD
  have hne : (irreducibleComponent xC : Set X).Nonempty :=
    ⟨xC, mem_irreducibleComponent⟩
  rcases hne with ⟨z, hz⟩
  have hzC : z ∈ connectedComponent xC := by
    rw [hC]
    exact huC hz
  have hzD : z ∈ connectedComponent xD := by
    have : z ∈ (f C : Set X) := hz
    rw [hEq] at this
    rw [hD]
    exact huD this
  have hCz : connectedComponent xC = connectedComponent z := connectedComponent_eq hzC
  have hDz : connectedComponent xD = connectedComponent z := connectedComponent_eq hzD
  calc
    C.1 = connectedComponent xC := hC.symm
    _ = connectedComponent z := hCz
    _ = connectedComponent xD := hDz.symm
    _ = D.1 := hD

/-- The connected component of a point is exactly its left coset of the
identity component (Proposition 1.1.4(a)). -/
public theorem connectedComponent_eq_leftCoset (G : Variety k) [AlgebraicGroup G]
    (x : Variety.Point G) :
    connectedComponent x =
      Set.image (fun h : Variety.Point G => x * h)
        (Theory.AlgebraicGroup.identityComponentSubgroup G : Set (Variety.Point G)) := by
  let H := Theory.AlgebraicGroup.identityComponentSubgroup G
  apply Set.Subset.antisymm
  · intro y hy
    have himg := (Theory.AlgebraicGroup.leftMulMorphism G x⁻¹).continuous.image_connectedComponent_subset x
    have hy' : x⁻¹ * y ∈ (Theory.AlgebraicGroup.leftMulMorphism G x⁻¹).toFun '' connectedComponent x :=
      ⟨y, hy, by simp [Theory.AlgebraicGroup.leftMulMorphism_apply]⟩
    have hpre : x⁻¹ * y ∈ H := by
      have : x⁻¹ * y ∈ connectedComponent (x⁻¹ * x) := himg hy'
      change x⁻¹ * y ∈ connectedComponent (1 : Variety.Point G)
      rw [inv_mul_cancel] at this
      exact this
    refine ⟨x⁻¹ * y, hpre, ?_⟩
    change x * (x⁻¹ * y) = y
    exact mul_inv_cancel_left x y
  · intro y hy
    have himg := (Theory.AlgebraicGroup.leftMulMorphism G x).continuous.image_connectedComponent_subset
      (1 : Variety.Point G)
    have hy' : (Theory.AlgebraicGroup.leftMulMorphism G x).toFun (x⁻¹ * y) ∈
        (Theory.AlgebraicGroup.leftMulMorphism G x).toFun '' connectedComponent (1 : Variety.Point G) := by
      refine ⟨x⁻¹ * y, ?_, rfl⟩
      rcases hy with ⟨h, hh, hyh⟩
      have : x⁻¹ * y = h := by
        calc
          x⁻¹ * y = x⁻¹ * (x * h) := by rw [← hyh]
          _ = h := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      have hh' : h ∈ connectedComponent (1 : Variety.Point G) := by
        simpa [H, Theory.AlgebraicGroup.identityComponent,
          Theory.AlgebraicGroup.identityComponentSubgroup_carrier] using hh
      simpa [this] using hh'
    have hsubset : (Theory.AlgebraicGroup.leftMulMorphism G x).toFun '' connectedComponent (1 : Variety.Point G) ⊆
        connectedComponent x := by
      simpa [Theory.AlgebraicGroup.leftMulMorphism_apply, mul_one] using himg
    simpa [Theory.AlgebraicGroup.leftMulMorphism_apply] using hsubset hy'

/-- The quotient by the identity component is finite: its cosets are exactly
the connected components (Proposition 1.1.4(a)). -/
public theorem finite_quotient_identityComponentSubgroup (G : Variety k) [AlgebraicGroup G] :
    Finite (Variety.Point G ⧸ Theory.AlgebraicGroup.identityComponentSubgroup G) := by
  let H := Theory.AlgebraicGroup.identityComponentSubgroup G
  have : H.Normal := by
    simpa [H, Theory.AlgebraicGroup.identityComponentClosedSubgroup_carrier] using
      (Theory.AlgebraicGroup.identityComponentClosedSubgroup_isNormal G)
  let comps := {C : Set (Variety.Point G) //
      C ∈ Set.range (connectedComponent : Variety.Point G → Set (Variety.Point G))}
  have hfin : Finite comps := finite_connectedComponents_of_noetherian
  have hsurj : Function.Surjective
      (fun C : comps => QuotientGroup.mk' H (Classical.choose (Set.mem_range.mp C.2))) := by
    intro q
    refine Quotient.inductionOn q ?_
    intro g
    refine ⟨⟨connectedComponent g, ⟨g, rfl⟩⟩, ?_⟩
    apply Quotient.sound
    let hmem : ∃ x : Variety.Point G,
        connectedComponent x = connectedComponent g := by
      exact ⟨g, rfl⟩
    let x0 := Classical.choose hmem
    have hx0 : connectedComponent x0 = connectedComponent g := Classical.choose_spec hmem
    have hx : connectedComponent x0 =
        Set.image (fun h : Variety.Point G => x0 * h) (H : Set (Variety.Point G)) :=
      connectedComponent_eq_leftCoset G x0
    have hg : connectedComponent g =
        Set.image (fun h : Variety.Point G => g * h) (H : Set (Variety.Point G)) :=
      connectedComponent_eq_leftCoset G g
    have hgH : g ∈ Set.image (fun h : Variety.Point G => g * h) (H : Set (Variety.Point G)) :=
      ⟨1, H.one_mem, mul_one g⟩
    have : g ∈ Set.image (fun h : Variety.Point G => x0 * h) (H : Set (Variety.Point G)) := by
      have himg : Set.image (fun h : Variety.Point G => x0 * h) (H : Set (Variety.Point G)) =
          Set.image (fun h : Variety.Point G => g * h) (H : Set (Variety.Point G)) := by
        rw [← hx, ← hg, hx0]
      rw [himg]
      exact hgH
    rcases this with ⟨h, hh, hgh⟩
    have hx0g : x0⁻¹ * g = h := by
      calc
        x0⁻¹ * g = x0⁻¹ * ((fun h : Variety.Point G => x0 * h) h) := by rw [hgh]
        _ = x0⁻¹ * (x0 * h) := by rfl
        _ = h := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    simpa [QuotientGroup.leftRel_apply] using (hx0g ▸ hh)
  exact Finite.of_surjective
    (fun C : comps => QuotientGroup.mk' H (Classical.choose (Set.mem_range.mp C.2))) hsurj

/-- The identity component has finite index in the whole group
(Proposition 1.1.4(a)). -/
public instance identityComponentSubgroup_finiteIndex (G : Variety k)
    [AlgebraicGroup G] :
    (Theory.AlgebraicGroup.identityComponentSubgroup G).FiniteIndex := by
  have : Finite (Variety.Point G ⧸ Theory.AlgebraicGroup.identityComponentSubgroup G) :=
    finite_quotient_identityComponentSubgroup G
  exact ⟨Subgroup.index_ne_zero_of_finite⟩

/-- Proposition 1.1.4(a): the identity component is a closed subgroup of
finite index, and it is contained in every closed subgroup of finite index. -/
public instance Morphism.kernel_normal
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : Theory.AlgebraicGroup.Morphism G H) : f.kernel.Normal :=
  MonoidHom.normal_ker f.onPoints

/-- The first-isomorphism theorem: the quotient of the source by the kernel is
isomorphic, as an abstract group, to the image. -/
public noncomputable def Morphism.quotientKernelEquivRange
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : Theory.AlgebraicGroup.Morphism G H) :
    (Variety.Point G ⧸ f.kernel) ≃*
      MonoidHom.mrange f.onPoints :=
  QuotientGroup.quotientKerEquivRange f.onPoints

/-- A surjective morphism from a connected variety has connected target. -/
public lemma connected_of_surjective_morphism
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (hG : _root_.IsConnected (Set.univ : Set (Variety.Point G)))
    (hf : Function.Surjective f.onPoints) :
    _root_.IsConnected (Set.univ : Set (Variety.Point H)) := by
  have himage := hG.image f.onPoints f.toVariety.continuous.continuousOn
  rw [Set.image_univ, hf.range_eq] at himage
  exact himage

section

variable {k : Type u} [Field k]

/-- The closed-subvariety presentation of the identity component is
connected. -/
public lemma identityComponentClosedSubgroup_carrier_isConnected
    (G : Variety k) [AlgebraicGroup G] :
    Variety.IsConnected
      (AlgebraicGroup.identityComponentClosedSubgroup G).carrierVariety := by
  let G0 := AlgebraicGroup.identityComponentClosedSubgroup G
  let e := Variety.closedSubvarietyPointHomeomorph G0.isZariskiClosed
  have hcarrier : (G0 : Set (Variety.Point G)) =
      AlgebraicGroup.identityComponent G := by
    rfl
  have hc : _root_.IsConnected (G0 : Set (Variety.Point G)) := by
    rw [hcarrier]
    exact AlgebraicGroup.identityComponent_isConnected G
  let : ConnectedSpace {x : Variety.Point G // x ∈ G0} :=
    Subtype.connectedSpace hc
  let : ConnectedSpace (Variety.Point G0.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

end

end Theory.AlgebraicGroup

