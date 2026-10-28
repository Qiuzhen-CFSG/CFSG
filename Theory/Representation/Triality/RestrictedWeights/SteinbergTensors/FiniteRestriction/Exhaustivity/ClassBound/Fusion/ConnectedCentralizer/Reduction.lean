module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.Restriction
public import Theory.AlgebraicGroup.RootSubgroups.FixedTorusConnectedGeneration

/-!
# Connected root-generated subgroups of toral centralizers

The torus and the root groups on which a torus point has weight one generate
a connected subgroup of its centralizer. To prove that this is the whole
centralizer, two geometric assertions remain: Bruhat coverage by this subgroup
and the torus normalizer, and containment of the centralizing normalizer in
the root-generated subgroup. They are kept separate below.

This is the inner-automorphism argument in Steinberg, Sections 8.2--8.5,
especially Remark 8.3(c), in `refs/KGroup/GLS3/Chapter2St2.tex`. The latter
normalizer assertion uses the full character lattice; universal-version
isogenies alone do not provide a regular splitting.
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound

open Theory.AlgebraicGroup

universe u
variable {k : Type u} [Field k]
variable {K : Variety k} [AlgebraicGroup K]

namespace ConnectedCentralizer

private theorem centralizer_image {G : Type*} [Group G] (e : G ≃* G) (x : G) :
    e '' (Subgroup.centralizer {x} : Set G) =
      (Subgroup.centralizer {e x} : Set G) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using
      congrArg e (Subgroup.mem_centralizer_singleton_iff.mp hz)
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      Subgroup.mem_centralizer_singleton_iff.mp hy

/-- Algebraic conjugation transports connectedness of point centralizers. -/
theorem centralizer_isConnected_of_isConj {x y : Variety.Point K}
    (hxy : IsConj x y)
    (hy : _root_.IsConnected (Subgroup.centralizer {y} : Set (Variety.Point K))) :
    _root_.IsConnected (Subgroup.centralizer {x} : Set (Variety.Point K)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy.symm
  have h := hy.image (Theory.AlgebraicGroup.conjugationByMorphism K g).toFun
    (Theory.AlgebraicGroup.conjugationByMorphism K g).continuous.continuousOn
  change _root_.IsConnected
    ((MulAut.conj g) '' (Subgroup.centralizer {y} : Set (Variety.Point K))) at h
  rw [centralizer_image, show (MulAut.conj g) y = x from hg] at h
  exact h

/-- Convert ambient connectedness to connectedness of the actual closed
subgroup variety, using its closed-subvariety homeomorphism. -/
theorem carrier_isConnected (C : ClosedSubgroup K)
    (hC : _root_.IsConnected (C : Set (Variety.Point K))) :
    Variety.IsConnected C.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph C.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point K // x ∈ (C : Set (Variety.Point K))} :=
    Subtype.connectedSpace hC
  let : ConnectedSpace (Variety.Point C.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

variable [CharP k 2]

/-- The torus together with the actual root groups centralizing `t`. -/
def toralRootSubgroup (S : Geometry K) (t : Variety.Point S.torus.carrierVariety) :
    Subgroup (Variety.Point K) :=
  S.torus.toSubgroup ⊔ RootSubgroupGenerated S.roots
    {a | (S.roots.rootWeight a).pointCharacter t = 1}

/-- The part of the point centralizer lying in the actual torus normalizer. -/
def toralNormalizerCentralizer (S : Geometry K)
    (t : Variety.Point S.torus.carrierVariety) : Subgroup (Variety.Point K) :=
  S.torus.normalizer.toSubgroup ⊓ Subgroup.centralizer {S.torus.includePoint t}

/-- The root-group weight equation puts every selected root group in the
point centralizer. -/
theorem rootSubgroup_le_centralizer (S : Geometry K)
    (t : Variety.Point S.torus.carrierVariety) (a : S.roots.Root)
    (ha : (S.roots.rootWeight a).pointCharacter t = 1) :
    (S.roots.rootSubgroup a).toSubgroup ≤
      Subgroup.centralizer {S.torus.includePoint t} := by
  intro y hy
  let X := S.roots.rootSubgroup a
  let p := S.rootParameter a
  let yX : Variety.Point X.carrierVariety := X.pointEquiv.symm ⟨y, hy⟩
  let q := p.inv.onPoints yX
  let c : k := Multiplicative.toAdd (additiveGroupPointEquiv k q)
  have hq : kPlusPoint c = q := by
    apply (additiveGroupPointEquiv k).injective
    exact Multiplicative.ofAdd.apply_symm_apply (additiveGroupPointEquiv k q)
  have hpc : X.includePoint (p.value c) = y := by
    change (X.pointEquiv (p.hom.onPoints (kPlusPoint c))).val = y
    rw [hq, p.inv_hom_id]
    exact congrArg Subtype.val (X.pointEquiv.apply_symm_apply ⟨y, hy⟩)
  have hconj := (S.realized.2.2.1 a).2 p c t
  rw [ha, one_mul, hpc] at hconj
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  calc
    y * S.torus.includePoint t =
        S.torus.includePoint t *
          ((S.torus.includePoint t)⁻¹ * y * S.torus.includePoint t) := by group
    _ = S.torus.includePoint t * y := congrArg (fun z => S.torus.includePoint t * z) hconj

/-- The proposed connected subgroup really lies in the literal centralizer. -/
theorem toralRootSubgroup_le_centralizer (S : Geometry K)
    (t : Variety.Point S.torus.carrierVariety) :
    toralRootSubgroup S t ≤ Subgroup.centralizer {S.torus.includePoint t} := by
  apply sup_le
  · intro y hy
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hcomm := S.maximalTorus.1.isMulCommutative
    rw [isMulCommutative_iff] at hcomm
    exact congrArg S.torus.inclusion.onPoints
      (hcomm (S.torus.pointEquiv.symm ⟨y, hy⟩) t)
  · exact RootSubgroupGenerated_le_of_rootSubgroup_le _ _ _
      (fun a ha => rootSubgroup_le_centralizer S t a ha)

/-- Connectedness follows from actual connected root groups and a torus. -/
theorem toralRootSubgroup_isConnected [IsAlgClosed k] (S : Geometry K)
    (t : Variety.Point S.torus.carrierVariety) :
    _root_.IsConnected (toralRootSubgroup S t : Set (Variety.Point K)) := by
  have hT : _root_.IsConnected (S.torus : Set (Variety.Point K)) := by
    let : ConnectedSpace (Variety.Point S.torus.carrierVariety) :=
      connectedSpace_iff_univ.mpr S.maximalTorus.1.isConnected
    change _root_.IsConnected (S.torus.toSubgroup : Set (Variety.Point K))
    rw [← S.torus.range_inclusion]
    exact isConnected_range S.torus.inclusion.toVariety.continuous
  exact isConnected_sup_rootSubgroupGenerated S.torus hT S.roots S.realized _

/-- The two independent geometric inputs identify the centralizer exactly. -/
theorem centralizer_eq_toralRootSubgroup (S : Geometry K)
    (t : Variety.Point S.torus.carrierVariety)
    (hbruhat : Subgroup.centralizer {S.torus.includePoint t} ≤
      toralRootSubgroup S t ⊔ toralNormalizerCentralizer S t)
    (hnormalizer : toralNormalizerCentralizer S t ≤ toralRootSubgroup S t) :
    Subgroup.centralizer {S.torus.includePoint t} = toralRootSubgroup S t :=
  le_antisymm (hbruhat.trans (sup_le le_rfl hnormalizer))
    (toralRootSubgroup_le_centralizer S t)

/-- Toral connectedness from Bruhat coverage and the normalizer calculation.
Neither geometric input is asserted here. -/
theorem toral_centralizer_isConnected [IsAlgClosed k] (S : Geometry K)
    (t : Variety.Point S.torus.carrierVariety)
    (hbruhat : Subgroup.centralizer {S.torus.includePoint t} ≤
      toralRootSubgroup S t ⊔ toralNormalizerCentralizer S t)
    (hnormalizer : toralNormalizerCentralizer S t ≤ toralRootSubgroup S t) :
    _root_.IsConnected
      (Subgroup.centralizer {S.torus.includePoint t} : Set (Variety.Point K)) := by
  rw [centralizer_eq_toralRootSubgroup S t hbruhat hnormalizer]
  exact toralRootSubgroup_isConnected S t

end ConnectedCentralizer

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
