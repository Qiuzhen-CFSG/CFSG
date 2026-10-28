module

public import Theory.AlgebraicGroup.Variety.MorphicActionTransport
public import Theory.AlgebraicGroup.Variety.ProjectiveLine
public import Theory.AlgebraicGroup.Bor1.RankOneGeometry.CurveInputs

/-!
# The projective-line action of the actual Borel curve

The closed orbit and the canonical reduced closed locus have the same support,
so their reduced schemes are isomorphic. Restrict the original regular action
to that locus and transport it along the supplied curve isomorphism. Its exact
point stabilizer remains the original Borel. This is the assembly step between
Borel §13.13(4)'s curve isomorphism and the PGL₂ action-family theorem, with no
faithfulness, separability, or pre-existing rank-one group map assumption.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
namespace Theory.AlgebraicGroup.Variety.Geometric
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {X Y : Geometric k}

theorem MorphicAction.exists_transport_closed_orbit
    (A : MorphicAction G X) (x : Point X)
    (hc : IsClosed (Set.range (A.orbitMorphismAt x).hom))
    (e : (A.orbitSubvariety x).toGeometric.toScheme ≅ Y.toScheme)
    (he : e.hom ≫ Y.structureMap=(A.orbitSubvariety x).toGeometric.structureMap) :
    ∃ (D : MorphicAction G Y) (y : Point Y),
      ∀ g, D.toMulAction.smul g y=y ↔ A.toMulAction.smul g x=x := by
  let Z : TopologicalSpace.Closeds X.toScheme := ⟨Set.range (A.orbitMorphismAt x).hom,hc⟩
  let C := reducedClosedSubvariety X Z
  let O := A.orbitSubvariety x
  let : IsClosedImmersion O.inclusion.hom := A.orbitSubvariety_isClosedImmersion x hc
  have hr : Set.range C.inclusion.hom=Set.range O.inclusion.hom :=
    (reducedClosedSubvariety_range X Z).trans (A.orbitSubvariety_range x).symm
  obtain ⟨s,_,hs⟩ := exists_schemeIso_of_closedImmersion_range_eq C.inclusion O.inclusion hr
  let c := s.trans e
  have hcc : c.hom ≫ Y.structureMap=C.toGeometric.structureMap := by
    change (s.hom ≫ e.hom) ≫ Y.structureMap=C.toGeometric.structureMap
    rw [Category.assoc,he,hs]
  have hinv : ∀ (g : Variety.Point G) (p : Point X),
      p.1 (IsLocalRing.closedPoint k)∈Z →
        (A.toMulAction.smul g p).1 (IsLocalRing.closedPoint k)∈Z := by
    intro g p hp
    obtain ⟨a,rfl⟩ := (A.point_mem_orbit_range_iff x p).mp hp
    exact (A.point_mem_orbit_range_iff x _).mpr ⟨g*a,A.toMulAction.mul_smul g a x⟩
  let R := A.onInvariantReducedClosedSubvariety Z hinv
  obtain ⟨xC,hxC,_⟩ := (point_mem_reducedClosedSubvariety_iff X Z x).mp
    ((A.point_mem_orbit_range_iff x x).mpr ⟨1,A.toMulAction.one_smul x⟩)
  let D := R.transportSchemeIso c hcc
  let y := schemeIsoPointEquiv c hcc xC
  refine ⟨D,y,?_⟩
  intro g
  have hinj : Function.Injective (fun p : Point C.toGeometric => C.inclusion p) := by
    intro p q hh
    apply Subtype.ext
    exact (cancel_mono C.inclusion.hom).mp (congrArg Subtype.val hh)
  change (R.transportSchemeIso c hcc).toMulAction.smul g (schemeIsoPointEquiv c hcc xC)=
    schemeIsoPointEquiv c hcc xC ↔ _
  rw [R.transportSchemeIso_smul,(schemeIsoPointEquiv c hcc).injective.eq_iff]
  rw [←hinj.eq_iff]
  rw [A.onInvariantReducedClosedSubvariety_inclusion,hxC]


theorem MorphicAction.exists_projectiveLine_borel_action_of_curve_iso
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (A : MorphicAction G X) (x : Point X)
    (hstab : ∀ g : Variety.Point G,A.toMulAction.smul g x=x ↔ g∈B.toSubgroup)
    (e : (A.orbitSubvariety x).toGeometric.toScheme ≅ (projectiveLine k).toScheme)
    (he : e.hom ≫ (projectiveLine k).structureMap=(A.orbitSubvariety x).toGeometric.structureMap) :
    ∃ (D : MorphicAction G (projectiveLine k)) (p : Point (projectiveLine k)),
      ∀ g : Variety.Point G,D.toMulAction.smul g p=p ↔ g∈B.toSubgroup := by
  have hc := A.orbit_isClosed_of_borel_fixed hG B hB x (fun g hg => (hstab g).mpr hg)
  obtain ⟨D,p,hDp⟩ := A.exists_transport_closed_orbit x hc e he
  exact ⟨D,p,fun g => (hDp g).trans (hstab g)⟩

end Theory.AlgebraicGroup.Variety.Geometric
