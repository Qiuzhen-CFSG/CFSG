module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalPlanes.Conjugate
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.SourceAssembly

/-!
# Original reciprocal plane and component families in 11.2.2(5)

The proved reciprocal-root source construction supplies the actual actors and
exact coranks. Their commutators, joined with the conjugate covering center,
are full planes in the literal Lᵍ-orbit of V₂ᵍ. Recentering the model action
preserves this entire original plane orbit. The final theorem applies the
preceding 11.1.3 component uniqueness on each reconstructed plane and its
actual relative solvable residual.

Only permitted earlier-source clauses remain explicit here; their discharge
belongs to qt-d-1222-natural-local-geometry. Matching the original and reciprocal
full planes in the common three-space, and final weak-closure assembly, remain
with qt-d-1222-natural-weak-closure-source. Neither equality of the covering
centers nor RootSpan.moved is assumed. This proves the reciprocal plane step,
not all of source 11.2.2(5).
Source: Aschbacher--Smith 11.1.3 and 11.2.2(5), printed pp.765,768.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalPlanes
open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k:=ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (Coordinates.g2 m))

/-- Recentering the actor retains the entire original plane orbit. -/
theorem recentered_plane_conjugate (u v : Model S.field.Carrier) : ∃ l : L,
    (Coordinates.g2 (ActorRecognition.recentered D S m u)).preimage
      ((naturalPlane S.field.Carrier).map (Natural.action S.field.Carrier v)) =
        (f.Vi 1).map (MulAut.conj (l : G)).toMonoidHom := by
  rw [ActorRecognition.recentered_preimage,←Submodule.map_comp]
  have he : (Natural.action S.field.Carrier u).comp (Natural.action S.field.Carrier v) =
      Natural.action S.field.Carrier (u*v) := by
    ext x
    simp only [map_mul,Module.End.mul_apply,LinearMap.comp_apply]
  rw [he]
  exact preimage_plane_conjugate D S m f (u*v)

/-- Source 11.2.2(5): the constructed original reciprocal roots recover full
planes in the literal Lᵍ-orbit of V₂ᵍ. All actor, kernel and corank premises are
supplied by the preceding source family. No equality of covering centers is used. -/
theorem source_reciprocal_planes
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hnon : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ∃ (u : Model S.field.Carrier)
      (a : (V.map (MulAut.conj g).toMonoidHom) →* Model S.field.Carrier),
      (∀ (x : V.map (MulAut.conj g).toMonoidHom) (v : D.space),
        (D.spaceEquiv (Multiplicative.ofAdd
          (Preliminary.markedAction D (ActorRecognition.recentered D S m u) (a x) v)) : G) =
            (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹) ∧
      a.ker = (centralizer (V : Set G)).subgroupOf (V.map (MulAut.conj g).toMonoidHom) ∧
      a.range = EvenTwoRank.elementary S.field.Carrier ∧
      ∀ Z ∈ RootCentralizers.longRoots S.field.Carrier,
        ∃ l : L, ⁅V.map (MulAut.conj g).toMonoidHom,
          V ⊓ centralizer (RootPullback.rootPreimage _ a Z : Set G)⁆ ⊔
          (V ⊓ centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom =
            ((f.Vi 1).map (MulAut.conj (l : G)).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨u,a,hact,hker,ha,hroots⟩ :=
    ReciprocalRoots.source_root_family D S m f hunique hthree hline g hg hnon
  refine ⟨u,a,hact,hker,ha,?_⟩
  intro Z hZ
  obtain ⟨r⟩ := hroots Z hZ
  obtain ⟨l,hl⟩ := recentered_plane_conjugate D S m f u r.conjugator
  refine ⟨l,?_⟩
  rw [←hl]
  exact conjugate_root_commutator_sup_center D S _ g _ r.actor r.conjugator
    r.action r.root_image (rootData_actor_ne_bot D S _ g a Z r)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalPlanes

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalPlanes
open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k:=ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (Coordinates.g2 m))

private theorem conjugate_plane_mem (g : G) (l : L) :
    ((f.Vi 1).map (MulAut.conj (l : G)).toMonoidHom).map (MulAut.conj g).toMonoidHom ∈
      planeFamily (L.map (MulAut.conj g).toMonoidHom)
        ((f.Vi 1).map (MulAut.conj g).toMonoidHom)
        (V.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨map_mono ?_,⟨MulAut.conj g l,mem_map_of_mem _ l.property⟩,?_⟩
  · exact (map_mono (D.centralQuotientPreimage_le _)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (D.normalizes l.property))
  · rw [map_map,map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply]
    group

/-- Actual 11.1.3 component application to every full reciprocal root plane.
The original unique-component premise is transported on the reconstructed plane,
with its conjugate covering center retained. Common-plane matching remains with
this source owner; earlier-source discharge belongs to the local-geometry owner. -/
theorem source_reciprocal_plane_components
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))
    (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (localResidual L (f.Vi 1)))
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hnon : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ∃ (u : Model S.field.Carrier)
      (a : (V.map (MulAut.conj g).toMonoidHom) →* Model S.field.Carrier),
      (∀ (x : V.map (MulAut.conj g).toMonoidHom) (v : D.space),
        (D.spaceEquiv (Multiplicative.ofAdd
          (Preliminary.markedAction D (ActorRecognition.recentered D S m u) (a x) v)) : G) =
            (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹) ∧
      a.ker = (centralizer (V : Set G)).subgroupOf (V.map (MulAut.conj g).toMonoidHom) ∧
      a.range = EvenTwoRank.elementary S.field.Carrier ∧
      ∀ Z ∈ RootCentralizers.longRoots S.field.Carrier,
        let I := ⁅V.map (MulAut.conj g).toMonoidHom,
          V ⊓ centralizer (RootPullback.rootPreimage _ a Z : Set G)⁆ ⊔
          (V ⊓ centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom
        I ∈ planeFamily (L.map (MulAut.conj g).toMonoidHom)
            ((f.Vi 1).map (MulAut.conj g).toMonoidHom)
            (V.map (MulAut.conj g).toMonoidHom) ∧
          Source.UniqueNoncentralComponent (normalizer (I : Set G)) I
            (localResidual (L.map (MulAut.conj g).toMonoidHom) I) := by
  obtain ⟨u,a,hact,hker,ha,hplanes⟩ :=
    source_reciprocal_planes D S m f hunique hthree hline g hg hnon
  refine ⟨u,a,hact,hker,ha,?_⟩
  intro Z hZ
  obtain ⟨l,hl⟩ := hplanes Z hZ
  have hi := hl.symm ▸ conjugate_plane_mem D S m f g l
  exact ⟨hi,planeComponents_of_unique hcomponent g _ _ hi⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalPlanes
