module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CommonPlanes.Generation
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CommonPlanes.Source

/-!
# Comparing the original and reciprocal generating planes

It suffices to match the recognized root planes: their relative residuals
generate L, and source 11.1.3 identifies each residual with the reciprocal
component at the same full plane. This gives L ≤ Lᵍ; equal orders give equality.
For a paired commutator B, the planes B C_V(L) and B C_(Vᵍ)(Lᵍ) have the same
order. Hence containment of the conjugate covering center in the original
plane gives equality of the full planes, retaining both centers throughout.

The absorption premise is explicit and remains with
qt-d-1222-natural-weak-closure-source in the nonzero-center branch. The
CentralTrivial consumer discharges it when C_V(L)=1. These conditional
comparison theorems do not establish the unrestricted source clause.
Source: Aschbacher--Smith 11.1.3 and 11.2.2(5), printed pp.765,768.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CommonPlanes
open Subgroup Representation Representation.BinaryOffender
open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k:=ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (Coordinates.g2 m))

/-- Matching only the generating root planes identifies the original component. -/
theorem mem_normalizer_of_root_plane_matches (u : Model S.field.Carrier) (g : G)
    (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (localResidual L (f.Vi 1)))
    (hplanes : ∀ v : Model S.field.Carrier,
      LieParabolicSetup.highestRoot.map (MulAut.conj v).toMonoidHom ≤ longRootLocal →
      (Coordinates.g2 (ActorRecognition.recentered D S m u)).preimage
        ((naturalPlane S.field.Carrier).map (Natural.action S.field.Carrier v)) ∈
        planeFamily (L.map (MulAut.conj g).toMonoidHom)
          ((f.Vi 1).map (MulAut.conj g).toMonoidHom)
          (V.map (MulAut.conj g).toMonoidHom)) :
    g ∈ normalizer (L : Set G) := by
  have hle : L ≤ L.map (MulAut.conj g).toMonoidHom := by
    conv_lhs => rw [←root_plane_residuals_generate D S (ActorRecognition.recentered D S m u)]
    apply iSup_le
    intro v
    apply iSup_le
    intro hv
    let I := (Coordinates.g2 (ActorRecognition.recentered D S m u)).preimage
      ((naturalPlane S.field.Carrier).map (Natural.action S.field.Carrier v))
    obtain ⟨l,hl⟩ := ReciprocalPlanes.recentered_plane_conjugate D S m f u v
    have hI : I ∈ planeFamily L (f.Vi 1) V :=
      ⟨D.centralQuotientPreimage_le _,l,hl⟩
    have hone : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
    have hc := planeComponents_of_unique hcomponent 1 V
    simp only [hone,map_id] at hc
    have he := (planeComponents_of_unique hcomponent g _ I (hplanes v hv)).2 _ (hc I hI).1
    change localResidual L I ≤ _
    rw [he]
    exact (localResidual_le _).trans inf_le_left
  exact mem_normalizer_iff_map_conj_eq.mpr
    (eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g).injective])).symm

private theorem reciprocal_plane_mem (g : G) (l : L) :
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

/-- One-sided covering-center absorption suffices: equal plane orders recover
the exact reciprocal planes, and their unique components reconstruct L. -/
theorem mem_normalizer_of_covering_center_absorption
    (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (localResidual L (f.Vi 1)))
    (u : Model S.field.Carrier) (g : G)
    (a : (V.map (MulAut.conj g).toMonoidHom) →* Model S.field.Carrier)
    (hact : ∀ (x : V.map (MulAut.conj g).toMonoidHom) (v : D.space),
      (D.spaceEquiv (Multiplicative.ofAdd
        (Preliminary.markedAction D (ActorRecognition.recentered D S m u) (a x) v)) : G) =
          (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹)
    (ha : a.range = EvenTwoRank.elementary S.field.Carrier)
    (hroots : ∀ Z ∈ RootCentralizers.longRoots S.field.Carrier,
      Nonempty (ReciprocalRoots.RootData D S (ActorRecognition.recentered D S m u) g a Z))
    (habsorb : ∀ v : Model S.field.Carrier,
      LieParabolicSetup.highestRoot.map (MulAut.conj v).toMonoidHom ≤ longRootLocal →
      (V ⊓ centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ≤
        (Coordinates.g2 (ActorRecognition.recentered D S m u)).preimage
          ((naturalPlane S.field.Carrier).map (Natural.action S.field.Carrier v))) :
    g ∈ normalizer (L : Set G) := by
  apply mem_normalizer_of_root_plane_matches D S m f u g hcomponent
  intro v hv
  let Z := LieParabolicSetup.highestRoot.map (MulAut.conj v).toMonoidHom
  obtain ⟨r⟩ := hroots Z ⟨hv,v,rfl⟩
  have hP := original_root_plane D S (ActorRecognition.recentered D S m u)
    _ a hact ha v hv
  have hQ := ReciprocalPlanes.conjugate_root_commutator_sup_center D S
    (ActorRecognition.recentered D S m u) g _ r.actor r.conjugator
    r.action r.root_image (ReciprocalPlanes.rootData_actor_ne_bot D S _ g a Z r)
  obtain ⟨k,hk⟩ := ReciprocalPlanes.recentered_plane_conjugate D S m f u r.conjugator
  rw [hk] at hQ
  obtain ⟨l,hl⟩ := ReciprocalPlanes.recentered_plane_conjugate D S m f u v
  have hle :
      ((f.Vi 1).map (MulAut.conj (k : G)).toMonoidHom).map (MulAut.conj g).toMonoidHom ≤
        (Coordinates.g2 (ActorRecognition.recentered D S m u)).preimage
          ((naturalPlane S.field.Carrier).map (Natural.action S.field.Carrier v)) := by
    rw [←hQ]
    exact sup_le (le_sup_left.trans_eq hP) (habsorb v hv)
  have he := eq_of_le_of_card_ge hle (by
    rw [hl,card_map_of_injective (MulAut.conj (l : G)).injective,
      card_map_of_injective (MulAut.conj g).injective,
      card_map_of_injective (MulAut.conj (k : G)).injective])
  rw [←he]
  exact reciprocal_plane_mem D S m f g k
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CommonPlanes
