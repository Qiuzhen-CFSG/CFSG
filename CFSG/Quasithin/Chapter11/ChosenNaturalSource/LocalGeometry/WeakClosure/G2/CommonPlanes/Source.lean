module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CommonPlanes.Transfer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CentralContainment.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalPlanes.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.PlaneGeneration

/-!
# Paired original and reciprocal full planes in 11.2.2(5)

The same recentered marking supplies the original actor and a common full
third flag preimage in V intersect Vᵍ. Its full original plane family generates
L by relative residuals. For every long-root preimage D, the commutator
[C_V(D),Vᵍ] joined with C_V(L) is an original full plane in this three-space;
joined with C_(Vᵍ)(Lᵍ), it is a reciprocal full plane. Source 11.1.3 supplies
the unique noncentral component at each of these actual planes.

The last equality retains both central terms. It is not equality of the two
planes. Coverage and comparison of the full families, including their centers,
and the final weak-closure assembly remain with
qt-d-1222-natural-weak-closure-source. The only preceding-source inputs here
are discharged by qt-d-1222-natural-local-geometry. Neither RootSpan.moved nor
vanishing of C_V(L) is assumed; this is not all of source 11.2.2(5).
Source: Aschbacher--Smith 11.1.3 and 11.2.2(5), printed pp.765,768.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CommonPlanes
open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k:=ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (Coordinates.g2 m))

/-- The common three-space uses the same recentred marking as the actors,
and is an actual L-conjugate of the full original third flag preimage. -/
theorem recentered_three_conjugate (u : Model S.field.Carrier) : ∃ l : L,
    (Coordinates.g2 (ActorRecognition.recentered D S m u)).preimage
      ((NaturalOffenders.upper (F:=S.field.Carrier)).comap
        (Restricted.NaturalCoordinates.coordinates S.field.Carrier)) =
      (f.Vi 2).map (MulAut.conj (l : G)).toMonoidHom := by
  obtain ⟨l₀,hl₀⟩ := RootPullback.exists_flag_conjugate D S m f
  obtain ⟨l₁,hl₁⟩ := (Coordinates.g2 m).quotientMap_surjective u
  let W := (NaturalOffenders.upper (F:=S.field.Carrier)).comap
    (Restricted.NaturalCoordinates.coordinates S.field.Carrier)
  refine ⟨l₁*l₀,?_⟩
  rw [ActorRecognition.recentered_preimage]
  have hm := (Coordinates.g2 m).preimage_conjugate l₁ W
  change ((Coordinates.g2 m).preimage W).map (MulAut.conj (l₁ : G)).toMonoidHom =
    (Coordinates.g2 m).preimage
      (W.map (Natural.action S.field.Carrier ((Coordinates.g2 m).quotientMap l₁))) at hm
  rw [hl₁] at hm
  rw [←hm,hl₀,map_map]
  congr 1
  ext x
  change (l₁ : G)*((l₀ : G)*x*(l₀ : G)⁻¹)*(l₁ : G)⁻¹ =
    ((l₁ : G)*(l₀ : G))*x*((l₁ : G)*(l₀ : G))⁻¹
  group

/-- The two actual full plane families on each original root commutator.
The original plane lies in V intersect Vᵍ. Both sides retain their own covering
centers; after adjoining both centers their equality is literal. -/
theorem source_paired_root_planes
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
      let U := (Coordinates.g2 (ActorRecognition.recentered D S m u)).preimage
        ((NaturalOffenders.upper (F:=S.field.Carrier)).comap
          (Restricted.NaturalCoordinates.coordinates S.field.Carrier))
      (∃ l : L, U = (f.Vi 2).map (MulAut.conj (l : G)).toMonoidHom) ∧
      U ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom ∧
      planeResidualSpan L (planeFamily L (f.Vi 1) U) = L ∧
      ∀ Z ∈ RootCentralizers.longRoots S.field.Carrier,
        let B := ⁅V.map (MulAut.conj g).toMonoidHom,
          V ⊓ centralizer (RootPullback.rootPreimage _ a Z : Set G)⁆
        let C := V ⊓ centralizer (L : Set G)
        let Cg := C.map (MulAut.conj g).toMonoidHom
        (B ⊔ C ∈ planeFamily L (f.Vi 1) U) ∧
        (B ⊔ Cg ∈ planeFamily (L.map (MulAut.conj g).toMonoidHom)
          ((f.Vi 1).map (MulAut.conj g).toMonoidHom) (V.map (MulAut.conj g).toMonoidHom)) ∧
        Source.UniqueNoncentralComponent (normalizer ((B ⊔ C : Subgroup G) : Set G)) (B ⊔ C)
          (localResidual L (B ⊔ C)) ∧
        Source.UniqueNoncentralComponent (normalizer ((B ⊔ Cg : Subgroup G) : Set G)) (B ⊔ Cg)
          (localResidual (L.map (MulAut.conj g).toMonoidHom) (B ⊔ Cg)) ∧
        (B ⊔ C) ⊔ Cg = (B ⊔ Cg) ⊔ C := by
  obtain ⟨u,a,hact,hker,ha,hroots⟩ :=
    ReciprocalRoots.source_root_family D S m f hunique hthree hline g hg hnon
  have hC := CentralContainment.source_central_containment D S m f hunique hthree hline g hg hnon
  let U := (Coordinates.g2 (ActorRecognition.recentered D S m u)).preimage
    ((NaturalOffenders.upper (F:=S.field.Carrier)).comap
      (Restricted.NaturalCoordinates.coordinates S.field.Carrier))
  obtain ⟨l₀,hl₀⟩ := recentered_three_conjugate D S m f u
  have hUA : U ≤ V.map (MulAut.conj g).toMonoidHom :=
    (RootPullback.threePreimage_le_conjugate_iff D S _ g a hact ha
      (RootPullback.strict_globalR_of_preceding D S m f hunique hthree hline)).mpr hC
  have hgen : planeResidualSpan L (planeFamily L (f.Vi 1) U) = L := by
    rw [show U = _ from hl₀]
    exact planeFamily_residuals_generate_conjugate D S m f l₀
  refine ⟨u,a,hact,hker,ha,⟨l₀,hl₀⟩,le_inf (D.centralQuotientPreimage_le _) hUA,hgen,?_⟩
  intro Z hZ
  dsimp only
  obtain ⟨r⟩ := hroots Z hZ
  obtain ⟨hZle,v,hZv⟩ := hZ
  obtain ⟨l,hl⟩ := ReciprocalPlanes.recentered_plane_conjugate D S m f u v
  have hP := original_root_plane D S (ActorRecognition.recentered D S m u)
    _ a hact ha v (hZv ▸ hZle)
  rw [←hZv,hl] at hP
  obtain ⟨k,hk⟩ := ReciprocalPlanes.recentered_plane_conjugate D S m f u r.conjugator
  have hQ := ReciprocalPlanes.conjugate_root_commutator_sup_center D S
    (ActorRecognition.recentered D S m u) g _ r.actor r.conjugator
    r.action r.root_image (ReciprocalPlanes.rootData_actor_ne_bot D S _ g a Z r)
  rw [hk] at hQ
  have hPU : ⁅V.map (MulAut.conj g).toMonoidHom,
        V ⊓ centralizer (RootPullback.rootPreimage _ a Z : Set G)⁆ ⊔
      (V ⊓ centralizer (L : Set G)) ≤ U := by
    rw [hP,←hl]
    exact ((Coordinates.g2 (ActorRecognition.recentered D S m u)).preimage_le_iff _ _).mpr
      (root_plane_le_three S.field.Carrier v (hZv ▸ hZle))
  have hPi : ⁅V.map (MulAut.conj g).toMonoidHom,
        V ⊓ centralizer (RootPullback.rootPreimage _ a Z : Set G)⁆ ⊔
      (V ⊓ centralizer (L : Set G)) ∈
        planeFamily L (f.Vi 1) U :=
    ⟨hPU,l,hP⟩
  have hQbase :
      ((f.Vi 1).map (MulAut.conj (k : G)).toMonoidHom).map (MulAut.conj g).toMonoidHom ∈
        planeFamily (L.map (MulAut.conj g).toMonoidHom)
          ((f.Vi 1).map (MulAut.conj g).toMonoidHom)
          (V.map (MulAut.conj g).toMonoidHom) := by
    refine ⟨map_mono ?_,⟨MulAut.conj g k,mem_map_of_mem _ k.property⟩,?_⟩
    · exact (map_mono (D.centralQuotientPreimage_le _)).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp (D.normalizes k.property))
    · rw [map_map,map_map]
      congr 1
      ext x
      simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply]
      group
  have hQi := hQ.symm ▸ hQbase
  have hone : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
  have hPc := planeComponents_of_unique hcomponent 1 U
  simp only [hone,map_id] at hPc
  refine ⟨hPi,hQi,hPc _ hPi,planeComponents_of_unique hcomponent g _ _ hQi,?_⟩
  exact sup_right_comm _ _ _
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CommonPlanes
