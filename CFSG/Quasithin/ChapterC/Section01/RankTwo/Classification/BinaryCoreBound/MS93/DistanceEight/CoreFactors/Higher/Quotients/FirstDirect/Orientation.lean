module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.FirstDirect.Marking
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Linear

/-!
# The first marked dual section from the actual edge action

The same edge kernel has a fixed plane on the original natural subgroup
and a fixed line on the actual first-hat quotient. Equivariant coordinates
would preserve those cardinalities, so the natural orientation is impossible.
The checked inner/graph classification then yields the dual coordinates
with exactly the CommonFacts marking and original source projection.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(v), pp.898--899.
This binary direct proof avoids assuming either doubled higher section.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.FirstDirect
open PathCentrality
open Early.Orbit.Source.HatIdentity.Third
open Escape.Propagation.Backward.Products.Selection.Choices
open SecondLayer.Recognition
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

noncomputable def baseNaturalModel (common : CommonFacts R source geometry)
    (s : Escape.NaturalSectionAt (alpha R) (V R (alpha R)) (Z R (alpha R))) : LocalModel (alpha R) where
  projection := common.natural.marking.toMonoidHom.comp (source.projection.comp (baseEquiv R).symm.toMonoidHom)
  surjective := common.natural.marking.surjective.comp (source.projection_surjective.comp (baseEquiv R).symm.surjective)
  kernel := by
    ext x
    change common.natural.marking (source.projection ((baseEquiv R).symm x)) = 1 ↔ _
    rw [common.natural.marking.map_eq_one_iff]
    have h := SetLike.ext_iff.mp (quotientActor_kernel common s) ((baseEquiv R).symm x)
    change quotientActor common s ((baseEquiv R).symm x) = 1 ↔ source.projection ((baseEquiv R).symm x) = 1 at h
    have he : quotientActor common s ((baseEquiv R).symm x) = SourceLines.actor common (base_color R) s x := by
      change SourceLines.actor common (base_color R) s ((baseEquiv R) ((baseEquiv R).symm x)) = _
      rw [MulEquiv.apply_symm_apply]
    rw [he] at h
    rw [← h]
    exact (congrArg (fun N : Subgroup (stabilizer R (alpha R)) => x ∈ N)
      (SourceLines.actor_kernel common (base_color R) s)).to_iff
  equiv := common.natural.equiv
  action := by
    intro g u v hv
    obtain ⟨m,rfl⟩ := (baseEquiv R).surjective g
    apply Multiplicative.toAdd.injective
    change (common.natural.equiv v).toAdd =
      (common.natural.marking (source.projection ((baseEquiv R).symm ((baseEquiv R) m)))).val.mulVec _
    rw [MulEquiv.symm_apply_apply]
    exact common.natural.action m u v hv

private theorem fixed_lower (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a t : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t) (model : LocalModel a) :
    4 ≤ Nat.card (fixedSpace (model.actorImage (Q R t))) := by
  let E := ⁅Z R a,Q R t⁆
  have hEU : E ≤ U R a := Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
    (LocalCommutator.moduleFacts common) a t ha hat
  have hEZ : E ≤ Z R t := commutator_le_of_normalized_index_two _ _ _
    (Escape.EdgeTransfer.edge_Z_le a t ha hat) (earlier.edge_Z_index a t ha hat)
    ((show Q R t ≤ stabilizer R a from fun _ hx => hx.2 a (adjacent_symm R hat)).trans (Z_normalized R a))
    ((show Q R t ≤ stabilizer R t from fun _ hx => hx.1).trans (Z_normalized R t))
  have hEc : E ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
    rw [Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance (LocalCommutator.moduleFacts common) a t ha hat] at hEZ
    exact hEZ.trans inf_le_right
  have hfix : model.coordinates E ≤ fixedSpace (model.actorImage (Q R t)) := by
    rintro _ ⟨u,hu,rfl⟩ _ ⟨g,hg,rfl⟩
    exact (model.action_fixed_iff g u).mpr (hEc hu g hg)
  have hcard : Nat.card (model.coordinates E) = 4 := by
    rw [model.coordinates_card E hEU, Early.First.Layer.edge_displacement_card common earlier ha hat]
  rw [← hcard]
  exact card_le_of_le hfix

private theorem fixed_card_transport (σ κ : SL ≃* SL) (P : Subgroup SL)
    (f : Space ≃* Space)
    (hf : ∀ g x, f (modelAction (σ g) x) = modelAction (κ g) (f x)) :
    Nat.card (fixedSpace (P.map σ.toMonoidHom)) = Nat.card (fixedSpace (P.map κ.toMonoidHom)) := by
  have hmap : (fixedSpace (P.map σ.toMonoidHom)).map f.toMonoidHom = fixedSpace (P.map κ.toMonoidHom) := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩ _ ⟨g,hg,rfl⟩
      change modelAction (κ g) (f x) = f x
      rw [← hf, hx (σ g) (mem_map_of_mem _ hg)]
    · intro y hy
      refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
      rintro _ ⟨g,hg,rfl⟩
      apply f.injective
      change f (modelAction (σ g) (f.symm y)) = f (f.symm y)
      rw [hf, f.apply_symm_apply, hy (κ g) (mem_map_of_mem _ hg)]
  rw [← hmap]
  exact Nat.card_congr ((fixedSpace (P.map σ.toMonoidHom)).equivMapOfInjective f.toMonoidHom f.injective).toEquiv

theorem no_natural_coordinates (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (s : Escape.NaturalSectionAt (alpha R) (V R (alpha R)) (Z R (alpha R))) :
    ¬ ∃ f : Space ≃* Space, ∀ g x,
      (f (modelAction (sourceMarking common s g) x)).toAdd =
        (common.natural.marking g).val.mulVec (f x).toAdd := by
  rintro ⟨f,hf⟩
  let P := ((Q R (p.walk.getVert 5)).subgroupOf (stabilizer R (alpha R))).map
    (source.projection.comp (baseEquiv R).symm.toMonoidHom)
  have hfirst : P.map (sourceMarking common s).toMonoidHom =
      ((Q R (p.walk.getVert 5)).subgroupOf (stabilizer R (alpha R))).map (SourceLines.actor common (base_color R) s) := by
    dsimp only [P]
    rw [map_map]
    congr 1
    ext x : 1
    change sourceMarking common s (source.projection ((baseEquiv R).symm x)) = SourceLines.actor common (base_color R) s x
    rw [sourceMarking_apply]
    change SourceLines.actor common (base_color R) s ((baseEquiv R) ((baseEquiv R).symm x)) = _
    rw [MulEquiv.apply_symm_apply]
  have hsecond : P.map common.natural.marking.toMonoidHom =
      (baseNaturalModel common s).actorImage (Q R (p.walk.getVert 5)) := by
    dsimp only [P]
    rw [map_map]
    rfl
  have hfix := fixed_card_transport (sourceMarking common s) common.natural.marking P f
    (fun g x => Multiplicative.toAdd.injective (hf g x))
  rw [hfirst,hsecond] at hfix
  have hadj : Adjacent R (alpha R) (p.walk.getVert 5) := by simpa only [p.center_eq] using p.adjacent (i := 4) (by decide)
  have hc := p.even_color (i := 6) (by decide) (by decide)
  have hct : Adjacent R (p.walk.getVert 6) (p.walk.getVert 5) := adjacent_symm R (p.adjacent (i := 5) (by decide))
  have hm := (p.moving_neighbors source common earlier (i := 4) (by decide) (by decide) (by decide)).2
  simp only [p.center_eq] at hm
  have htwo : Nat.card (fixedSpace (((Q R (p.walk.getVert 5)).subgroupOf (stabilizer R (alpha R))).map
      (SourceLines.actor common (base_color R) s))) = 2 := by
    rw [SourceLines.edge_kernel_image common earlier hc (base_color R) hct hadj hm s,
      LineModel.fixed_core_line _ (SourceLines.image_card common earlier hc (base_color R) hct hadj hm s),
      SourceLines.image_card common earlier hc (base_color R) hct hadj hm s]
  have hfour := fixed_lower common earlier (base_color R) hadj (baseNaturalModel common s)
  omega

/-- The first quotient is dual under the original CommonFacts marking,
without assuming either later doubled quotient. -/
theorem markedDualSection (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    Nonempty (MarkedDualSection source common (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R))) := by
  obtain ⟨s⟩ := earlier.natural_section (alpha R) (base_color R)
  let σ := sourceMarking common s
  obtain ⟨f,hf⟩ | ⟨f,hf⟩ := natural_or_dual_of_coordinates
    (modelAction.comp σ.toMonoidHom) common.natural.marking (MulEquiv.refl Space) σ (fun _ _ => rfl)
  · exact (no_natural_coordinates common earlier p s ⟨f,hf⟩).elim
  let q := f.toMonoidHom.comp (coordinates common earlier p s)
  have hdist : (cosetGraph R).dist (p.walk.getVert 6) (alpha R) = 2 := by
    rw [SimpleGraph.dist_comm]
    simpa only [p.center_eq] using p.distance (geometry := geometry) (i := 4) (j := 6) (by decide) (by decide)
  refine ⟨⟨(hatV_le_radius R hdist.le).trans s.local_group,
    Early.Z_le_hatV (base_color R) (by rw [SimpleGraph.dist_comm]; exact hdist), ?_, q,
    f.surjective.comp (coordinates_onto common earlier p s), ?_, ?_⟩⟩
  · simpa only [alpha, stabilizer_m_base] using hatV_normalized R (alpha R) (p.walk.getVert 6)
  · rw [MonoidHom.ker_comp_of_injective _ _ f.injective, coordinates_kernel]
  · intro m x y hy
    have h := coordinates_source_action common earlier p s m x y hy
    have he : coordinates common earlier p s y = modelAction (σ (source.projection m)) (coordinates common earlier p s x) :=
      Multiplicative.toAdd.injective h
    change (f (coordinates common earlier p s y)).toAdd = _
    rw [he]
    exact hf (source.projection m) (coordinates common earlier p s x)
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.FirstDirect
