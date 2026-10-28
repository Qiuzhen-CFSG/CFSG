module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MidpointDerivedSaturation
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.Native

/-!
# A large slice and the whole-core derived obstruction at distance four

For the literal full point-core image, two consecutive small slices on one
critical path are impossible. If a given path has a small first slice, extend
that same path by two edges and discard its first two edges. At distance four
the old endpoint is exactly the new midpoint, so the large second slice is
now the first slice of the extended path. Transport the whole path to the
original base vertex. This constructs a large slice without choosing the two
bounds on independent paths.

The resulting path supplies the hypothesis of the selected-kernel derived
calculation and its normal-subgroup saturation. Consequently the entire
moving cover lies in the derived subgroup of the whole replacement two-core,
without a slice or path hypothesis. The already proved natural-cover exclusion
forces this cover to have order thirty-two. Literal vertex coordinates and
the replacement inclusion give the same containment and lower order bound
at every original vertex and in the original ambient two-core.

These are lower bounds for the whole two-core's derived subgroup. They do not
bound the derived subgroup of the residual core [Q,Ltilde] from above, or
supply the endpoint estimate needed in MS93 (5.12). That configuration and
the other radical-image branches remain to be excluded.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (2.2)(v), (3.10) and (5.12), printed pp.856--857, 879--881 and
924--927. This combines the existing literal path extension and
consecutive-slice obstruction; it does not assert completion of (5.12).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement Pointwise IsMulCommutative
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- One original critical path has a large forward slice. If the first
path's slice is small, the same path's two-edge extension supplies it. -/
theorem full_point_four_exists_large_slice_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom) :
    ∃ a', ∃ p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a',
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨a',⟨p⟩⟩ := CriticalPath.exists_from (R := d.radical)
    (geometry := replacementGeometry h d) (a := alpha d.radical) rfl
  by_cases hlarge : 2 < (B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (p.walk.getVert 2))
  · exact ⟨a',p,hlarge⟩
  have hpre : 2 < (B d.radical (p.walk.getVert 2)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical a') := by
    by_contra hn
    exact consecutive_small_slices_false_knownSimple hb u hfull p
      (by omega) (by omega)
  obtain ⟨z,q,_,_,hq⟩ := (full_point_forward_path_knownSimple hb2 u hfull p).2.2
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hq2 : q.walk.getVert 2 = a' := by simpa only [hql,Nat.reduceSub] using hq
  have hcol : color d.radical (p.walk.getVert 2) = false := q.start_color
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical hcol
  have hbase : act d.radical g⁻¹ (p.walk.getVert 2) = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hlarg : 2 < (B d.radical (act d.radical g⁻¹ (p.walk.getVert 2))
      ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical ((actWalk d.radical g⁻¹ q.walk).getVert 2)) := by
    rw [actWalk_getVert,Escape.PairingControl.FirstPairing.B_act hb2 g⁻¹ _ hcol,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective,hq2]
    exact hpre
  have hex : ∃ r : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g⁻¹ (p.walk.getVert 2)) (act d.radical g⁻¹ z),
      2 < (B d.radical (act d.radical g⁻¹ (p.walk.getVert 2))
        ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (r.walk.getVert 2)) :=
    ⟨q.act g⁻¹,hlarg⟩
  rw [hbase] at hex
  obtain ⟨r,hr⟩ := hex
  exact ⟨_,r,hr⟩

/-- At distance four with full point-core image, the order-thirty-two
moving cover lies in the derived subgroup of the whole replacement core.
No path or large-slice premise remains. -/
theorem full_point_four_replacement_derived_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom) :
    replacementMoved d ≤ ⁅pCore 2 d.overgroup,pCore 2 d.overgroup⁆ ∧
      Nat.card (replacementMoved d) = 32 ∧
      32 ≤ Nat.card (⁅pCore 2 d.overgroup,pCore 2 d.overgroup⁆ : Subgroup d.overgroup) := by
  obtain ⟨a',p,hlarge⟩ := full_point_four_exists_large_slice_knownSimple hb u hfull
  have hle := (full_point_four_large_slice_replacement_derived_knownSimple hb u hfull p hlarge).1
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hf : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hc : Nat.card (replacementMoved d) = 32 := by
    rcases moved_card s with hc | hc
    · have he := distance_eq_two_of_natural_full_point s hc u hf
      omega
    · exact hc
  refine ⟨hle,hc,?_⟩
  have hh := card_le_of_le hle
  rwa [hc] at hh

/-- The full moving cover lies in the whole core's derived subgroup at
every original vertex, through its literal replacement coordinates. -/
theorem full_point_four_vertex_derived_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    (a : Vertex d.radical) (ha : color d.radical a = false) :
    U d.radical a ≤ ⁅Q d.radical a,Q d.radical a⁆ ∧
      Nat.card (U d.radical a) = 32 ∧
      32 ≤ Nat.card (⁅Q d.radical a,Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) := by
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a ha
  obtain ⟨hle,hU,hcard⟩ := full_point_four_replacement_derived_knownSimple hb u hfull
  have hm := map_mono (f := i) hle
  rw [map_commutator,hiQ,hiU] at hm
  refine ⟨hm,?_,?_⟩
  · rw [←hiU,card_map_of_injective hi,hU]
  · rw [←hiQ,←map_commutator,card_map_of_injective hi]
    exact hcard

/-- The actual replacement inclusion puts the original moved layer in
the derived subgroup of the original ambient two-core, retaining the
original nonsylow radical and the order-thirty-two central attachment. -/
theorem full_point_four_initial_derived_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom) :
    initialMoved L R ≤ ⁅pCore 2 (L ⊔ R : Subgroup G),pCore 2 (L ⊔ R : Subgroup G)⁆ ∧
      Nat.card (initialMoved L R) = 32 ∧
      32 ≤ Nat.card (⁅pCore 2 (L ⊔ R : Subgroup G),pCore 2 (L ⊔ R : Subgroup G)⁆ :
        Subgroup (L ⊔ R : Subgroup G)) := by
  obtain ⟨hle,hU,_⟩ := full_point_four_replacement_derived_knownSimple hb u hfull
  have hh := map_mono (f := d.overgroup.subtype) hle
  rw [replacementMoved_map h d,map_commutator] at hh
  have hcore : (pCore 2 d.overgroup).map d.overgroup.subtype ≤ pCore 2 (L ⊔ R : Subgroup G) := by
    rw [replacement_core h d]
    exact map_comap_le _ _
  have hle' := hh.trans (commutator_mono hcore hcore)
  have hU' : Nat.card (initialMoved L R) = 32 := by
    rw [←replacementMoved_map h d,card_map_of_injective d.overgroup.subtype_injective,hU]
  refine ⟨hle',hU',?_⟩
  have hh := card_le_of_le hle'
  rwa [hU'] at hh

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
