module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSmallSeeds

/-!
# Strict mixed-plane intersections at distance four

The mixed plane has fixed codimension two on both permitted moving covers.
Thus each full component seed has index four over an incident edge seed,
including all central attachments. A strict Baumann slice makes the
intersection of two neighboring component seeds equal their common edge
seed. When the two incident edge kernels generate the component stabilizer,
the compatible triple intersection is fixed by that stabilizer.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the compatible selection and fixed-line argument in (5.12)(1),
printed pp.924--926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- The full vertex seed has index four over any incident edge seed in
 the mixed-plane branch, on both the natural and augmentation covers. -/
theorem mixed_edge_seed_index (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    (Z d.radical t).relIndex (Z d.radical a) = 4 := by
  have hbase : (Z d.radical (beta d.radical)).relIndex
      (Z d.radical (alpha d.radical)) = 4 := by
    let := replacementMoved_normal h d
    have hfix : replacementMoved d ⊓ omegaCenter d.radical =
        replacementMoved d ⊓ centralizer (d.radical : Set d.overgroup) := by
      apply le_antisymm
      · exact inf_le_inf_left _ (fun _ hx => (mem_omegaCenter_iff.mp hx).2.2)
      · intro v hv
        exact ⟨hv.1,mem_omegaCenter_iff.mpr ⟨replacement_core_le_radical h d
          ((mem_omegaCenterIn_iff _ _).mp (replacementMoved_le_omegaCenter h d hv.1)).1,
          elemPow_eq_one_of_isElementaryAbelian v hv.1,hv.2⟩⟩
    have hcodim : Representation.BinaryOffender.fixedCodim (coverAction s)
        (d.radical.map s.projection) = 2 := by
      rcases cover_model s with ⟨E,hE⟩ | ⟨E,hE⟩
      · have hh := Representation.BinaryOffender.fixedCodim_map_equivariant
          (coverAction s) (naturalRepresentation (Fin 6)) (MonoidHom.id (Equiv.Perm (Fin 6))) E hE
          (d.radical.map s.projection)
        rw [hh,map_id,hfull,Representation.BinaryOffender.fixedCodim_map_conj]
        exact fixedCodim_plus.2.2.2
      · have hh := Representation.BinaryOffender.fixedCodim_map_equivariant
          (coverAction s) (coreRepresentation (Fin 6)) (MonoidHom.id (Equiv.Perm (Fin 6))) E hE
          (d.radical.map s.projection)
        rw [hh,map_id,hfull,Representation.BinaryOffender.fixedCodim_map_conj]
        exact fixedCodim_plus.2.2.1
    have hindex : (omegaCenter d.radical).relIndex (replacementMoved d) = 4 := by
      rw [←inf_relIndex_right,inf_comm,hfix,inf_comm,inf_relIndex_right,
        NormalElementaryQuotient.centralizer_index_eq_fixedCodim
          (replacementMoved d) s.projection s.surjective
          (s.projection_kernel.trans (moved_centralizer s).symm)]
      change 2 ^ Representation.BinaryOffender.fixedCodim (coverAction s)
        (d.radical.map s.projection) = 4
      rw [hcodim]
      rfl
    have hseed : Z d.radical (beta d.radical) = (omegaCenter d.radical).map (embedM d.radical) := by
      rw [Z,if_neg (by exact Bool.noConfusion : color d.radical (beta d.radical) ≠ false),
        edgeOmega,Q_beta,omegaCenter_map _ _ (embedM_injective d.radical)]
    rw [hseed,ChapterC.NaturalSixControl.SymplecticSeed.Z_eq_seedHull,
      relIndex_map_map_of_injective _ _ (embedM_injective d.radical),
      DistanceTwo.CentralLayer.seedHull_eq_moved_sup_seed h e hz d,
      relIndex_sup_of_normalizes _ _ (show omegaCenter d.radical ≤
        normalizer (replacementMoved d : Set d.overgroup) from le_normalizer_of_normal)]
    exact hindex
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    have he := relIndex_map_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
      (Z d.radical (beta d.radical)) (Z d.radical (alpha d.radical))
      (MulAut.conj g⁻¹).injective
    rw [←Z_act,←Z_act] at he
    simp only [alpha,beta,act_mVertex,act_hVertex,one_mul] at he
    exact he.trans hbase
  · rw [hg.1] at ha
    cases ha

include s in
theorem mixed_strict_seed_intersection_eq_edge
    (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) :
    Z d.radical a ⊓ Z d.radical c = Z d.radical t := by
  have hc : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [ha] at h1
    cases ht : color d.radical t <;> cases hcc : color d.radical c <;> simp_all
  let W := Z d.radical a ⊓ Z d.radical c
  have hTW : Z d.radical t ≤ W :=
    le_inf (adjacent_Z_le d.radical ha hat) (adjacent_Z_le d.radical hc hct)
  have hindex : (Z d.radical t).relIndex (Z d.radical c) = 4 :=
    mixed_edge_seed_index s u hfull hc hct
  let := finite_Z d.radical c
  let : Finite (U d.radical c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical c)) (inclusion_injective _)
  have hWB : W ≤ B d.radical a ((replacementGeometry h d).Z_normal _) :=
    inf_le_left.trans (Escape.EdgeTransfer.Z_le_B hb a ha)
  have hWi : 2 < W.relIndex (Z d.radical c) :=
    hstrict.trans_le ((relIndex_le_of_le_left hWB index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical c) index_ne_zero_of_finite))
  have hm := relIndex_mul_relIndex (Z d.radical t) W (Z d.radical c) hTW inf_le_right
  rw [hindex] at hm
  have hpos : 0 < (Z d.radical t).relIndex W :=
    Nat.pos_of_ne_zero (by intro he; rw [he,zero_mul] at hm; omega)
  have hone : (Z d.radical t).relIndex W = 1 := by nlinarith
  exact le_antisymm (relIndex_eq_one.mp hone) hTW

include s in
theorem mixed_strict_compatible_triple_central
    (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom)
    {a v c b t : Vertex d.radical} (ha : color d.radical a = false)
    (hab : Adjacent d.radical a b) (hvb : Adjacent d.radical v b)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hstrict0 : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical v))
    (hstrict1 : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c))
    (hgen : Q d.radical b ⊔ Q d.radical t = stabilizer d.radical a) :
    Z d.radical v ⊓ Z d.radical a ⊓ Z d.radical c ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  have h0 := mixed_strict_seed_intersection_eq_edge s hb u hfull ha hab hvb hstrict0
  have h1 := mixed_strict_seed_intersection_eq_edge s hb u hfull ha hat hct hstrict1
  have hcent {w : Vertex d.radical} (haw : Adjacent d.radical a w) :
      Z d.radical w ≤ centralizer (Q d.radical w : Set (FreeAmalgam d.radical)) := by
    have hw : color d.radical w = true := by
      have hh := adjacent_color_ne d.radical haw
      rw [ha] at hh
      cases he : color d.radical w <;> simp_all
    intro x hx
    rw [Z,if_neg (by simp [hw])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  apply le_centralizer_iff.mpr
  rw [←hgen]
  apply sup_le
  · apply le_centralizer_iff.mp
    exact (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left)).trans
      (h0.le.trans (hcent hab))
  · apply le_centralizer_iff.mp
    exact (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans
      (h1.le.trans (hcent hat))

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
