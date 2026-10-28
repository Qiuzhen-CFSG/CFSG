module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.ElementarySelection
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSmallMovers
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSmallNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowAdjacent
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowRestriction
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.NonsylowImage

/-!
# Source small movers for non-elementary distance-four images

For a non-elementary replacement image, the original radical is Sylow:
otherwise the existing image catalogue makes it elementary. The image
normalizer is a two-group. Maximality of the restricted original Sylow
therefore identifies it with the whole radical normalizer.

The actual full-cover fixed-index bounds identify the unique maximum
small mover with the preimage of the three-transposition subgroup in the
marked Sylow image. Its index in that normalizer is two, its image order
is eight, and its fixed index on either moved cover is four. Small actors
lie in this same mover and commute with it modulo the two-core. The
entire mover acts quadratically. All statements transport through the
literal edge embeddings and retain the central attachment.

These are the source-(5.5)--(5.7) inputs needed for initial selection in
the remaining non-elementary images at distance four. They only require
distance greater than two and do not use the beyond-four exclusion.
The existing private model calculations are reused with their exact
hypotheses and unchanged public boundaries.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.0), (5.4)--(5.8), printed pp.912 and 915--920, used in (5.12),
p.924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation.NormalElementaryQuotient
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Nonelementary
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "S" => Equiv.Perm (Fin 6)
local notation "ρ" => naturalRepresentation (Fin 6)
variable (hne : ¬ IsElementaryAbelian 2
  (d.radical.map (SourceReduction.projection h e hz hn d)))

include e hz hn hne in
theorem radical_normalizer_knownSimple
    (hb : 2 < replacementDistance h d) :
    normalizer (d.radical : Set d.overgroup) =
        (R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup ∧
      (∃ W : Sylow 2 d.overgroup, (W : Subgroup d.overgroup) =
        normalizer (d.radical : Set d.overgroup)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hs : ∃ P : Sylow 2 (L ⊔ R : Subgroup G),
      (P : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R) := by
    by_contra hns
    rcases nonsylow_radical_image_maximal_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hns with ⟨g,hg⟩ | ⟨g,hg⟩
    · apply hne
      rw [hg]
      let : IsElementaryAbelian 2 pointCore :=
        pointCore_elementary
      exact IsElementaryAbelian.map _
    · apply hne
      rw [hg]
      let : IsElementaryAbelian 2 (D 6) := elementary_disjointTranspositions (3 : Fin 4)
      exact IsElementaryAbelian.map _
  obtain ⟨P,hP⟩ := hs
  have hne' : ¬ IsElementaryAbelian 2 (d.radical.map s.projection) := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hnp := NonsylowImage.nonelementary_normalizer_isPGroup
    (d.radical.map s.projection) ((replacement_radical_isPGroup h d).map s.projection) hne'
  have hp : IsPGroup 2 (normalizer (d.radical : Set d.overgroup)) := by
    have hp := hnp.comap_of_ker_isPGroup s.projection (by
      rw [s.projection_kernel]; exact pCore_isPGroup)
    rwa [comap_normalizer_eq_of_surjective _ s.surjective,comap_map_eq,
      s.projection_kernel,sup_eq_left.mpr (replacement_core_le_radical h d)] at hp
  obtain ⟨W,hW⟩ := SylowRestriction.restricted_sylow s P hP
  have hle := SylowRestriction.restricted_normalizes_radical (d := d)
  have he : normalizer (d.radical : Set d.overgroup) =
      (R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup :=
    (W.is_maximal' hp (hW.symm ▸ hle)).trans hW
  exact ⟨he,⟨W,hW.trans he.symm⟩⟩

include e hz hn hne in
theorem normalizer_small_movers_knownSimple
    (hb : 2 < replacementDistance h d) :
    let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
    let N := normalizer (d.radical : Set d.overgroup)
    ∃ u : S,
      N.map s.projection = sylowCarrier.map (MulAut.conj u).toMonoidHom ∧
      let F := N ⊓ ((D 6).map (MulAut.conj u).toMonoidHom).comap s.projection
      SmallMover.Maximal (replacementMoved d) (pCore 2 d.overgroup) N 4 = {F} ∧
      SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) N 4 = F ∧
      F.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom ∧
      (pCore 2 d.overgroup).relIndex F = 8 ∧ F.relIndex N = 2 ∧
      (centralizer (F : Set d.overgroup)).relIndex (replacementMoved d) = 4 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  let N := normalizer (d.radical : Set d.overgroup)
  obtain ⟨_,⟨W,hW⟩⟩ := radical_normalizer_knownSimple hne hb
  let P := W.mapSurjective s.surjective
  obtain ⟨u,hu⟩ := MulAction.exists_smul_eq S sylow P
  have hN : N.map s.projection = sylowCarrier.map (MulAut.conj u).toMonoidHom := by
    have hh := congrArg (fun W : Sylow 2 S => (W : Subgroup S)) hu
    change sylowCarrier.map (MulAut.conj u).toMonoidHom =
      (W : Subgroup d.overgroup).map s.projection at hh
    rw [hW] at hh
    exact hh.symm
  have hk : s.projection.ker ≤ N := by
    rw [s.projection_kernel]
    exact (replacement_core_le_radical h d).trans d.radical.le_normalizer
  have hfix : replacementMoved d ≤ centralizer (s.projection.ker : Set d.overgroup) := by
    rw [s.projection_kernel,←moved_centralizer s]
    exact le_centralizer_iff.mpr le_rfl
  have hbds (A : Subgroup d.overgroup) :
      2 ^ fixedCodim ρ (A.map s.projection) ≤
        (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ∧
      (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤
        2 ^ fixedCodim (coreRepresentation (Fin 6)) (A.map s.projection) := by
    let := replacementMoved_normal h d
    rw [centralizer_index_eq_fixedCodim (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm)]
    have hh := (cover_model s).fixedCodim_bounds (A.map s.projection)
    simp only [Subgroup.map_id] at hh
    exact ⟨Nat.pow_le_pow_right (by decide) hh.1,Nat.pow_le_pow_right (by decide) hh.2⟩
  let F := N ⊓ ((D 6).map (MulAut.conj u).toMonoidHom).comap s.projection
  have hm := SylowSmallMovers.sylow_small_movers N (replacementMoved d) s.projection u hk hfix hN hbds
  dsimp only at hm
  rw [s.projection_kernel] at hm
  have hD : (D 6).map (MulAut.conj u).toMonoidHom ≤ N.map s.projection := by
    rw [hN]
    exact map_mono D_le_sylowCarrier
  have hF : F.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    apply le_antisymm ((map_mono inf_le_right).trans (map_comap_le _ _))
    intro y hy
    obtain ⟨x,hx,rfl⟩ := hD hy
    exact mem_map_of_mem s.projection ⟨hx,hy⟩
  have hkF : s.projection.ker ≤ F := le_inf hk (ker_le_comap _ _)
  have hidx : F.relIndex N = 2 := by
    have hi := relIndex_mul_relIndex s.projection.ker F N hkF inf_le_left
    rw [s.projection_kernel,hm.2.2] at hi
    have hNi : (pCore 2 d.overgroup).relIndex N = 16 := by
      rw [←s.projection_kernel,relIndex_ker,hN,
        card_map_of_injective (MulAut.conj u).injective,card_sylowCarrier]
    rw [hNi] at hi
    omega
  refine ⟨u,hN,hm.1,hm.2.1,hF,hm.2.2,hidx,?_⟩
  have hh := hbds F
  rw [hF,fixedCodim_map_conj,fixedCodim_map_conj,
    fixedCodim_D.2.2.1,fixedCodim_D.2.2.2] at hh
  change (centralizer (F : Set d.overgroup)).relIndex (replacementMoved d) = 4
  norm_num at hh
  omega

include e hz hn hne in
theorem normalizer_small_movers_small_action_knownSimple
    (hb : 2 < replacementDistance h d)
    (A : Subgroup d.overgroup) (hA : A ≤ d.radical)
    (hidx : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2) :
    let J := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup)
      (normalizer (d.radical : Set d.overgroup)) 4
    A ≤ J ∧ ⁅J,A⁆ ≤ pCore 2 d.overgroup := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  let N := normalizer (d.radical : Set d.overgroup)
  let J := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) N 4
  obtain ⟨u,hN,_,hJ,hF,_,_,_⟩ := normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hb
  change J = _ at hJ
  have hJmap : J.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [hJ]
    exact hF
  have hnat : fixedCodim ρ (A.map s.projection) ≤ 1 := by
    let := replacementMoved_normal h d
    rw [centralizer_index_eq_fixedCodim (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm)] at hidx
    have hh := (cover_model s).fixedCodim_bounds (A.map s.projection)
    simp only [Subgroup.map_id] at hh
    exact hh.1.trans ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hidx)
  have hAD := SylowSmallMovers.small_image_centralized _ u
    ((map_mono (hA.trans d.radical.le_normalizer)).trans_eq hN) hnat
  have hAJ : A ≤ J := by
    rw [hJ]
    exact le_inf (hA.trans d.radical.le_normalizer) (map_le_iff_le_comap.mp hAD.1)
  have hmap : (⁅J,A⁆ : Subgroup d.overgroup).map s.projection = ⊥ := by
    rw [map_commutator,hJmap]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact hAD.2
  exact ⟨hAJ,((Subgroup.map_eq_bot_iff _).mp hmap).trans_eq s.projection_kernel⟩

include e hz hn hne in
theorem edge_normalizer_small_movers_knownSimple
    (hb : 2 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    let T := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
    ∃ J : Subgroup (FreeAmalgam d.radical),
      SmallMover.Maximal (U d.radical a) (Q d.radical a) T 4 = {J} ∧
      SmallMover.join (U d.radical a) (Q d.radical a) T 4 = J ∧
      Q d.radical a ≤ J ∧ J ≤ T ∧
      (Q d.radical a).relIndex J = 8 ∧ J.relIndex T = 2 ∧
      (centralizer (J : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = 4 ∧
      ∀ A : Subgroup (FreeAmalgam d.radical), A ≤ Q d.radical t →
        (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤ 2 →
        A ≤ J ∧ ⁅J,A⁆ ≤ Q d.radical a := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let N := normalizer (d.radical : Set d.overgroup)
  let T := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
  obtain ⟨i,hinj,hir,hiR,hiQ,hiU⟩ := SylowAdjacent.edge_coordinates (h := h) hc ha hat
  have hiN : N.map i = T := by
    have hh : (normalizer (d.radical.map i : Set _)).comap i = N := by
      rw [comap_normalizer_eq_of_le_range (map_le_range _ _),
        comap_map_eq_self_of_injective hinj]
    rw [←hh,map_comap_eq,hiR,hir,inf_comm]
  obtain ⟨u,hN,hm,hj,hF,hFi,hNi,hfixed⟩ := normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hb
  let F := N ⊓ ((D 6).map (MulAut.conj u).toMonoidHom).comap s.projection
  have hFm : SmallMover.Maximal (replacementMoved d) (pCore 2 d.overgroup) N 4 = {F} := hm
  have hFj : SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) N 4 = F := hj
  have hQF : pCore 2 d.overgroup ≤ F := by
    rw [←s.projection_kernel]
    exact le_inf ((s.projection_kernel ▸ replacement_core_le_radical h d).trans d.radical.le_normalizer)
      (ker_le_comap _ _)
  refine ⟨F.map i,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hh := SylowSmallMovers.maximal_map_singleton i hinj _ _ _ _ hFm
    rwa [hiU,hiQ,hiN] at hh
  · have hh := SmallMover.join_map i hinj (replacementMoved d) (pCore 2 d.overgroup) N 4
    rw [hFj,hiU,hiQ,hiN] at hh
    exact hh.symm
  · rw [←hiQ]
    exact map_mono hQF
  · change F.map i ≤ T
    rw [←hiN]
    exact map_mono inf_le_left
  · rw [←hiQ,relIndex_map_map_of_injective _ _ hinj]
    exact hFi
  · change (F.map i).relIndex T = 2
    rw [←hiN,relIndex_map_map_of_injective _ _ hinj]
    exact hNi
  · rw [←hiU,SmallMover.centralizer_index_map i hinj]
    exact hfixed
  · intro A hA hidx
    have hAr : A ≤ i.range := hA.trans (hiR ▸ map_le_range i d.radical)
    have hAm : (A.comap i).map i = A := map_comap_eq_self hAr
    have hA₀ : A.comap i ≤ d.radical := by
      have hh := comap_mono (f := i) hA
      rw [←hiR,comap_map_eq_self_of_injective hinj] at hh
      exact hh
    have hidx₀ : (centralizer (A.comap i : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
      rw [←hAm,←hiU,SmallMover.centralizer_index_map i hinj] at hidx
      exact hidx
    have hh := normalizer_small_movers_small_action_knownSimple
      (e := e) (hz := hz) (hn := hn) hne hb (A.comap i) hA₀ hidx₀
    change A.comap i ≤ SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) N 4 ∧
      ⁅SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) N 4,A.comap i⁆ ≤ _ at hh
    rw [hFj] at hh
    have hh₁ := map_mono (f := i) hh.1
    rw [hAm] at hh₁
    have hh₂ := map_mono (f := i) hh.2
    rw [map_commutator,hAm,hiQ] at hh₂
    exact ⟨hh₁,hh₂⟩

include e hz hn hne in
theorem normalizer_small_mover_quadratic_knownSimple
    (hb : 2 < replacementDistance h d) :
    let J := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup)
      (normalizer (d.radical : Set d.overgroup)) 4
    ⁅⁅replacementMoved d,J⁆,J⁆ = ⊥ := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  obtain ⟨u,_,_,hJ,himage,_⟩ := normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hb
  dsimp only
  rw [hJ]
  exact commutator_eq_bot_iff_le_centralizer.mpr
    (SylowAdjacent.cube_actor_commutator_fixed s _ u himage.le)

include e hz hn hne in
theorem edge_small_mover_quadratic_knownSimple
    (hb : 2 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    let T := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
    let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
    ⁅⁅U d.radical a,J⁆,J⁆ = ⊥ := by
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨i,hinj,hir,hiR,hiQ,hiU⟩ := SylowAdjacent.edge_coordinates (h := h) hc ha hat
  let N := normalizer (d.radical : Set d.overgroup)
  have hiN : N.map i = normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a := by
    have hh : (normalizer (d.radical.map i : Set _)).comap i = N := by
      rw [comap_normalizer_eq_of_le_range (map_le_range _ _),comap_map_eq_self_of_injective hinj]
    rw [←hh,map_comap_eq,hiR,hir,inf_comm]
  have hh := congrArg (Subgroup.map i) (normalizer_small_mover_quadratic_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hb)
  dsimp only at hh ⊢
  rw [map_commutator,map_commutator,SmallMover.join_map i hinj,hiU,hiQ,hiN,Subgroup.map_bot] at hh
  exact hh

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Nonelementary
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
