module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.FullSeedBackward
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedLarge
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.PairExclusion
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CoreActor
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CoreParity
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.RestrictedActor
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedLarge
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.FullSeedBackward

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeRadiusPlane


/-!
# Mixed-image generation with the same full endpoint restriction

At distance four, a radical image of order four is the mixed plane: the
order-four offender catalogue and the proved two-transposition exclusion
supply this identification in the original symmetric quotient.

On the natural cover, adjoining the whole endpoint moving subgroup to the
full restriction preserves its controlled commutator and gives image order
four. On the augmentation cover, the mixed plane moves the constant vector,
whereas an involution cannot move an augmentation vector to that constant.
Consequently a restriction preserving the entire critical commutator cannot
have cyclic image. Its image fills the same mixed plane.

Two conjugate mixed planes generate S₆. Lift this equality through the actual
two-core and the graph embedding to obtain an edge kernel generating with
the same controlled full seed. The seed retains its central attachment,
index at most two and exact critical commutator. FullBackward consumes this
generation to eliminate the small backward alternative on both covers.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3)(ii), (5.2)(i) and the generating choice in (5.12)(1)–(2),
printed pp.866–867,913–914,924–926. The internal imports reuse the existing
coordinate and full-seed calculations within this source implementation;
they preserve those modules' public boundaries. No new finite certificate
or equality between the relative normalizer and edge kernel is needed.
-/

public noncomputable section
open Theory.SpecificGroups.SymmetricSix
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags CoreCrossing
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
local notation "S" => Equiv.Perm (Fin 6)
local notation "ρ" => coreRepresentation (Fin 6)

private theorem core_mixed_preserving_large (A W : Subgroup S)
    (g : S) (hA : A = plus.map (MulAut.conj g).toMonoidHom) (hWA : W ≤ A)
    (a : S) (ha : a ∈ W) (hao : orderOf a = 2)
    (hm : subspaceCommutator ρ ⊤ W = subspaceCommutator ρ ⊤ A) :
    4 ≤ Nat.card W := by
  have hc : Nat.card A = 4 := by
    rw [hA,card_map_of_injective (MulAut.conj g).injective,card_plus]
  have hp : IsPGroup 2 W := (IsPGroup.of_card (p := 2) (n := 2) hc).to_le hWA
  by_contra! hs
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hs2 : Nat.card W ≤ 2 := by
    rw [hn] at hs ⊢
    have hn2 : n < 2 := (Nat.pow_lt_pow_iff_right (by decide)).mp hs
    interval_cases n <;> decide
  have he : zpowers a = W := eq_of_le_of_card_ge (zpowers_le.mpr ha) (by
    rw [Nat.card_zpowers,hao]
    exact hs2)
  have hone : oneWord ∈ subspaceCommutator ρ ⊤ A := by
    rw [hA]
    exact CoreActor.one_moved_conjugate plus CoreActor.one_moved_plus g
  rw [←hm,←he,Representation.CyclicFixedRank.commutator_eq_range] at hone
  obtain ⟨v,hv⟩ := hone
  have hsq : a^2=1 := by simpa only [hao] using pow_orderOf_eq_one a
  exact no_constant a hsq v.val v.property (congrArg Subtype.val hv)

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

private theorem cover_mixed_preserving_large
    (hcore : Nat.card (replacementMoved d) = 32)
    (A W : Subgroup d.overgroup) (g : S)
    (hA : A.map s.projection = plus.map (MulAut.conj g).toMonoidHom)
    (hWA : W ≤ A) (a : S) (ha : a ∈ W.map s.projection) (hao : orderOf a = 2)
    (hm : ⁅replacementMoved d,W⁆ = ⁅replacementMoved d,A⁆) :
    4 ≤ Nat.card (W.map s.projection) := by
  rcases cover_model s with ⟨E,_⟩ | ⟨E,hE⟩
  · have hc : Nat.card (replacementMoved d) = 16 := by
      change Nat.card (Additive (replacementMoved d)) = 16
      rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K:=ZMod 2),
        Nat.card_zmod,finrank_natural_even (Fin 6) (by decide)]
      decide
    omega
  · apply core_mixed_preserving_large _ _ g hA (map_mono hWA) a ha hao
    rw [←core_coordinates_moved s E hE W,←core_coordinates_moved s E hE A]
    congr 1
    unfold Representation.NormalElementaryQuotient.commutatorSpace
    rw [hm]

include s in
private theorem mixed_endpoint_image
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : S) (him : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    ∃ v : S, ((Z d.radical z).comap (embedM d.radical)).map s.projection =
      plus.map (MulAut.conj v).toMonoidHom := by
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hat : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hZt : Z d.radical z ≤ Q d.radical (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(replacementGeometry h d).distance_constant _ p.end_color]
    change p.walk.length-1 < replacementDistance h d
    omega
  obtain ⟨v,hv⟩ := MixedLarge.graphImage_le_mixed_of_le_edge s u him.le _ hat _ hZt
  have hcard : 4 ≤ Nat.card (graphImage s (Z d.radical z)) := by
    rw [graphImage_card s _ (hZt.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hat)))]
    exact reverse_critical_image_four_le s hc (replacementDistance_pos h d) p hlarge
  exact ⟨v,eq_of_le_of_card_ge hv (by
    rw [card_map_of_injective (MulAut.conj v).injective,card_plus]
    exact hcard)⟩

include s in
private theorem mixed_full_seed_control
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (u : S) (him : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    ∃ E : Subgroup (FreeAmalgam d.radical),
      Z d.radical (p.walk.getVert 3) ≤ E ∧ E ≤ Z d.radical z ∧
      E.relIndex (Z d.radical z) ≤ 2 ∧
      ⁅Z d.radical (alpha d.radical),E⁆ = ⁅Z d.radical (alpha d.radical),Z d.radical z⁆ ∧
      ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert 2),E⁆ =
        ⁅Z d.radical (alpha d.radical),Z d.radical z⁆ ∧
      4 ≤ Nat.card ((E.comap (embedM d.radical)).map s.projection) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  rcases moved_card s with hnat | hcore
  · obtain ⟨E,hFE,hEZ,hi,_,hcomm,hcontrol⟩ := large_image_full_seed_control s hc hb2 p hlarge
    have hWcontrol := natural_radius_exact_control s hc hnat hb2 p hlarge
    rw [hl] at hFE hcontrol hWcontrol
    have hUZ : U d.radical z ≤ Z d.radical z := DistanceEight.U_le_Z d.radical z
    have hRZe : ⁅Z d.radical (alpha d.radical),Z d.radical z⁆ ≤ Z d.radical z :=
      ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_right).trans hUZ
    let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) z p.end_color
    have hRN : Z d.radical z ≤ normalizer
        ((⁅Z d.radical (alpha d.radical),Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) :=
      ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (centralizer_le hRZe)).trans (Subgroup.centralizer_le_normalizer _)
    let := finite_Z d.radical z
    refine ⟨E ⊔ U d.radical z,hFE.trans le_sup_left,sup_le hEZ hUZ,
      (relIndex_le_of_le_left (show E ≤ E ⊔ U d.radical z from le_sup_left)
        index_ne_zero_of_finite).trans hi,?_,?_,?_⟩
    · exact le_antisymm (commutator_mono le_rfl (sup_le hEZ hUZ))
        (hcomm.ge.trans (commutator_mono le_rfl le_sup_left))
    · apply le_antisymm
      · rw [commutator_comm]
        exact commutator_sup_le_of_relative_normal (Z d.radical z) E (U d.radical z) _
          ⁅Z d.radical (alpha d.radical),Z d.radical z⁆ hRN hEZ hUZ
          (by rw [commutator_comm]; exact hcontrol.le)
          (by rwa [commutator_comm])
      · exact hcontrol.ge.trans (commutator_mono le_rfl le_sup_left)
    · have hUG : U d.radical z ≤ stabilizer d.radical (alpha d.radical) := hUZ.trans
        (critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
          (replacementDistance_pos h d) p.critical)
      have hiU : 4 ≤ Nat.card (graphImage s (U d.radical z)) := by
        rw [graphImage_card s _ hUG]
        exact reverse_critical_moving_image_four_le s hc p hlarge
      exact hiU.trans (card_le_of_le (map_mono (comap_mono
        (show U d.radical z ≤ E ⊔ U d.radical z from le_sup_right))))
  · obtain ⟨E,hFE,hEZ,hi,hcomm,hcontrol,a,ha,hao,_⟩ :=
      large_image_full_seed_even_control s hc hb p hlarge
    refine ⟨E,hFE,hEZ,hi,hcomm,hcontrol,?_⟩
    obtain ⟨v,hv⟩ := mixed_endpoint_image s hc hb2 u him p hlarge
    have hZG : Z d.radical z ≤ (embedM d.radical).range :=
      (critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
        (replacementDistance_pos h d) p.critical).trans_eq (stabilizer_m_base d.radical)
    have hmZ : ((Z d.radical z).comap (embedM d.radical)).map (embedM d.radical) = Z d.radical z :=
      map_comap_eq_self hZG
    have hmE : (E.comap (embedM d.radical)).map (embedM d.radical) = E :=
      map_comap_eq_self (hEZ.trans hZG)
    apply cover_mixed_preserving_large s hcore _ _ v hv (comap_mono hEZ) a ha hao
    apply map_injective (embedM_injective d.radical)
    rw [map_commutator,map_commutator,hmE,hmZ,←hc.U_eq_moved]
    have hat : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
      apply (cosetGraph_adj d.radical _ _).mp
      simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
    have hZt : Z d.radical z ≤ Q d.radical (p.walk.getVert 1) := by
      apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
      rw [SimpleGraph.dist_comm,p.dist_end,(replacementGeometry h d).distance_constant _ p.end_color]
      change p.walk.length-1 < replacementDistance h d
      omega
    rwa [←seed_commutator_eq_moving (h := h) (e := e) (hz := hz) rfl hat E (hEZ.trans hZt),
      ←seed_commutator_eq_moving (h := h) (e := e) (hz := hz) rfl hat (Z d.radical z) hZt]

include s in
private theorem mixed_generating_neighbor (u v : S)
    (him : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom)
    (W : Subgroup (FreeAmalgam d.radical))
    (hWG : W ≤ stabilizer d.radical (alpha d.radical))
    (hWim : (W.comap (embedM d.radical)).map s.projection =
      plus.map (MulAut.conj v).toMonoidHom) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      Q d.radical t ⊔ W = stabilizer d.radical (alpha d.radical) := by
  obtain ⟨k,hk⟩ := MixedLarge.conjugate_generates u v
  rw [←him,←hWim] at hk
  obtain ⟨g,hgk⟩ := s.surjective k
  let A := W.comap (embedM d.radical)
  have hm : (d.radical.map (MulAut.conj g).toMonoidHom).map s.projection =
      (d.radical.map s.projection).map (MulAut.conj k).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change s.projection (g*x*g⁻¹) = k*s.projection x*k⁻¹
    rw [map_mul,map_mul,map_inv,hgk]
  have hQ : (pCore 2 d.overgroup).map (MulAut.conj g).toMonoidHom = pCore 2 d.overgroup :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hker : s.projection.ker ≤ d.radical.map (MulAut.conj g).toMonoidHom := by
    rw [s.projection_kernel,←hQ]
    exact map_mono (replacement_core_le_radical h d)
  have hgen : d.radical.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ := by
    apply map_injective_of_ker_le s.projection (hker.trans le_sup_left) le_top
    rw [Subgroup.map_sup,hm,map_top_of_surjective s.projection s.surjective]
    exact hk
  let f := (embedM d.radical g)⁻¹
  have hf : f ∈ stabilizer d.radical (alpha d.radical) := by
    change f ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have hfix : act d.radical f (alpha d.radical) = alpha d.radical := hf
  refine ⟨act d.radical f (beta d.radical),?_,?_⟩
  · rw [←hfix]
    exact (adjacent_act_iff d.radical f (alpha d.radical) (beta d.radical)).mpr
      (base_adjacent d.radical)
  · have hmapA : A.map (embedM d.radical) = W :=
      map_comap_eq_self (hWG.trans_eq (stabilizer_m_base d.radical))
    have hh := congrArg (Subgroup.map (embedM d.radical)) hgen
    rw [Subgroup.map_sup,hmapA,←MonoidHom.range_eq_map] at hh
    rw [Q_act,Q_beta]
    change _ = stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    have hmapR : (d.radical.map (embedM d.radical)).map (MulAut.conj f⁻¹).toMonoidHom =
        (d.radical.map (MulAut.conj g).toMonoidHom).map (embedM d.radical) := by
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change f⁻¹*embedM d.radical x*(f⁻¹)⁻¹=embedM d.radical (g*x*g⁻¹)
      simp only [f,inv_inv,map_mul,map_inv]
    rw [hmapR]
    exact hh

include s in
/-- In the order-four radical branch, the controlled full endpoint restriction
retains the whole mixed image and generates with an actual edge kernel. -/
theorem four_full_seed_generating_neighbor
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (hcard : Nat.card (d.radical.map s.projection) = 4)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    ∃ E : Subgroup (FreeAmalgam d.radical),
      Z d.radical (p.walk.getVert 3) ≤ E ∧ E ≤ Z d.radical z ∧
      E.relIndex (Z d.radical z) ≤ 2 ∧
      ⁅Z d.radical (alpha d.radical),E⁆ =
        ⁅Z d.radical (alpha d.radical),Z d.radical z⁆ ∧
      ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert 2),E⁆ =
        ⁅Z d.radical (alpha d.radical),Z d.radical z⁆ ∧
      (¬ E ≤ Q d.radical (alpha d.radical)) ∧
      ∃ t, Adjacent d.radical (alpha d.radical) t ∧
        (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical (alpha d.radical)) ⊔ E = stabilizer d.radical (alpha d.radical) ∧
        Q d.radical t ⊔ E = stabilizer d.radical (alpha d.radical) := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨u,him⟩ := PairExclusion.four_image_mixed_knownSimple hb2 (by
    rwa [←SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s])
  rw [←SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at him
  obtain ⟨E,hFE,hEZ,hi,hcomm,hcontrol,hEi⟩ := mixed_full_seed_control s hc hb u him p hlarge
  have hEG : E ≤ stabilizer d.radical (alpha d.radical) := hEZ.trans
    (critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
      (replacementDistance_pos h d) p.critical)
  have hEn : ¬ E ≤ Q d.radical (alpha d.radical) := by
    intro hEQ
    have hker : E.comap (embedM d.radical) ≤ s.projection.ker := by
      rw [s.projection_kernel]
      have hh := comap_mono (f := embedM d.radical) hEQ
      rwa [Q_alpha_comap d.radical (replacement_radical_isPGroup h d)
        (replacement_core_le_radical h d)] at hh
    have he := (Subgroup.map_eq_bot_iff (E.comap (embedM d.radical))).mpr hker
    rw [he,card_bot] at hEi
    omega
  obtain ⟨v,hv⟩ := mixed_endpoint_image s hc hb2 u him p hlarge
  have he : (E.comap (embedM d.radical)).map s.projection =
      plus.map (MulAut.conj v).toMonoidHom :=
    eq_of_le_of_card_ge ((map_mono (comap_mono hEZ)).trans_eq hv) (by
      rw [card_map_of_injective (MulAut.conj v).injective,card_plus]
      exact hEi)
  obtain ⟨t,hat,hgen⟩ := mixed_generating_neighbor s u v him E hEG he
  have hQG : Q d.radical t ≤ stabilizer d.radical (alpha d.radical) :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  refine ⟨E,hFE,hEZ,hi,hcomm,hcontrol,hEn,t,hat,?_,hgen⟩
  apply le_antisymm (sup_le inf_le_right hEG)
  exact hgen.symm.le.trans
    (sup_le_sup_right (le_inf (Q d.radical t).le_normalizer hQG) E)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
