module
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.OmegaExtension
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowAdjacent
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.AugmentationFixedSmallRadical
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeRadiusPlane

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.AugmentationFixedElementary
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenEqual
/-!
# Reciprocal cores in the order-sixteen radical image

The controlled backward transporter agrees on the entire incident edge core.
It therefore transports the original midpoint core's quadratic action to the
selected backward core. The large backward path gives the reciprocal
quadratic action. Each core lies in the opposite edge small mover.

If those movers differ, their intersection has index four in the edge core.
The large critical image already has order at least four, so it fills the
midpoint-core image. Thus the whole midpoint movement equals the critical
commutator. Edge normality and the selected complementary actor make this
small commutator residual-fixed; the hatted seed then captures the full
radius. Consequently failure of full-radius fixedness in this actual
selection forces the two small movers to coincide.

The literal radical projection, both moving covers, full central attachments
and controlled transporters are retained. The common-mover comparison is a
separate remaining part of the order-thirty-two-cover branch.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.5), (5.12)(2), printed pp.917,925.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.GroupTheory Representation.NormalElementaryQuotient
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
local notation "S" => Equiv.Perm (Fin 6)

include e hz hn in
private theorem sixteen_normal_quadratic_le_mover
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16) (A : Subgroup d.overgroup)
    (hA : A ≤ normalizer (d.radical : Set d.overgroup))
    (hnA : normalizer (d.radical : Set d.overgroup) ≤ normalizer (A : Set d.overgroup))
    (hquad : ⁅⁅replacementMoved d,A⁆,A⁆ = ⊥) :
    A ≤ SmallMover.join (replacementMoved d) (pCore 2 d.overgroup)
      (normalizer (d.radical : Set d.overgroup)) 4 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  obtain ⟨u,hN,_,hJ,_,_,_,_⟩ := Nonelementary.normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) (SixteenUnequal.sixteen_nonelementary hcard) hb
  let f := (MulAut.conj u⁻¹).toMonoidHom
  have back (B : Subgroup S) : (B.map (MulAut.conj u).toMonoidHom).map f = B := by
    rw [map_map]
    have he : f.comp (MulAut.conj u).toMonoidHom = MonoidHom.id S := by
      ext x
      simp [f]
    rw [he,map_id]
  have hqu : QuadraticPointCore.Quadratic (A.map s.projection) :=
    image_quadratic_of_commutator s A (commutator_eq_bot_iff_le_centralizer.mp hquad)
  have hq : QuadraticPointCore.Quadratic ((A.map s.projection).map f) :=
    QuadraticPointCore.quadratic_conjugate _ hqu u⁻¹
  let : IsElementaryAbelian 2 ((A.map s.projection).map f) :=
    elementary_of_faithful_quadratic (naturalRepresentation (Fin 6))
      (naturalRepresentation_injective (Fin 6) (by decide)) _ hq
  have hle : (A.map s.projection).map f ≤ sylowCarrier := by
    have hh := map_mono (f := f) (map_mono (f := s.projection) hA)
    rw [hN,back] at hh
    exact hh
  have hnorm : sylowCarrier ≤ normalizer (((A.map s.projection).map f : Subgroup S) : Set S) := by
    have hh := (map_mono (f := s.projection) hnA).trans (le_normalizer_map s.projection)
    have hh := (map_mono (f := f) hh).trans (le_normalizer_map f)
    rwa [hN,back] at hh
  have hD := QuadraticSylow.normal_quadratic_le_cube _ hle hnorm hq
  have him : A.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    apply (map_le_map_iff_of_injective (f := f) (MulAut.conj u⁻¹).injective).mp
    rwa [back]
  rw [hJ]
  exact le_inf hA (map_le_iff_le_comap.mp him)


include e hz hn in
private theorem sixteen_edge_normal_quadratic_le_mover
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (A : Subgroup (FreeAmalgam d.radical))
    (hA : A ≤ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a)
    (hnA : normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a ≤
      normalizer (A : Set (FreeAmalgam d.radical)))
    (hquad : ⁅⁅U d.radical a,A⁆,A⁆ = ⊥) :
    A ≤ SmallMover.join (U d.radical a) (Q d.radical a)
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a) 4 := by
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨i,hinj,hir,hiR,hiQ,hiU⟩ := SylowAdjacent.edge_coordinates (h := h) hc ha hat
  let N := normalizer (d.radical : Set d.overgroup)
  let T := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
  have hiN : N.map i = T := by
    have hh : (normalizer (d.radical.map i : Set _)).comap i = N := by
      rw [comap_normalizer_eq_of_le_range (map_le_range _ _),comap_map_eq_self_of_injective hinj]
    rw [←hh,map_comap_eq,hiR,hir,inf_comm]
  have hAm : (A.comap i).map i = A := map_comap_eq_self ((hA.trans inf_le_right).trans_eq hir.symm)
  have hA₀ : A.comap i ≤ N := by
    have hh := comap_mono (f := i) hA
    change A.comap i ≤ T.comap i at hh
    rw [←hiN,comap_map_eq_self_of_injective hinj] at hh
    exact hh
  have hn₀ : N ≤ normalizer (A.comap i : Set d.overgroup) := by
    intro x hx
    have hix : i x ∈ T := hiN ▸ mem_map_of_mem i hx
    exact le_normalizer_comap i (hnA hix)
  have hq₀ : ⁅⁅replacementMoved d,A.comap i⁆,A.comap i⁆ = ⊥ := by
    apply (map_injective hinj)
    rw [map_commutator,map_commutator,hiU,hAm,hquad,Subgroup.map_bot]
  have hh := map_mono (f := i) (sixteen_normal_quadratic_le_mover
    (e := e) (hz := hz) (hn := hn) hb hcard _ hA₀ hn₀ hq₀)
  rwa [hAm,SmallMover.join_map i hinj,hiU,hiQ,hiN] at hh

include s in
private theorem controlled_midpoint_core_quadratic
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical)))
    {t c : Vertex d.radical}
    (htransport : ∃ x ∈ stabilizer d.radical (alpha d.radical),
      act d.radical x (p.walk.getVert 1) = t ∧
      ∃ k ∈ stabilizer d.radical t, c = act d.radical k (act d.radical x (p.walk.getVert 2)) ∧
      ∃ g ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical (alpha d.radical),
        ∀ v ∈ Q d.radical t, (MulAut.conj k⁻¹) v = (MulAut.conj g) v) :
    ⁅⁅Z d.radical (alpha d.radical),Q d.radical c⁆,Q d.radical c⁆ = ⊥ := by
  obtain ⟨x,hx,hxt,k,hk,rfl,g,hg,hagree⟩ := htransport
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hm1 : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have h1 : color d.radical (p.walk.getVert 1) = true := by
    have ha1 : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
      apply (cosetGraph_adj d.radical _ _).mp
      simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
    have hh := adjacent_color_ne d.radical ha1
    rw [p.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hmQ : Q d.radical (act d.radical x (p.walk.getVert 2)) ≤ Q d.radical t := by
    rw [←hxt,Q_act,Q_act]
    exact map_mono (Q_le_adjacent_h d.radical h1 hm1)
  have hQ : Q d.radical (act d.radical k (act d.radical x (p.walk.getVert 2))) =
      (Q d.radical (act d.radical x (p.walk.getVert 2))).map (MulAut.conj g).toMonoidHom := by
    rw [Q_act]
    ext y
    constructor <;> rintro ⟨v,hv,rfl⟩
    · exact ⟨v,hv,(hagree v (hmQ hv)).symm⟩
    · exact ⟨v,hv,hagree v (hmQ hv)⟩
  have hxZ : (Z d.radical (alpha d.radical)).map (MulAut.conj x⁻¹).toMonoidHom =
      Z d.radical (alpha d.radical) :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized _ _ ((stabilizer d.radical _).inv_mem hx))
  have hgZ : (Z d.radical (alpha d.radical)).map (MulAut.conj g).toMonoidHom =
      Z d.radical (alpha d.radical) :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized _ _ hg.2)
  have hquad : ⁅⁅Z d.radical (alpha d.radical),Q d.radical (p.walk.getVert 2)⁆,
      Q d.radical (p.walk.getVert 2)⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (large_midpoint_core_quadratic s hc hb p hlarge)
  have hqx := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hquad
  rw [map_commutator,map_commutator,hxZ,←Q_act,Subgroup.map_bot] at hqx
  have hqg := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hqx
  rwa [map_commutator,map_commutator,hgZ,←hQ,Subgroup.map_bot] at hqg

include e hz hn in
private theorem sixteen_adjacent_core_le_mover
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a c t : Vertex d.radical} (hc : color d.radical c = false)
    (hct : Adjacent d.radical c t) (hat : Adjacent d.radical a t)
    (hquad : ⁅⁅U d.radical c,Q d.radical a⁆,Q d.radical a⁆ = ⊥) :
    Q d.radical a ≤ SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 := by
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [hc] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard hc hct
  have hAT : Q d.radical a ≤ Q d.radical t := Q_le_adjacent_h d.radical ht hat
  have hnA : Q d.radical t ≤ normalizer (Q d.radical a : Set (FreeAmalgam d.radical)) :=
    (show Q d.radical t ≤ stabilizer d.radical a from
      fun _ hx => hx.2 _ (adjacent_symm d.radical hat)).trans (Q_normalized d.radical a)
  have hh := sixteen_edge_normal_quadratic_le_mover (e := e) (hz := hz) (hn := hn)
    hb hcard hc hct (Q d.radical a) (hT.symm ▸ hAT) (hT.symm ▸ hnA) hquad
  rwa [hT] at hh

include s in
private theorem sixteen_unequal_large_midpoint_movement_eq
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {c z : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical c))
    (hquad : ⁅⁅U d.radical (q.walk.getVert 2),Q d.radical c⁆,Q d.radical c⁆ = ⊥)
    (hne : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical (q.walk.getVert 1)) 4 ≠
      SmallMover.join (U d.radical (q.walk.getVert 2)) (Q d.radical (q.walk.getVert 2))
        (Q d.radical (q.walk.getVert 1)) 4) :
    ⁅Z d.radical c,Q d.radical (q.walk.getVert 2)⁆ = ⁅Z d.radical c,Z d.radical z⁆ := by
  let a := q.walk.getVert 2
  let t := q.walk.getVert 1
  let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
  let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
  have hl : q.walk.length = 4 := q.length_eq_b.trans hb
  have hb2 : 2 < replacementDistance h d := by omega
  have hct : Adjacent d.radical c t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using q.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent d.radical a t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [q.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have ha : color d.radical a = false := by
    have hh := adjacent_color_ne d.radical hat
    rw [ht] at hh
    exact Bool.eq_false_of_not_eq_true hh
  obtain ⟨hQaJ,hJT,hJi,hJidx,hJN,_⟩ := SixteenUnequal.sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 hcard ha hat
  obtain ⟨hQcE,hET,hEi,hEidx,hEN,_⟩ := SixteenUnequal.sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 hcard q.start_color hct
  have hQaE : Q d.radical a ≤ E := sixteen_adjacent_core_le_mover
    (e := e) (hz := hz) (hn := hn) hb2 hcard q.start_color hct hat
    (commutator_eq_bot_iff_le_centralizer.mpr
      ((commutator_mono (DistanceEight.U_le_Z d.radical c) le_rfl).trans
        (large_midpoint_core_quadratic s hc hb q hlarge)))
  have hQcJ : Q d.radical c ≤ J := sixteen_adjacent_core_le_mover
    (e := e) (hz := hz) (hn := hn) hb2 hcard ha hat hct hquad
  have hQcI : Q d.radical c ≤ J ⊓ E := le_inf hQcJ hQcE
  have hQaI : Q d.radical a ≤ J ⊓ E := le_inf hQaJ hQaE
  let := finite_stabilizer d.radical c
  let : Finite (Q d.radical t) := Finite.of_injective (inclusion
    (show Q d.radical t ≤ stabilizer d.radical c from
      fun _ hx => hx.2 _ (adjacent_symm d.radical hct))) (inclusion_injective _)
  have hpair := SylowKernelPair.two_hyperplanes (Q d.radical t) J E hJT hET hJidx hEidx hne.symm
  have hIidx : (Q d.radical c).relIndex (J ⊓ E) = 4 := by
    have hmul := relIndex_mul_relIndex (Q d.radical c) (J ⊓ E) (Q d.radical t)
      hQcI (inf_le_left.trans hJT)
    have hmul' := relIndex_mul_relIndex (Q d.radical c) E (Q d.radical t) hQcE hET
    rw [hpair.2] at hmul
    rw [hEi,hEidx] at hmul'
    omega
  have hidx : (Q d.radical c).relIndex (Q d.radical a) ≤ 4 := by
    rw [←hIidx]
    exact relIndex_le_of_le_right hQaI (by rw [hIidx]; decide)
  have hZA : Z d.radical z ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z q.end_color)
    rw [(replacementGeometry h d).distance_constant _ q.end_color,SimpleGraph.dist_comm,q.dist_end,hl]
    exact hb2
  have hreverse := reverse_critical_image_four_le s hc (replacementDistance_pos h d) q hlarge
  have hnA : Q d.radical a ≤ normalizer (Q d.radical c : Set (FreeAmalgam d.radical)) :=
    ((Q_le_adjacent_h d.radical ht hat).trans
      (show Q d.radical t ≤ stabilizer d.radical c from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hct))).trans (Q_normalized d.radical c)
  have hjoin : Q d.radical c ⊔ Z d.radical z = Q d.radical c ⊔ Q d.radical a := by
    have hinc : Q d.radical c ⊔ Z d.radical z ≤ Q d.radical c ⊔ Q d.radical a :=
      sup_le_sup_left hZA _
    have hmul := relIndex_mul_relIndex (Q d.radical c) (Q d.radical c ⊔ Z d.radical z)
      (Q d.radical c ⊔ Q d.radical a) le_sup_left hinc
    rw [core_join_relIndex _ _ (hZA.trans hnA),core_join_relIndex _ _ hnA] at hmul
    let : Finite (Q d.radical c ⊔ Q d.radical a : Subgroup (FreeAmalgam d.radical)) :=
      Finite.of_injective (inclusion (sup_le (hQcE.trans hET) (hQaJ.trans hJT)))
        (inclusion_injective _)
    have hp : 0 < (Q d.radical c ⊔ Z d.radical z).relIndex (Q d.radical c ⊔ Q d.radical a) :=
      Nat.pos_of_ne_zero index_ne_zero_of_finite
    apply le_antisymm hinc
    apply relIndex_eq_one.mp
    nlinarith
  have hcentral : Z d.radical c ≤ centralizer (Q d.radical c : Set (FreeAmalgam d.radical)) :=
    commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical c q.start_color)
  have hQaGc : Q d.radical a ≤ stabilizer d.radical c :=
    (Q_le_adjacent_h d.radical ht hat).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have comm_eq (A : Subgroup (FreeAmalgam d.radical))
      (hAG : A ≤ stabilizer d.radical c) :
      ⁅Z d.radical c,Q d.radical c ⊔ A⁆ = ⁅Z d.radical c,A⁆ := by
    have hcomZ : ⁅Z d.radical c,A⁆ ≤ Z d.radical c :=
      le_normalizer_iff_commutator_le_left.mp (hAG.trans (Z_normalized d.radical c))
    have hN : Q d.radical c ⊔ A ≤ normalizer ((⁅Z d.radical c,A⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) :=
      sup_le (((le_centralizer_iff.mp hcentral).trans (centralizer_le hcomZ)).trans
        (Subgroup.centralizer_le_normalizer _)) (normalizer_commutator_ge_right _ _)
    apply le_antisymm ?_ (commutator_mono le_rfl le_sup_right)
    rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal (Q d.radical c ⊔ A) _ _ _ _ hN
      le_sup_left le_sup_right
      ((commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hcentral)).le.trans bot_le)
      (commutator_comm A (Z d.radical c)).le
  have heq := comm_eq (Q d.radical a) hQaGc
  have heq' := comm_eq (Z d.radical z) (hZA.trans hQaGc)
  rw [←heq,←hjoin,heq']

include s in
/-- Reciprocal quadratic cores and unequal edge movers make the entire midpoint
movement equal the critical commutator. The selected complementary actor then
puts that commutator in the midpoint's residual fixed core. -/
theorem sixteen_reciprocal_unequal_critical_fixed
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {c z : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical c))
    (hquad : ⁅⁅U d.radical (q.walk.getVert 2),Q d.radical c⁆,Q d.radical c⁆ = ⊥)
    (hne : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical (q.walk.getVert 1)) 4 ≠
      SmallMover.join (U d.radical (q.walk.getVert 2)) (Q d.radical (q.walk.getVert 2))
        (Q d.radical (q.walk.getVert 1)) 4)
    (W : Subgroup (FreeAmalgam d.radical))
    (hgen : Q d.radical (q.walk.getVert 1) ⊔ W = stabilizer d.radical (q.walk.getVert 2))
    (hfix : ⁅Z d.radical c,Z d.radical z⁆ ≤ centralizer (W : Set (FreeAmalgam d.radical))) :
    ⁅Z d.radical c,Z d.radical z⁆ ≤ fixedCore d.radical (q.walk.getVert 2) := by
  let a := q.walk.getVert 2
  let D := ⁅Z d.radical c,Z d.radical z⁆
  have heq := sixteen_unequal_large_midpoint_movement_eq s hc hb hcard q hlarge hquad hne
  have hdata := large_midpoint_movement s hc hb q hlarge
  rw [heq] at hdata
  have hDcard := large_midpoint_movement_card s hc hb q hlarge
  rw [heq] at hDcard
  have hGN : stabilizer d.radical a ≤ normalizer (D : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    exact sup_le hdata.2.2.1 ((le_centralizer_iff.mp hfix).trans (Subgroup.centralizer_le_normalizer _))
  have hl : q.walk.length = 4 := q.length_eq_b.trans hb
  have ha : color d.radical a = false := (q.vertex_color (by omega)).mpr (by decide)
  exact small_core_residual_fixed_knownSimple (h := h) (e := e) ha D
    (hdata.2.1.trans (omegaCenter_le _)) ((Ltilde_le_stabilizer _).trans hGN) hDcard

include s in
/-- Fixedness of the actual large backward critical commutator captures the
full radius, using its strict Baumann slice and restricted hatted seed. -/
theorem large_backward_critical_fixed_radius
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {z c m : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical)))
    (q : CriticalPath d.radical (replacementGeometry h d) c m)
    (hq2 : q.walk.getVert 2 = alpha d.radical)
    (hback : 4 ≤ (Q d.radical m).relIndex (Z d.radical c))
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c))
    (hfixed : ⁅Z d.radical c,Z d.radical m⁆ ≤ fixedCore d.radical (alpha d.radical)) :
    ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical) := by
  obtain ⟨E,_hFE,hEZ,hiE,hEQ⟩ := critical_hatted_seed_midpoint_control s hc hb q hback
  rw [hq2] at hEQ
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hEV : E ≤ V d.radical (alpha d.radical) := hEZ.trans
    ((Z_le_localZSpan d.radical c _).trans (localZSpan_le_V d.radical (by
      rw [←hq2,q.dist_start (by omega)])))
  have hEB : ¬ E ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hbad
    let := finite_Z d.radical c
    let : Finite (U d.radical c) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z d.radical c)) (inclusion_injective _)
    have hh := (relIndex_le_of_le_left (inf_le_left.trans hbad)
      (L := U d.radical c) index_ne_zero_of_finite).trans hiE
    omega
  exact restricted_seed_radius_core_fixed s hc hb p hlarge E hEV hEB (hEQ.le.trans hfixed)

include e hz hn in
/-- In the actual controlled backward selection, failure of full-radius
fixedness forces the two edge small movers to coincide. The core transport
uses agreement on the whole edge kernel, preserving the original path. -/
theorem sixteen_selected_backward_movers_eq_of_radius_not_fixed_knownSimple
    (hb : replacementDistance h d = 4)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {z t c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical)))
    (W : Subgroup (FreeAmalgam d.radical))
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq1 : q.walk.getVert 1 = t) (hq2 : q.walk.getVert 2 = alpha d.radical)
    (hback : 4 ≤ (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c))
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c))
    (hgen : Q d.radical t ⊔ W = stabilizer d.radical (alpha d.radical))
    (hfix : ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆ ≤
      centralizer (W : Set (FreeAmalgam d.radical)))
    (htransport : ∃ x ∈ stabilizer d.radical (alpha d.radical),
      act d.radical x (p.walk.getVert 1) = t ∧
      ∃ k ∈ stabilizer d.radical t, c = act d.radical k (act d.radical x (p.walk.getVert 2)) ∧
      ∃ g ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical (alpha d.radical),
        ∀ v ∈ Q d.radical t, (MulAut.conj k⁻¹) v = (MulAut.conj g) v)
    (hnot : ¬ ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical)) :
    SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 =
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical t) 4 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  by_contra hne
  apply hnot
  have hquad := controlled_midpoint_core_quadratic s hc hb p hlarge htransport
  have hquadU : ⁅⁅U d.radical (q.walk.getVert 2),Q d.radical c⁆,Q d.radical c⁆ = ⊥ := by
    rw [hq2]
    exact bot_unique ((commutator_mono (commutator_mono
      (DistanceEight.U_le_Z d.radical _) le_rfl) le_rfl).trans_eq hquad)
  have hfixed := sixteen_reciprocal_unequal_critical_fixed s hc hb hcard q hback hquadU
    (by simpa only [hq1,hq2] using hne) W (by simpa only [hq1,hq2] using hgen) hfix
  rw [hq2] at hfixed
  exact large_backward_critical_fixed_radius s hc hb p hlarge q hq2 hback hstrict hfixed

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
