module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.BaumannMovement

/-!
# Reciprocal local spans after full-radius fixedness

At two component vertices a and c at distance two, fixedness of [V_a,Q_a]
makes [Z_c,Q_a] invariant under the full stabilizer of a: the incident edge
kernel normalizes it, and the local residual centralizes it. Taking the
local orbit span therefore preserves this exact seed commutator. Applying
the argument in both directions gives the reciprocal intersection bounds
used before the factorization-module argument in MS93 (5.12)(2).

The final theorem applies the calculation to the literal second vertex of
the original critical path. Full-radius fixedness remains explicit here;
this module does not assert the subsequent factorization witness or the
large-image exclusion.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.12)(2), printed p.926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include h in
private theorem reciprocal_residual_edge_generation {a t : Vertex d.radical}
    (ha : color d.radical a = false) (hat : Adjacent d.radical a t) :
    Ltilde d.radical a ⊔ Q d.radical t = stabilizer d.radical a := by
  have hsup : replacementComponent d ⊔ d.radical = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨k,hk,r,hr,rfl⟩ := replacement_product h d g
    exact mul_mem (mem_sup_left hk) (mem_sup_right hr)
  have hbase : Ltilde d.radical (alpha d.radical) ⊔ Q d.radical (beta d.radical) =
      stabilizer d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d,Q_beta,←Subgroup.map_sup,hsup]
    exact (MonoidHom.range_eq_map (embedM d.radical)).symm.trans (stabilizer_m_base d.radical).symm
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hbase
    rw [Subgroup.map_sup,←Ltilde_act,←Q_act,←stabilizer_act] at he
    simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using he
  · rw [hg.1] at ha
    cases ha

include h in
theorem reciprocal_span_core_eq_seed_of_radius_fixed
    (hb : 2 < replacementDistance h d) {a c : Vertex d.radical}
    (ha : color d.radical a = false) (hc : color d.radical c = false)
    (hd : (cosetGraph d.radical).dist a c = 2)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    ⁅localZSpan d.radical c a,Q d.radical a⁆ = ⁅Z d.radical c,Q d.radical a⁆ ∧
      ⁅localZSpan d.radical c a,Q d.radical a⁆ ≤ Z d.radical c := by
  let D := ⁅Z d.radical c,Q d.radical a⁆
  have hZV : Z d.radical c ≤ V d.radical a := le_iSup_of_le c
    (le_iSup_of_le (show (cosetGraph d.radical).dist c a ≤ 2 by
      rw [SimpleGraph.dist_comm,hd]) le_rfl)
  have hDfixed : D ≤ fixedCore d.radical a := (commutator_mono hZV le_rfl).trans hfixed
  have hQa : Q d.radical a ≤ stabilizer d.radical c :=
    Q_le_stabilizer_of_dist_le_two a c ha hc hd.le
  have hDZ : D ≤ Z d.radical c :=
    le_normalizer_iff_commutator_le_left.mp (hQa.trans (Z_normalized d.radical c))
  obtain ⟨t,hat,hct⟩ := exists_common_neighbor_of_dist_two d.radical a c hd
  have hTa : Q d.radical t ≤ stabilizer d.radical a :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have hTc : Q d.radical t ≤ stabilizer d.radical c :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
  have hTN : Q d.radical t ≤ normalizer (D : Set (FreeAmalgam d.radical)) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅Z d.radical c,Q d.radical a⁆).map (MulAut.conj x).toMonoidHom = _
    have hz : (Z d.radical c).map (MulAut.conj x).toMonoidHom = Z d.radical c :=
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical c (hTc hx))
    have hq : (Q d.radical a).map (MulAut.conj x).toMonoidHom = Q d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a (hTa hx))
    rw [map_commutator,hz,hq]
  have hLN : Ltilde d.radical a ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    (le_centralizer_iff.mp (hDfixed.trans inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hGN : stabilizer d.radical a ≤ normalizer (D : Set (FreeAmalgam d.radical)) := by
    rw [←reciprocal_residual_edge_generation (h := h) ha hat]
    exact sup_le hLN hTN
  have heq : ⁅localZSpan d.radical c a,Q d.radical a⁆ = D := by
    rw [LocalCommutator.span_commutator_eq_conjugates (geometry := replacementGeometry h d)
      ha (by rw [SimpleGraph.dist_comm,hd]) hb]
    apply le_antisymm
    · apply iSup_le
      intro g
      change D.map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom ≤ D
      exact (mem_normalizer_iff_map_conj_eq.mp
        (hGN ((stabilizer d.radical a).inv_mem g.property))).le
    · exact (commutator_mono (Z_le_localZSpan d.radical c a) le_rfl).trans_eq
        (LocalCommutator.span_commutator_eq_conjugates
          (geometry := replacementGeometry h d) ha
          (by rw [SimpleGraph.dist_comm,hd]) hb)
  exact ⟨heq,heq.le.trans hDZ⟩

include h in
theorem reciprocal_span_intersection_commutators_of_radius_fixed
    (hb : 2 < replacementDistance h d) {a c : Vertex d.radical}
    (ha : color d.radical a = false) (hc : color d.radical c = false)
    (hd : (cosetGraph d.radical).dist a c = 2)
    (hfixedA : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hfixedC : ⁅V d.radical c,Q d.radical c⁆ ≤ fixedCore d.radical c) :
    ⁅localZSpan d.radical c a ⊓ Q d.radical c,localZSpan d.radical a c⁆ ≤ Z d.radical a ∧
      ⁅localZSpan d.radical a c ⊓ Q d.radical a,localZSpan d.radical c a⁆ ≤ Z d.radical c := by
  have hA := reciprocal_span_core_eq_seed_of_radius_fixed (h := h) hb ha hc hd hfixedA
  have hC := reciprocal_span_core_eq_seed_of_radius_fixed (h := h) hb hc ha
    (by rwa [SimpleGraph.dist_comm]) hfixedC
  constructor
  · rw [commutator_comm]
    exact (commutator_mono le_rfl inf_le_right).trans hC.2
  · rw [commutator_comm]
    exact (commutator_mono le_rfl inf_le_right).trans hA.2

include h in
theorem selected_reciprocal_span_configuration_of_radius_fixed
    (hb : replacementDistance h d = 4) {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hfixedA : ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical))
    (hfixedC : ⁅V d.radical (p.walk.getVert 2),Q d.radical (p.walk.getVert 2)⁆ ≤
      fixedCore d.radical (p.walk.getVert 2)) :
    let P₁ := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
    let P₂ := localZSpan d.radical (alpha d.radical) (p.walk.getVert 2)
    ⁅P₁,Q d.radical (alpha d.radical)⁆ = ⁅Z d.radical (p.walk.getVert 2),Q d.radical (alpha d.radical)⁆ ∧
      ⁅P₂,Q d.radical (p.walk.getVert 2)⁆ = ⁅Z d.radical (alpha d.radical),Q d.radical (p.walk.getVert 2)⁆ ∧
      ⁅P₁ ⊓ Q d.radical (p.walk.getVert 2),P₂⁆ ≤ Z d.radical (alpha d.radical) ∧
      ⁅P₂ ⊓ Q d.radical (alpha d.radical),P₁⁆ ≤ Z d.radical (p.walk.getVert 2) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hc : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hd : (cosetGraph d.radical).dist (alpha d.radical) (p.walk.getVert 2) = 2 :=
    p.dist_start (by omega)
  exact ⟨(reciprocal_span_core_eq_seed_of_radius_fixed (h := h) hb2 rfl hc hd hfixedA).1,
    (reciprocal_span_core_eq_seed_of_radius_fixed (h := h) hb2 hc rfl
      (by rwa [SimpleGraph.dist_comm]) hfixedC).1,
    reciprocal_span_intersection_commutators_of_radius_fixed (h := h) hb2 rfl hc hd hfixedA hfixedC⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
