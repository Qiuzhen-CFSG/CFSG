module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Source

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Normalizer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Moving.Symmetry.SmallAction

/-!
# Normalizer selection outside the fixed preimage

The displacement has order at most four. If its product with Z_c were
normal in G_c, the small-section action theorem would put it in B_c.
Thus a displacement outside B_c gives a subgroup normal in the common
edge kernel and nonnormal in G_c. Source (2.1)(vii) then selects an actual
G_c-conjugate which the critical endpoint does not normalize. The same
conjugate has nontrivial triple commutator.

These are the normalizer and triple-commutator parts of MS93 (4.4.1),
claim (2), p.891. The critical noncontainment remains separate.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
variable {M : Type*} [Group M] {L R : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R}

/-- The small displacement product is normal in the actual common edge kernel. -/
theorem displacement_join_edge_normal [Finite M] {a c t : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t) (hct : Adjacent R c t) :
    ((⁅Z R a, Q R c⁆ ⊔ Z R c).subgroupOf (Q R t)).Normal := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have hta : Q R t ≤ stabilizer R a := by
    rw [Q_h_eq_edge R ht hat]
    exact inf_le_left
  have htc : Q R t ≤ stabilizer R c := by
    rw [Q_h_eq_edge R ht hct]
    exact inf_le_left
  apply normal_subgroupOf_of_le_normalizer
  apply le_trans (le_inf ?_ (htc.trans (Z_normalized R c)))
    (normalizer_inf_normalizer_le_normalizer_sup _ _)
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized R a (hta hg)),
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized R c (htc hg))]

/-- Local normality would force the whole small displacement into B_c,
by the action on its literal quotient modulo Z_c. -/
theorem displacement_le_B_of_join_normal [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hn : ((⁅Z R a, Q R c⁆ ⊔ Z R c).subgroupOf (stabilizer R c)).Normal) :
    ⁅Z R a, Q R c⁆ ≤ B R c (geometry.Z_normal c) := by
  let S := stabilizer R c
  let E := ⁅Z R a, Q R c⁆
  let J := E ⊔ Z R c
  have hEV : E ≤ V R c :=
    ((displacement_le_U common ha hd).trans (U_le_Z R a)).trans
      ((Z_le_localZSpan R a c).trans (localZSpan_le_V R hd.le))
  have hVQ : V R c ≤ Q R c := V_le_Q R hc (by omega)
  have hVG : V R c ≤ S := hVQ.trans (fun _ hx => hx.1)
  have hJG : J ≤ S := sup_le (hEV.trans hVG) (Z_le_stabilizer R c)
  have hJQ : J ≤ Q R c := sup_le (hEV.trans hVQ)
    ((Z_le_VBall R c 2).trans hVQ)
  let : Finite S := finite_stabilizer R c
  let : (J.subgroupOf S).Normal := hn
  let : ((Z R c).subgroupOf S).Normal := geometry.Z_normal c
  obtain ⟨π, hπ, hk⟩ := Escape.Initial.Natural.exists_localProjection source c hc
  have hp : IsPGroup 2 π.ker := by
    rw [hk]
    exact (Q_isPGroup R source.two_group source.core_le c hc).comap_subtype
  have hsmall : ((Z R c).subgroupOf S).relIndex (J.subgroupOf S) ≤ 4 := by
    rw [show J.subgroupOf S = E.subgroupOf S ⊔ (Z R c).subgroupOf S from
      subgroupOf_sup (hEV.trans hVG) (Z_le_stabilizer R c), relIndex_sup_right]
    have hcard : Nat.card (E.subgroupOf S) ≤ 4 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe (hEV.trans hVG)).toEquiv]
      exact displacement_card_le_four common ha hd
    exact (Nat.le_of_dvd Nat.card_pos (relIndex_dvd_card _ _)).trans hcard
  have hcomm := Escape.Propagation.Backward.Moving.Symmetry.small_normal_section_residual
    π hπ hp (J.subgroupOf S) ((Z R c).subgroupOf S)
    (fun _ hx => show _ ∈ J from mem_sup_right hx)
    (by intro x hx; rw [hk]; exact hJQ hx) hsmall
  have hbound : ⁅J, Ltilde R c⁆ ≤ Z R c := by
    have hh := map_mono (f := S.subtype) hcomm
    rwa [map_commutator, map_subgroupOf_eq_of_le hJG,
      map_subgroupOf_eq_of_le (Z_le_stabilizer R c)] at hh
  intro x hx
  apply (mem_B_iff R c _ hVG x).mpr
  refine ⟨hEV hx, ?_⟩
  intro l hl
  rw [commutator_comm] at hbound
  exact hbound (commutator_mem_commutator hl (mem_sup_left hx))

/-- Failure of B_c-containment supplies the nonnormality premise in (2.1)(vii). -/
theorem displacement_join_not_normal [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hout : ¬ ⁅Z R a, Q R c⁆ ≤ B R c (geometry.Z_normal c)) :
    ¬ ((⁅Z R a, Q R c⁆ ⊔ Z R c).subgroupOf (stabilizer R c)).Normal :=
  fun hn => hout (displacement_le_B_of_join_normal common hb ha hc hd hn)

/-- Select the actual orbit conjugate outside the endpoint normalizer.
The endpoint also fails to centralize its displacement. -/
theorem exists_unnormalized_displacement [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c e : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (p : CriticalPath R geometry c e)
    (hout : ¬ ⁅Z R a, Q R c⁆ ≤ B R c (geometry.Z_normal c)) :
    ∃ g ∈ stabilizer R c,
      ¬ Z R e ≤ normalizer (⁅Z R (act R g a), Q R c⁆ ⊔ Z R c : Subgroup (FreeAmalgam R)) ∧
      ⁅⁅Z R (act R g a), Q R c⁆, Z R e⁆ ≠ ⊥ := by
  obtain ⟨t, hat, hct⟩ := exists_common_neighbor_of_dist_two R a c hd
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  let J := ⁅Z R a, Q R c⁆ ⊔ Z R c
  have hJT : J ≤ Q R t := sup_le
    (((displacement_le_U common ha hd).trans (U_le_Z R a)).trans
      ((Z_le_localZSpan R a c).trans ((localZSpan_le_Q R p.start_color hd.le (by omega)).trans
        (Q_le_adjacent_h R ht hct))))
    (((Z_le_VBall R c 2).trans (V_le_Q R p.start_color (by omega))).trans
      (Q_le_adjacent_h R ht hct))
  have hN := displacement_join_edge_normal ha hat hct
  have hnot := displacement_join_not_normal common hb ha p.start_color hd hout
  obtain ⟨g, hg, hbad, _⟩ := source_2_1_vii R c e t p.start_color hct J J
    hJT hJT hN hN hnot hnot (critical_conjugates_sup_edge common p hct)
  have hQ : (Q R c).map (MulAut.conj g⁻¹).toMonoidHom = Q R c :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized R c ((stabilizer R c).inv_mem hg))
  have hZ : (Z R c).map (MulAut.conj g⁻¹).toMonoidHom = Z R c :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized R c ((stabilizer R c).inv_mem hg))
  have hJ : J.map (MulAut.conj g⁻¹).toMonoidHom =
      ⁅Z R (act R g a), Q R c⁆ ⊔ Z R c := by
    change (⁅Z R a, Q R c⁆ ⊔ Z R c).map _ = _
    rw [Subgroup.map_sup, map_commutator, hQ, hZ, ← Z_act]
  rw [hJ] at hbad
  refine ⟨g, hg, hbad, ?_⟩
  intro htriple
  apply hbad
  apply le_trans (le_inf ?_ ((p.endpoint_Z_le_start_stabilizer (by omega)).trans
    (Z_normalized R c))) (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp htriple)).trans
    (Subgroup.centralizer_le_normalizer _)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
