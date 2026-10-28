module
public import Theory.GroupAction.ComponentTwoSectionBound
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.CriticalGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.KernelSource

/-!
# Original radius growth and escaping neighboring seeds

At critical distance greater than two, the radius cannot be centralized
modulo its starting seed by the residual: otherwise the common edge ball
is a nontrivial subgroup normal in both vertex stabilizers. For a component
whose simple quotient has order divisible by seventeen, this forces the
radius quotient to have at least 256 elements.

The same edge argument supplies a neighboring seed join which is not normal
in the starting stabilizer. The actual critical endpoint has a conjugate
which fails to normalize this join. With the explicit radius displacement
used in MS93 (5.7), this constructs a backward critical path, retaining every
overlapping vertex. The displacement is not proved here.

Source: MS93 (2.1)(iii),(vii), p.856, and (5.7)--(5.8), pp.919--920.
Original source applications are in GenerationTwoSymplecticRadius.
-/

public noncomputable section
open Subgroup
open Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M}

omit [Finite M] in
private theorem edge_ball_normalized (t : Vertex R) :
    stabilizer R t ≤ normalizer (VBall R t 1 : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  have h := VBall_act R g⁻¹ t 1
  have hgt : act R g⁻¹ t = t := (stabilizer R t).inv_mem hg
  simpa only [hgt, inv_inv, MulEquiv.toMonoidHom_eq_coe] using h.symm

omit [Finite M] in
private theorem edge_ball_le_radius {a t : Vertex R} (hat : Adjacent R a t) :
    VBall R t 1 ≤ V R a := by
  have hatd : (cosetGraph R).dist a t = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)
  apply iSup_le
  intro d
  apply iSup_le
  intro hd
  apply le_iSup_of_le d
  apply le_iSup_of_le (show (cosetGraph R).dist d a ≤ 2 from ?_)
  · exact le_rfl
  · have hh := (cosetGraph_connected R).dist_triangle (u := d) (v := t) (w := a)
    rw [SimpleGraph.dist_comm (u := t),hatd] at hh
    omega

/-- Residual--edge generation suffices; the whole local quotient may have an outer part. -/
theorem radius_moving_not_le_Z_of_residual_edge_generation
    (hms : MSCharacteristicCondition R) (hgen : pResidual 2 M ⊔ R = ⊤)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t)
    (hne : Z R a ≠ ⊥) : ¬ Vcirc R a ≤ Z R a := by
  intro hfixed
  let N := VBall R t 1
  have hatd : (cosetGraph R).dist a t = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)
  have hZN : Z R a ≤ N := le_iSup_of_le a (le_iSup_of_le hatd.le le_rfl)
  have hNV : N ≤ V R a := edge_ball_le_radius hat
  have hNQ := hNV.trans (geometry.V_le_Q hb a ha)
  have hNS : N ≤ stabilizer R a ⊓ stabilizer R t :=
    le_inf (hNQ.trans (fun _ hx => hx.1)) (hNQ.trans (fun _ hx => hx.2 t hat))
  have hNt : stabilizer R t ≤ normalizer (N : Set (FreeAmalgam R)) := edge_ball_normalized t
  have hNa : stabilizer R a ≤ normalizer (N : Set (FreeAmalgam R)) := by
    rw [←local_residual_edge_generation R hgen ha hat]
    refine sup_le ?_ ((show Q R t ≤ stabilizer R t from fun _ hx => hx.1).trans hNt)
    apply le_normalizer_iff_commutator_le_left.mpr
    exact (commutator_mono hNV le_rfl).trans (hfixed.trans hZN)
  have hbot := no_common_normal_at_edge R hms a t ha hat N hNS
    (normal_subgroupOf_of_le_normalizer hNa) (normal_subgroupOf_of_le_normalizer hNt)
  exact hne (le_bot_iff.mp (hZN.trans hbot.le))

/-- The first nontrivial two-section admitting this residual action has order at least 256. -/
theorem radius_index_ge_256_of_residual_edge_generation
    (hms : MSCharacteristicCondition R) (hgen : pResidual 2 M ⊔ R = ⊤)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t)
    (hne : Z R a ≠ ⊥) (hp : IsPGroup 2 (Q R a))
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (q : Ltilde R a →* S) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (hS : 17 ∣ Nat.card S) :
    256 ≤ (Z R a).relIndex (V R a) := by
  by_contra! hi
  have hVQ := geometry.V_le_Q hb a ha
  have hVG := hVQ.trans (show Q R a ≤ stabilizer R a from fun _ hx => hx.1)
  let := finite_stabilizer R a
  let : Finite (V R a) := Finite.of_injective (inclusion hVG) (inclusion_injective _)
  let : Finite (Ltilde R a) := Finite.of_injective
    (inclusion (Ltilde_le_stabilizer a)) (inclusion_injective _)
  let : ((Z R a).subgroupOf (V R a)).Normal :=
    normal_subgroupOf_of_le_normalizer (hVG.trans (Z_normalized R a))
  exact radius_moving_not_le_Z_of_residual_edge_generation hms hgen geometry hb ha hat hne
    (commutator_component_le_of_seventeen_section_lt_256 (Ltilde R a) (V R a) (Z R a)
      (isPPerfect_embedded_pResidual_of_finite 2 _) q hq hk hS (hp.to_le hVQ) hi
      ((Ltilde_le_stabilizer a).trans (DistanceEight.V_normalized R a))
      ((Ltilde_le_stabilizer a).trans (Z_normalized R a)))

/-- A neighbor has a seed join which is not normal in the original local group. -/
theorem exists_neighbor_seed_join_not_normalized
    (hms : MSCharacteristicCondition R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t)
    (hne : Z R a ≠ ⊥) :
    ∃ d, Adjacent R d t ∧
      ¬ stabilizer R a ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) := by
  by_contra! hall
  let N := VBall R t 1
  have hatd : (cosetGraph R).dist a t = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)
  have hZN : Z R a ≤ N := le_iSup_of_le a (le_iSup_of_le hatd.le le_rfl)
  have hNV : N ≤ V R a := edge_ball_le_radius hat
  have hNQ := hNV.trans (geometry.V_le_Q hb a ha)
  have hNS : N ≤ stabilizer R a ⊓ stabilizer R t :=
    le_inf (hNQ.trans (fun _ hx => hx.1)) (hNQ.trans (fun _ hx => hx.2 t hat))
  have hNt : stabilizer R t ≤ normalizer (N : Set (FreeAmalgam R)) := edge_ball_normalized t
  have hNa : stabilizer R a ≤ normalizer (N : Set (FreeAmalgam R)) := by
    apply le_normalizer_iff.mpr
    intro g hg
    have hm : N.map (MulAut.conj g).toMonoidHom ≤ N := by
      change (VBall R t 1).map _ ≤ N
      rw [VBall,Subgroup.map_iSup]
      apply iSup_le
      intro d
      rw [Subgroup.map_iSup]
      apply iSup_le
      intro hd
      by_cases hz : (cosetGraph R).dist d t = 0
      · have hdt := (cosetGraph_connected R).dist_eq_zero_iff.mp hz
        subst d
        have hta := adjacent_Z_le R ha hat
        exact (map_mono hta).trans ((mem_normalizer_iff_map_conj_eq.mp
          (Z_normalized R a hg)).le.trans hZN)
      · have hadj : Adjacent R d t := (cosetGraph_adj R _ _).mp
          (SimpleGraph.dist_eq_one_iff_adj.mp (by omega))
        have hdn : Z R d ≤ N := le_iSup_of_le d (le_iSup_of_le hd le_rfl)
        exact (map_mono (show Z R d ≤ Z R d ⊔ Z R a from le_sup_left)).trans
          ((mem_normalizer_iff_map_conj_eq.mp (hall d hadj hg)).le.trans (sup_le hdn hZN))
    intro x hx
    exact hm (mem_map_of_mem (MulAut.conj g).toMonoidHom hx)
  have hbot := no_common_normal_at_edge R hms a t ha hat N hNS
    (normal_subgroupOf_of_le_normalizer hNa) (normal_subgroupOf_of_le_normalizer hNt)
  exact hne (le_bot_iff.mp (hZN.trans hbot.le))

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four

namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {M J : Type*} [Group M] [Finite M] [Group J] {R : Subgroup M}

/-- The nonnormal neighboring join supplies a literal escaping critical conjugate. -/
theorem exists_critical_neighbor_join_escape
    (hms : MSCharacteristicCondition R) (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hgen : pResidual 2 M ⊔ R = ⊤)
    (q : M →* J) (hq : Function.Surjective q) (hk : q.ker = pCore 2 M)
    [((pResidual 2 M).map q).Normal] [IsSimpleGroup ((pResidual 2 M).map q)]
    [IsQuasisimple ((pResidual 2 M).map q)]
    (hcent : centralizer ((pResidual 2 M).map q : Set J) = ⊥)
    (geometry : Geometry R) (hb : 2 < geometry.b R) (hC : EdgeCentralizerCondition R)
    {a t e : Vertex R} (ha : color R a = false) (hat : Adjacent R a t)
    (hne : Z R a ≠ ⊥) (path : CriticalPath R geometry a e) :
    ∃ d, Adjacent R d t ∧
      ¬ stabilizer R a ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) ∧
      ∃ g ∈ stabilizer R a,
        ¬ Z R e ≤ normalizer ((Z R d ⊔ Z R a).map (MulAut.conj g⁻¹).toMonoidHom) := by
  obtain ⟨d,hdt,hn⟩ := exists_neighbor_seed_join_not_normalized hms geometry hb ha hat hne
  have ht : color R t = true := by
    have hh := adjacent_color_ne R hat
    cases he : color R t <;> simp_all
  have hd : color R d = false := by
    have hh := adjacent_color_ne R hdt
    cases he : color R d <;> simp_all
  have hAQ : Z R a ≤ Q R a :=
    (geometry.omega_bound a ha (lt_of_lt_of_eq (by omega : 0 < geometry.b R) (geometry.distance_constant a ha).symm)).trans (omegaCenter_le _)
  have hDQ : Z R d ≤ Q R d :=
    (geometry.omega_bound d hd (lt_of_lt_of_eq (by omega : 0 < geometry.b R) (geometry.distance_constant d hd).symm)).trans (omegaCenter_le _)
  let N := Z R d ⊔ Z R a
  have hNQ : N ≤ Q R t :=
    sup_le (hDQ.trans (Q_le_adjacent_h R ht hdt)) (hAQ.trans (Q_le_adjacent_h R ht hat))
  have hNG : N ≤ stabilizer R a := hNQ.trans (fun _ hx => hx.2 a (adjacent_symm R hat))
  have hnQ : Q R t ≤ normalizer (N : Set _) :=
    ChapterC.Sp4Four.DistanceReduction.edge_normalizes_neighbor_seed_join hat hdt
  have hnG : ¬ (N.subgroupOf (stabilizer R a)).Normal := fun hh =>
    hn ((normal_subgroupOf_iff_le_normalizer hNG).mp hh)
  have hbe : 0 < criticalDistance R a (geometry.exists_critical a ha) :=
    lt_of_lt_of_eq (by omega : 0 < geometry.b R) (geometry.distance_constant a ha).symm
  have hrev := critical_reverse R geometry hC a ha hbe e path.end_color path.critical
  have heG := critical_Z_le_stabilizer R geometry a ha hbe path.critical
  have hegen := edge_conjugate_generation_of_centric_component R hp hQR hgen q hq hk hcent
    ha hat (Z R e) heG hrev.2
  obtain ⟨g,hg,hg₁,_⟩ := source_2_1_vii R a e t ha hat N N hNQ hNQ
    (normal_subgroupOf_of_le_normalizer hnQ) (normal_subgroupOf_of_le_normalizer hnQ) hnG hnG hegen
  exact ⟨d,hdt,hn,g,hg,hg₁⟩
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four


namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open scoped commutatorElement
variable {M : Type*} [Group M] {R : Subgroup M}

/-- The actual escaping conjugate gives a backward path with every overlap
vertex retained, once the radius displacement of source (5.7) is supplied. -/
theorem backward_path_of_escaped_neighbor_join
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    {a d t e : Vertex R} (p : CriticalPath R geometry a e)
    (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (g : FreeAmalgam R) (hg : g ∈ stabilizer R a)
    (hescape : ¬ Z R e ≤ normalizer
      ((Z R d ⊔ Z R a).map (MulAut.conj g⁻¹).toMonoidHom : Set _))
    (hdisp : ⁅V R a ⊓ Q R (p.walk.getVert (p.walk.length-2)),Z R e⁆ ≤ Z R a) :
    ∃ d' t', Adjacent R a t' ∧ Adjacent R d' t' ∧
      (∃ back : CriticalPath R geometry d' (p.walk.getVert (p.walk.length-2)),
        back.walk.getVert 1 = t' ∧
        ∀ i ≤ p.walk.length-2, back.walk.getVert (i+2) = p.walk.getVert i) ∧
      ¬ V R a ≤ Q R (p.walk.getVert (p.walk.length-2)) := by
  have hga : act R g a = a := hg
  have hatg : Adjacent R a (act R g t) := by
    rw [←hga]
    exact (adjacent_act_iff R g _ _).mpr hat
  have hdtg : Adjacent R (act R g d) (act R g t) :=
    (adjacent_act_iff R g _ _).mpr hdt
  rw [Subgroup.map_sup,←Z_act R g d,←Z_act R g a,hga] at hescape
  have hV : Z R (act R g d) ≤ V R a :=
    le_sup_left.trans (neighbor_seed_join_le_radius hatg hdtg)
  have hnot : ¬ Z R (act R g d) ≤ Q R (p.walk.getVert (p.walk.length-2)) := by
    intro hbad
    apply hescape
    have hzZ := (p.endpoint_Z_le_start_stabilizer (by omega)).trans (Z_normalized R a)
    have hd : ⁅Z R e,Z R (act R g d)⁆ ≤ Z R a := by
      rw [commutator_comm]
      exact (commutator_mono (le_inf hV hbad) le_rfl).trans hdisp
    apply le_normalizer_iff.mpr
    intro z hz y hy
    have hm : (Z R (act R g d) ⊔ Z R a).map (MulAut.conj z).toMonoidHom ≤
        Z R (act R g d) ⊔ Z R a := by
      rw [Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨v,hv,rfl⟩
        have hc := hd (commutator_mem_commutator hz hv)
        change z*v*z⁻¹ ∈ Z R (act R g d) ⊔ Z R a
        rw [show z*v*z⁻¹ = ⁅z,v⁆*v by simp [commutatorElement_def,mul_assoc]]
        exact mul_mem (mem_sup_right hc) (mem_sup_left hv)
      · rw [MulEquiv.toMonoidHom_eq_coe,mem_normalizer_iff_map_conj_eq.mp (hzZ hz)]
        exact le_sup_right
    exact hm (mem_map_of_mem (MulAut.conj z).toMonoidHom hy)
  exact ⟨act R g d,act R g t,hatg,hdtg,
    exists_backward_path_of_not_le geometry (by omega) p hatg hdtg hnot,
    fun h => hnot (hV.trans h)⟩
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
