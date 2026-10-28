module

public import Stellmacher.SectionEight.GeneratedEightSixEquationOneCoreTools
public import Stellmacher.SectionEight.GeneratedEightSixFirstCommutator

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem eight_six_squares_of_involution_join
    {G : Type u} [Group G] (family : Set (Subgroup G)) (V D : Subgroup G)
    (hgen : V = sSup family) (hnormal : V ≤ Subgroup.normalizer (D : Set G))
    (hcomm : ⁅V, V⁆ ≤ D)
    (hsquare : ∀ subgroup ∈ family, ∀ element ∈ subgroup, element ^ 2 ∈ D) :
    ∀ element ∈ V, element ^ 2 ∈ D := by
  let _ : (D.subgroupOf V).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnormal
  have hderived : _root_.commutator V ≤ D.subgroupOf V := by
    intro element helement
    apply hcomm
    have hmapped : (_root_.commutator V).map V.subtype = ⁅V, V⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator]
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hmapped ▸ Subgroup.mem_map.mpr ⟨element, helement, rfl⟩
  let _ : IsMulCommutative (V ⧸ D.subgroupOf V) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := D.subgroupOf V)).mpr
      hderived
  let _ : CommGroup (V ⧸ D.subgroupOf V) := IsMulCommutative.instCommGroup
  let square : V →* V ⧸ D.subgroupOf V :=
    (powMonoidHom 2).comp (QuotientGroup.mk' (D.subgroupOf V))
  let kernel : Subgroup G := square.ker.map V.subtype
  have hkernel (element : G) (helement : element ∈ V) :
      element ∈ kernel ↔ element ^ 2 ∈ D := by
    have hzero : square ⟨element, helement⟩ = 1 ↔ element ^ 2 ∈ D := by
      change (QuotientGroup.mk' (D.subgroupOf V) ⟨element, helement⟩) ^ 2 = 1 ↔ _
      rw [← map_pow]
      exact QuotientGroup.eq_one_iff (N := D.subgroupOf V) (⟨element, helement⟩ ^ 2)
    constructor
    · rintro ⟨representative, hrepresentative, heq⟩
      apply hzero.mp
      have heq' : representative = ⟨element, helement⟩ := Subtype.ext heq
      rwa [← heq']
    · intro hsquare
      exact Subgroup.mem_map.mpr ⟨⟨element, helement⟩, hzero.mpr hsquare, rfl⟩
  have hVkernel : V ≤ kernel := by
    rw [hgen]
    apply sSup_le
    intro subgroup hsubgroup element helement
    have hsubV : subgroup ≤ V := hgen ▸ le_sSup hsubgroup
    exact (hkernel element (hsubV helement)).mpr
      (hsquare subgroup hsubgroup element helement)
  exact fun element helement => (hkernel element helement).mp (hVkernel helement)

public theorem eight_six_neighbor_join_le_core
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hlength : 1 < path.length) (vertex : graph.Vertex) :
    VAt graph vertex ≤ QAt graph vertex := by
  rw [VAt, v, graph.vAt_def]
  apply sSup_le
  rintro subgroup ⟨neighbor, hneighbor, rfl⟩
  apply SevenSix.critical_minimality graph path
  have hdistance : graph.distance neighbor vertex = 1 := by
    simpa only [graph.neighbors_def, Set.mem_ofPred_eq] using hneighbor
  omega

public theorem eight_six_first_join_bounds_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (D : Subgroup G) (hnormal : GAt ctx.Γ ctx.criticalPath.a ≤
      Subgroup.normalizer (D : Set G)) (hZa : ZAt ctx.Γ ctx.criticalPath.a ≤ D)
    (hcomm : ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
      QAt ctx.Γ ctx.criticalPath.firstStep⁆ = ZAt ctx.Γ ctx.criticalPath.firstStep) :
    ⁅VAt ctx.Γ ctx.criticalPath.firstStep, VAt ctx.Γ ctx.criticalPath.firstStep⁆ ≤ D ∧
      ∀ element ∈ VAt ctx.Γ ctx.criticalPath.firstStep, element ^ 2 ∈ D := by
  let graph := ctx.Γ
  let path := ctx.criticalPath
  have hlen : path.length = 2 := hlength
  have hVcore := eight_six_neighbor_join_le_core graph path (by omega) path.firstStep
  have hline := eight_six_first_step_fixed_line_local ctx hcenter hcard
  have hderived : ⁅VAt graph path.firstStep, VAt graph path.firstStep⁆ ≤ D :=
    ((Subgroup.commutator_mono le_rfl hVcore).trans_eq hcomm).trans (hline.2.trans hZa)
  refine ⟨hderived, ?_⟩
  have hVinitial : VAt graph path.firstStep ≤ GAt graph path.a :=
    hVcore.trans ((SevenSix.local_cores_le_edge_sylow ctx.sectionSeven graph path).2.trans
      (path.S_le_edge_stabilizers.trans inf_le_left))
  apply eight_six_squares_of_involution_join _ _ D
    (show VAt graph path.firstStep = _ from graph.vAt_def path.firstStep)
    (hVinitial.trans hnormal) hderived
  rintro subgroup ⟨neighbor, hneighbor, rfl⟩ element helement
  have hback : path.firstStep ∈ neighborhood graph neighbor :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr
      (graph.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent graph).mp hneighbor))
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven graph hback
  have hpower := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 (z graph neighbor)) ⟨element, helement⟩
  have hpower' : element ^ 2 = 1 := congrArg Subtype.val hpower
  rw [hpower']
  exact D.one_mem

public theorem eight_six_derived_of_three_factor_bounds
    {G : Type u} [Group G] (A B D Q : Subgroup G)
    (hgen : Q = A ⊔ B ⊔ D) (hnormal : Q ≤ Subgroup.normalizer (D : Set G))
    (hAA : ⁅A, A⁆ ≤ D) (hBB : ⁅B, B⁆ ≤ D) (hAB : ⁅A, B⁆ ≤ D) :
    ⁅Q, Q⁆ ≤ D := by
  have hAQ : A ≤ Q := hgen ▸ le_sup_left.trans le_sup_left
  have hBQ : B ≤ Q := hgen ▸ le_sup_right.trans le_sup_left
  have hDQ : D ≤ Q := hgen ▸ le_sup_right
  have hfamily : Q = sSup {A, B, D} := by
    simpa only [sSup_insert, sSup_singleton, sup_assoc] using hgen
  have hcontain : ∀ subgroup ∈ ({A, B, D} : Set (Subgroup G)), subgroup ≤ Q := by
    intro subgroup hsubgroup
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsubgroup
    rcases hsubgroup with rfl | rfl | rfl
    · exact hAQ
    · exact hBQ
    · exact hDQ
  have hDcomm : ⁅D, Q⁆ ≤ D :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hnormal
  have hcomm : ∀ first ∈ ({A, B, D} : Set (Subgroup G)),
      ∀ second ∈ ({A, B, D} : Set (Subgroup G)), ⁅first, second⁆ ≤ D := by
    intro first hfirst second hsecond
    have hsecondQ := hcontain second hsecond
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfirst hsecond
    rcases hfirst with rfl | rfl | rfl
    · rcases hsecond with rfl | rfl | rfl
      · exact hAA
      · exact hAB
      · rw [Subgroup.commutator_comm]
        exact (Subgroup.commutator_mono le_rfl hAQ).trans hDcomm
    · rcases hsecond with rfl | rfl | rfl
      · rwa [Subgroup.commutator_comm]
      · exact hBB
      · rw [Subgroup.commutator_comm]
        exact (Subgroup.commutator_mono le_rfl hBQ).trans hDcomm
    · exact (Subgroup.commutator_mono le_rfl hsecondQ).trans hDcomm
  rw [hfamily]
  apply eight_six_commutator_sSup_le _ _ _ Q hnormal hcontain
  intro subgroup hsubgroup
  rw [Subgroup.commutator_comm]
  exact eight_six_commutator_sSup_le _ _ _ Q hnormal hcontain
    (fun other hother => hcomm other hother subgroup hsubgroup)

public theorem eight_six_neighbor_join_bounds_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (D : Subgroup G) (hnormal : GAt ctx.Γ ctx.criticalPath.a ≤
      Subgroup.normalizer (D : Set G)) (hZa : ZAt ctx.Γ ctx.criticalPath.a ≤ D)
    (hcomm : ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
      QAt ctx.Γ ctx.criticalPath.firstStep⁆ = ZAt ctx.Γ ctx.criticalPath.firstStep)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a) :
    ⁅VAt ctx.Γ previous, VAt ctx.Γ previous⁆ ≤ D ∧
      ∀ element ∈ VAt ctx.Γ previous, element ^ 2 ∈ D := by
  have hfirst := eight_six_first_join_bounds_local ctx hcenter hlength hcard
    D hnormal hZa hcomm
  have hneighbor : ctx.criticalPath.firstStep ∈ neighborhood ctx.Γ ctx.criticalPath.a :=
    (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj
  obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
    ctx.criticalPath.a hneighbor hprevious
  let conjugation := (MulAut.conj (actor : G)⁻¹).toMonoidHom
  have hmap : VAt ctx.Γ previous =
      (VAt ctx.Γ ctx.criticalPath.firstStep).map conjugation := by
    rw [← hactor]
    exact v_act ctx.Γ actor ctx.criticalPath.firstStep
  have hDmap : D.map conjugation ≤ D := by
    rintro element ⟨original, horiginal, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (hnormal ((GAt ctx.Γ ctx.criticalPath.a).inv_mem actor.property)) original).mp horiginal
  constructor
  · rw [hmap, ← Subgroup.map_commutator]
    exact (Subgroup.map_mono hfirst.1).trans hDmap
  · rw [hmap]
    rintro element ⟨original, horiginal, rfl⟩
    rw [← map_pow]
    exact hDmap (Subgroup.mem_map.mpr ⟨original ^ 2, hfirst.2 original horiginal, rfl⟩)

public theorem eight_six_core_derived_and_squares_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (D L Q : Subgroup G)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (action : EightSixEquationOneActionData ctx.Γ ctx.criticalPath D L Q)
    (hgen : Q = (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔ D) :
    ⁅Q, Q⁆ ≤ D ∧
      (∀ element ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a, element ^ 2 ∈ D) ∧
      (∀ element ∈ VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a,
        element ^ 2 ∈ D) := by
  let graph := ctx.Γ
  let path := ctx.criticalPath
  have hcontain := eight_six_action_core_containments ctx.sectionSeven graph path
    previous hprevious D L Q hD hL hQ action
  have hnormal : GAt graph path.a ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer action.intersection_normal.1).mp
      action.intersection_normal.2
  have hfirst := eight_six_first_join_bounds_local ctx hcenter hlength hcard D hnormal
    hcontain.2.2 action.first_commutator
  have hpreviousBounds := eight_six_neighbor_join_bounds_local ctx hcenter hlength hcard
    D hnormal hcontain.2.2 action.first_commutator previous hprevious
  refine ⟨?_, fun element helement => hpreviousBounds.2 element helement.1,
    fun element helement => hfirst.2 element helement.1⟩
  have hQaGa : QAt graph path.a ≤ GAt graph path.a := by
    rw [QAt, q, graph.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  apply eight_six_derived_of_three_factor_bounds _ _ D Q hgen
    (hcontain.2.1.trans (hQaGa.trans hnormal))
    ((Subgroup.commutator_mono inf_le_left inf_le_left).trans hpreviousBounds.1)
    ((Subgroup.commutator_mono inf_le_left inf_le_left).trans hfirst.1)
  have hlen : path.length = 2 := hlength
  have hVprevious := eight_six_neighbor_join_le_core graph path (by omega) previous
  have hVfirst := eight_six_neighbor_join_le_core graph path (by omega) path.firstStep
  have hQaPrevious : QAt graph path.a ≤ GAt graph previous :=
    ((lemma_seven_three ctx.sectionSeven graph).sylow_and_core path.a previous hprevious
      (default : Sylow 2 (↥(GAt graph path.a ⊓ GAt graph previous)))).2.2
  have hQaFirst : QAt graph path.a ≤ GAt graph path.firstStep :=
    (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven graph path).1.trans
      (path.S_le_edge_stabilizers.trans inf_le_right)
  rw [hD]
  apply le_inf
  · exact (Subgroup.commutator_mono (inf_le_left.trans hVprevious) inf_le_right).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        (hQaPrevious.trans (SevenSix.stabilizer_le_normalizer_q graph previous)))
  · exact (Subgroup.commutator_mono inf_le_right (inf_le_left.trans hVfirst)).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp
        (hQaFirst.trans (SevenSix.stabilizer_le_normalizer_q graph path.firstStep)))

end Stellmacher.SectionEight
