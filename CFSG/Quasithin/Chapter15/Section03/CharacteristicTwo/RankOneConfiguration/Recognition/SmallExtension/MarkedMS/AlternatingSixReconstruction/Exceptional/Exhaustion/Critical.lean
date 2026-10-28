module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.NormalGeneration
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Graph
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent
public import Theory.Frattini.OmegaProducts

/-!
# Critical-endpoint detection for the exceptional whole core

Transport the radical-intersection centralizer equality to every edge of the
original holomorph graph. Critical reversal and the first-edge argument put
each endpoint's X-layer in the other vertex stabilizer. Their commutator lies
in both X-layers, while the escaping opposite Z-layer is a two-group.

The normal-generation theorem with the retained cubic kernel now shows that
one critical endpoint detects the entire Frattini section of Q. Its
contrapositive is the failed comparison at the start of MS93 (3.6).
At distance two, Q is in the midpoint kernel and centralizes the critical
commutator, so it is the actual actor used in (3.3); its auxiliary commutator
vanishes. A proof of the remaining local bound therefore gives exhaustion.
The rank-two application is in Source. This does not prove that local bound
or the large-distance exhaustion.

Source: Meierfrankenfeld--Stellmacher (1993), (2.2), pp.856--857,
(3.3), pp.866--868, and the first paragraph of (3.6), p.870.
The Frattini-section transport follows the existing binary LocalModules and
natural Geometry.Structure.Noncontainment proofs, with two-subgroup detection
in place of their center-free normal-generation premise.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "T" => edge L R

/-- MS93 (2.2)'s extra centralizer hypothesis on every actual edge.
Only the radical-intersection equality is transported, not full faithfulness. -/
theorem sourceEdgeCentralizer (h : SmallMSPair κ L R) (e : CentralMarking L) :
    EdgeCentralizerCondition T := by
  intro a t ha hat
  obtain ⟨g, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (adjacent_iff_exists_common T a t).mp hat
  · have hm := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom)
      (graph_edge_centralizer h e)
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,
      map_centralizer_equiv] at hm
    change (Q T (beta T)).map (MulAut.conj g⁻¹).toMonoidHom ⊓
      centralizer ((Z T (alpha T)).map (MulAut.conj g⁻¹).toMonoidHom : Set _) =
      (Q T (alpha T)).map (MulAut.conj g⁻¹).toMonoidHom at hm
    simpa only [← Q_act, ← Z_act, alpha, beta, act_mVertex, act_hVertex, one_mul] using hm
  · change true = false at ha
    cases ha

/-- X at a critical endpoint lies in the opposite finite vertex stabilizer. -/
theorem critical_X_le_vertex
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (a : Vertex T) (ha : color T a = false) (c : Vertex T)
    (hc : CriticalPair T a c ((sourceGeometry h).exists_critical a ha)) :
    X T a ≤ stabilizer T c := by
  have hd : (cosetGraph T).dist c a = sourceDistance h := by
    rw [SimpleGraph.dist_comm, hc.1, (sourceGeometry h).distance_constant a ha]
    rfl
  have hp := sourceDistance_pos h
  obtain ⟨t, hct, hta⟩ := exists_adjacent_dist_sub_one T c a (by omega)
  have hXt := X_le_Q_of_dist_lt T (sourceGeometry h) (sourceEdgeCentralizer h e) a ha t
    (by rw [(sourceGeometry h).distance_constant a ha, SimpleGraph.dist_comm]
        change (cosetGraph T).dist t a < sourceDistance h
        omega)
  exact hXt.trans (fun _ hx => hx.2 c (adjacent_symm T hct))

/-- The critical X-commutator lies in both central omega layers. -/
theorem critical_X_commutator_le
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (a : Vertex T) (ha : color T a = false) (c : Vertex T)
    (hc : CriticalPair T a c ((sourceGeometry h).exists_critical a ha)) :
    ⁅X T a, X T c⁆ ≤ X T a ⊓ X T c := by
  have hcColor := critical_endpoint_color T a ha _ hc
  have hp : 0 < criticalDistance T a ((sourceGeometry h).exists_critical a ha) := by
    rw [(sourceGeometry h).distance_constant a ha]
    exact sourceDistance_pos h
  have hr := CFSG.Quasithin.ChapterC.BinaryMS.MS93.critical_reverse T
    (sourceGeometry h) (sourceEdgeCentralizer h e) a ha hp c hcColor hc
  exact le_inf
    (le_normalizer_iff_commutator_le_left.mp
      ((critical_X_le_vertex h e c hcColor a hr).trans (X_normalized T a)))
    (le_normalizer_iff_commutator_le_right.mp
      ((critical_X_le_vertex h e a ha c hc).trans (X_normalized T c)))

omit [Finite G] in
private theorem normal_comap_base (N : Subgroup (FreeAmalgam T))
    (hN : stabilizer T (alpha T) ≤ normalizer (N : Set (FreeAmalgam T))) :
    (N.comap (embedM T)).Normal := by
  constructor
  intro x hx m
  change embedM T (m*x*m⁻¹) ∈ N
  rw [map_mul,map_mul,map_inv]
  apply le_normalizer_iff.mp hN _ _ _ hx
  rw [show alpha T = mVertex T 1 from rfl,stabilizer_m_base]
  exact ⟨m,rfl⟩

/-- A critical endpoint detects the whole Frattini section. Its elementary
image cannot disappear in the retained cubic kernel E/Q. -/
theorem graph_core_le_frattini_of_critical_commutator_le
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (hcomm : ⁅Q T (alpha T), Z T c⁆ ≤
      (frattini (Q T (alpha T))).map (Q T (alpha T)).subtype ⊔ X T (alpha T)) :
    core T (alpha T) ≤
      (frattini (Q T (alpha T))).map (Q T (alpha T)).subtype ⊔ X T (alpha T) := by
  let N := (frattini (Q T (alpha T))).map (Q T (alpha T)).subtype ⊔ X T (alpha T)
  have hn : stabilizer T (alpha T) ≤ normalizer (N : Set (FreeAmalgam T)) := by
    apply (le_inf ?_ (X_normalized T (alpha T))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
    exact (Q_normalized T (alpha T)).trans (normalizer_le_normalizer_characteristic_image
      (Q T (alpha T)) (frattini (Q T (alpha T))))
  let N0 := N.comap (embedM T)
  let : N0.Normal := normal_comap_base N hn
  let A := (Z T c).comap (embedM T)
  have hcColor := critical_endpoint_color T (alpha T) rfl _ hc
  have hr := CFSG.Quasithin.ChapterC.BinaryMS.MS93.critical_reverse T (sourceGeometry h)
    (sourceEdgeCentralizer h e) (alpha T) rfl (sourceDistance_pos h) c hcColor hc
  have hb : 0 < criticalDistance T c ((sourceGeometry h).exists_critical c hcColor) := by
    rw [(sourceGeometry h).distance_constant c hcColor]
    exact sourceDistance_pos h
  have hZX := (sourceGeometry h).omega_bound c hcColor hb
  have hZ : Z T c ≤ (embedM T).range := by
    rw [← show stabilizer T (alpha T) = (embedM T).range from stabilizer_m_base T]
    exact hZX.trans (critical_X_le_vertex h e c hcColor (alpha T) hr)
  have hAm : A.map (embedM T) = Z T c :=
    (map_comap_eq _ _).trans (inf_eq_right.mpr hZ)
  have hA : IsPGroup 2 A := by
    let : IsElementaryAbelian 2 (X T c) := omegaCenter_elementary (Q T c)
    let : IsElementaryAbelian 2 (Z T c) := IsElementaryAbelian.of_le hZX
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.comap_of_injective
      (embedM T) (embedM_injective T) (Z T c)
    exact IsElementaryAbelian.isPGroup 2 A
  have hAQ : ¬ A ≤ pCore 2 M := by
    intro hA'
    apply hr.2
    rw [←hAm, Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact map_mono hA'
  have hQQ : ⁅pCore 2 M,pCore 2 M⁆ ≤ N0 := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, ← Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    apply le_trans _ le_sup_left
    let := finite_stabilizer T (alpha T)
    let : Finite (Q T (alpha T)) := Finite.of_injective
      (inclusion (show Q T (alpha T) ≤ stabilizer T (alpha T) from fun _ hx => hx.1))
      (inclusion_injective _)
    let : Fact (IsPGroup 2 (Q T (alpha T))) :=
      ⟨Q_isPGroup T h.relative_radical.isPGroup h.relative_radical.twoCore_le (alpha T) rfl⟩
    rw [← map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  have hcomm0 : ⁅pCore 2 M,A⁆ ≤ N0 := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, hAm, ← Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact hcomm
  have hm := map_mono (f := embedM T)
    (core_le_of_two_subgroup_commutator_le h e hz N0 A hQQ hA hAQ hcomm0)
  rw [← graph_core h] at hm
  exact hm.trans (map_comap_le _ _)

/-- The non-Frattini branch has the exact failed comparison used in MS93
(3.3). The proof works at every positive critical distance. -/
theorem critical_commutator_not_le
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hlarge : ¬ core T (alpha T) ≤
      (frattini (Q T (alpha T))).map (Q T (alpha T)).subtype ⊔ X T (alpha T))
    (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl)) :
    ¬ ⁅Q T (alpha T),Z T c⁆ ≤
      ⁅Q T (alpha T),X T c ⊓ Q T (alpha T)⁆ ⊔ ⁅X T (alpha T),X T c⁆ := by
  intro hh
  apply hlarge
  apply graph_core_le_frattini_of_critical_commutator_le h e hz c hc
  apply hh.trans
  apply sup_le
  · apply le_trans (commutator_mono le_rfl inf_le_right)
    apply le_trans _ le_sup_left
    let := finite_stabilizer T (alpha T)
    let : Finite (Q T (alpha T)) := Finite.of_injective
      (inclusion (show Q T (alpha T) ≤ stabilizer T (alpha T) from fun _ hx => hx.1))
      (inclusion_injective _)
    let : Fact (IsPGroup 2 (Q T (alpha T))) :=
      ⟨Q_isPGroup T h.relative_radical.isPGroup h.relative_radical.twoCore_le (alpha T) rfl⟩
    rw [← map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  · exact ((critical_X_commutator_le h e (alpha T) rfl c hc).trans inf_le_left).trans
      le_sup_right

/-- At distance two the original Q is a legitimate source-(3.3) actor:
it lies in the middle edge kernel and centralizes the critical commutator.
The final clause kills the auxiliary [A,Y] term for this literal actor. -/
theorem distanceTwo_source_actor
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl)) :
    ∃ t, Adjacent T (alpha T) t ∧ Adjacent T c t ∧
      Q T (alpha T) ≤ Q T t ⊓
        centralizer ((⁅Z T (alpha T),Z T c⁆ : Subgroup (FreeAmalgam T)) : Set (FreeAmalgam T)) ∧
      ⁅X T (alpha T) ⊓ Q T c,Q T (alpha T)⁆ = ⊥ := by
  have hd : (cosetGraph T).dist (alpha T) c = 2 := hc.1.trans hb
  obtain ⟨t, hat, hct⟩ := exists_common_neighbor_of_dist_two T (alpha T) c hd
  have ht : color T t = true := by
    have hh := adjacent_color_ne T hat
    change false ≠ color T t at hh
    cases hcol : color T t <;> simp_all
  have hcColor := critical_endpoint_color T (alpha T) rfl _ hc
  have hZa := (sourceGeometry h).omega_bound (alpha T) rfl (sourceDistance_pos h)
  have hZc := (sourceGeometry h).omega_bound c hcColor (by
    rw [(sourceGeometry h).distance_constant c hcColor]
    exact sourceDistance_pos h)
  have hcomm : ⁅Z T (alpha T),Z T c⁆ ≤ X T (alpha T) :=
    (commutator_mono hZa hZc).trans
      ((critical_X_commutator_le h e (alpha T) rfl c hc).trans inf_le_left)
  refine ⟨t, hat, hct,
    le_inf (Q_le_adjacent_h T ht hat)
      ((Q_le_centralizer_X T (alpha T)).trans (centralizer_le hcomm)), ?_⟩
  exact commutator_eq_bot_iff_le_centralizer.mpr
    (inf_le_left.trans (le_centralizer_iff.mp (Q_le_centralizer_X T (alpha T))))

/-- A bound at one actual critical endpoint suffices for entire-core exhaustion. -/
theorem coreExhaustion_of_critical_commutator_le
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (hcomm : ⁅Q T (alpha T),Z T c⁆ ≤
      (frattini (Q T (alpha T))).map (Q T (alpha T)).subtype ⊔ X T (alpha T)) :
    CoreExhaustion L R :=
  coreExhaustion_of_graph_frattini h
    (graph_core_le_frattini_of_critical_commutator_le h e hz c hc hcomm)

/-- The comparison on the right side of (3.3) already implies exhaustion;
its local module proof remains with this reconstruction owner. -/
theorem coreExhaustion_of_critical_comparison
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (hcomm : ⁅Q T (alpha T),Z T c⁆ ≤
      ⁅Q T (alpha T),X T c ⊓ Q T (alpha T)⁆ ⊔ ⁅X T (alpha T),X T c⁆) :
    CoreExhaustion L R := by
  apply coreExhaustion_of_graph_frattini h
  by_contra hn
  exact critical_commutator_not_le h e hz hn c hc hcomm

/-- The source-(3.3) bound on the actual Q actor removes the entire
exceptional exhaustion premise. Its finite-action proof is the remaining
local obligation, not an assumption of the original source theorem. -/
theorem coreExhaustion_of_source33_bound
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (hcomm : ⁅Z T c,Q T (alpha T)⁆ ≤
      ⁅X T (alpha T),X T c⁆ ⊔ ⁅X T (alpha T) ⊓ Q T c,Q T (alpha T)⁆) :
    CoreExhaustion L R := by
  obtain ⟨_, _, _, _, hzero⟩ := distanceTwo_source_actor h e hb c hc
  rw [hzero, sup_bot_eq, commutator_comm] at hcomm
  exact coreExhaustion_of_critical_comparison h e hz c hc (hcomm.trans le_sup_right)

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
